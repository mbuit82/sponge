module DerivedRules.UseDerivedRules where

import Core
import Parse.Proofs

import Defs.Operators
import Defs.Specs

import DerivedRules.Utils
import DerivedRules.ImplicationalFragment
import DerivedRules.KReasoning
import DerivedRules.Deduction

import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map

-- DERIVED RULES
-- The way derived rules work is that they're applied on everything. If you use one for a logic that doesn't have the required operators or axioms, then the Datalog proof just won't go through (and eventually we'll get an error pointing to the right user line). Nothing too terrible. And they _really_, really don't belong in the logics. 
derivedRules :: Map.Map String (ProofTree -> ProofTree)
derivedRules = Map.fromList [ 
    -- contrapositionDerivedRule,
    ("strengthening", strengtheningDerivedRule), -- from |- x -> y infer |- (P -> ... -> x) -> (P -> ... -> y) (any depth you'd like!)
    ("weakening", weakeningDerivedRule),
    ("embedding", embeddingDerivedRule),
    ("K reasoning", kReasoningDerivedRule) -- distribute boxes, push boxes through; hope to add diamonds
    ]

useDerivedRules' :: Map.Map String (ProofTree -> ProofTree) -> ProofTree -> ProofTree
useDerivedRules' derRulesDict pfTree =
    case derRulesDict Map.!? pfJustification pfTree of 
        Nothing -> pfTree
        Just derRule -> derRule pfTree

useDerivedRules :: ProofTree -> ProofTree
useDerivedRules = applyOverTree (useDerivedRules' derivedRules)

getHaskellProofWithoutDeduction :: String -> String -> IO (Sentence, [Sentence], ProofTree)
getHaskellProofWithoutDeduction logicName proofName = do
    (goal, deductionArgs, userLines) <- parseUserProofFile logicName proofName
    let userProof = linesToProofTree userLines
    let afterDerivedRules = useDerivedRules userProof -- this way, derived rules can use cited thms
    let afterCitingAxioms = useCitedAxioms (getLogic logicName) afterDerivedRules
    afterCitingTheorems <- useCitedTheorems afterCitingAxioms
    pure (goal, deductionArgs, afterCitingTheorems) -- this is what we return for the FINAL pass, which is deduction (below)

getHaskellProof :: String -> String -> IO (Sentence, ProofTree)
getHaskellProof logicName proofName = do
    (goal, deductionArgs, pf) <- getHaskellProofWithoutDeduction logicName proofName
    pure (goal, (makeDeductionsFunc deductionArgs) pf)

-- not quite what you want bc don't u avoid repetitions here
seeHaskellProof :: String -> String -> IO ()
seeHaskellProof logicName proofName = do
    (_, pf) <- getHaskellProof logicName proofName
    let lns = proofTreeToLines pf
    let relevantContents = map (\l -> (lineNumber l, lineContent l, justification l, refLines l)) lns
    mapM_ print relevantContents



applySubstToSent :: Map.Map String Sentence -> Sentence -> Sentence
applySubstToSent varMap (Atom a) = instantiateVar varMap a
applySubstToSent varMap (OpNode op args) = (OpNode op (map (applySubstToSent varMap) args))

-- writing bc might be useful later idk
changeRootContent :: (Sentence -> Sentence) -> ProofTree -> ProofTree
changeRootContent sentFunc (ProofTree pfc pfj spfs) = 
    ProofTree (sentFunc pfc) pfj spfs

applySubstToProof :: Map.Map String Sentence -> ProofTree -> ProofTree
applySubstToProof varMap =
    applyOverTree (changeRootContent (applySubstToSent varMap))

reconstructCitedTheorem :: ProofTree -> Sentence
reconstructCitedTheorem (ProofTree pfc pfj spfs) = 
    makeChain cond (map pfContent spfs) pfc

removeCitingText :: String -> String
removeCitingText jus =
    if isInfixOf "applying" jus ||
        isInfixOf "citing" jus ||
        isInfixOf "using" jus
    then dropWhile (/= ' ') (dropWhile isSpace jus)
    else jus

getTheoremInfo :: String -> (String, String)
getTheoremInfo jus =
    let jus' = removeCitingText jus in
    -- error (takeWhile (/= ' ') (dropWhile isSpace jus))
    let ((proofName'), rest) = break (=='(') (dropWhile isSpace jus') in
    let (logicName, rest') = break (==')') (dropWhile isSpace (fromJust (stripPrefix "(from" rest))) in
    (logicName, dropWhileEnd isSpace proofName')

getUsedDerivedArgs :: [Sentence] -> [ProofTree] -> ([(Sentence, ProofTree)], [Sentence], [ProofTree])
getUsedDerivedArgs deductionArgs [] = ([], deductionArgs, [])
getUsedDerivedArgs [] spfs = ([], [], spfs)
getUsedDerivedArgs (dArg:remArgs) (newRef:remRefs) =
    let (remPairs, unusedDeductions, unusedApps) = getUsedDerivedArgs remArgs remRefs in
        ((dArg, newRef) : remPairs, unusedDeductions, unusedApps)

derivationComposition :: Map.Map Sentence ProofTree -> ProofTree -> ProofTree
derivationComposition pairsDict (ProofTree pfc pfj spfs) =
    if pfj == "Assumption" 
        then fromJust (pairsDict Map.!? pfc)
        else ProofTree pfc pfj (map (derivationComposition pairsDict) spfs)

-- wondering about name
optimizedApply :: Sentence -> [Sentence] -> ProofTree -> ProofTree -> ProofTree
optimizedApply citedGoal deductionArgs citedPf pfTree =
    let varMap = getVarMap (reconstructCitedTheorem pfTree) citedGoal in
    let citedPfSubstd = applySubstToProof varMap citedPf in
    let deductionArgsSubstd = map (applySubstToSent varMap) deductionArgs in
    let (usedDerivedArgs, remHyps, remArgs) = getUsedDerivedArgs deductionArgsSubstd (subProofs pfTree) in
    applyPfs (derivationComposition (Map.fromList usedDerivedArgs) ((makeDeductionsFunc remHyps) citedPfSubstd)) remArgs

useCitedTheorem :: ProofTree -> IO ProofTree
useCitedTheorem pfTree = do
    let (thmLogicName, thmName) = getTheoremInfo (pfJustification pfTree)
    (thmGoal, deductionArgs, citedPf) <- getHaskellProofWithoutDeduction thmLogicName thmName
    pure (optimizedApply thmGoal deductionArgs citedPf pfTree)

useCitedTheorems' :: ProofTree -> IO ProofTree
useCitedTheorems' pfTree =
    if "(from " `isInfixOf` (pfJustification pfTree)
        then do useCitedTheorem pfTree
        else do pure pfTree

useCitedTheorems :: ProofTree -> IO ProofTree
useCitedTheorems = applyOverTreeM useCitedTheorems'

useCitedAxiom :: Logic -> ProofTree -> ProofTree
useCitedAxiom logic pfTree = 
    let axiom = (axiomsDict logic Map.! (pfJustification pfTree)) in
    let axc = axiomContent axiom in
    optimizedApply axc [] (ProofTree axc (axiomName axiom) []) pfTree

useCitedAxioms' :: Logic -> ProofTree -> ProofTree
useCitedAxioms' logic pfTree =
    if (pfJustification pfTree) `elem` (map axiomName (axioms logic)) && (subProofs pfTree /= [])
        then useCitedAxiom logic pfTree
        else pfTree

useCitedAxioms :: Logic -> ProofTree -> ProofTree
useCitedAxioms logic = applyOverTree (useCitedAxioms' logic)



-- don't really have a palce for these right now, they're toys
getUserSentencesInOrder :: [Line] -> [Sentence]
getUserSentencesInOrder userLines =
    map lineContent userLines

findLNumForContent :: [Line] -> Sentence -> Int
findLNumForContent [] sent = error ("no line w sentence " ++ (show sent))
findLNumForContent (ln:lns) sent =
    if lineContent ln == sent then lineNumber ln else findLNumForContent lns sent

asdf :: String -> String -> IO [Int]
asdf logicName proofName = do
    (goal, deductionArgs, userLines) <- parseUserProofFile logicName proofName
    let userSents = getUserSentencesInOrder userLines
    (goal, haskellPf) <- getHaskellProof logicName proofName
    let haskellLines' = proofTreeToLines haskellPf
    -- let haskellLines = pruneProofTree haskellLines'
    pure (map (findLNumForContent haskellLines') userSents)