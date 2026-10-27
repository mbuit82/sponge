module ProofTrees where

import Core
import Parse.Sentences
import Parse.Proofs

import Deduction
import Defs.Operators
import Defs.Rules
-- import Defs.Rules
import Defs.Specs

import PruneProofTrees

import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map

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
    let haskellLines = pruneProofTree haskellLines'
    pure (map (findLNumForContent haskellLines) userSents)



getHaskellProofWithoutDeduction :: String -> String -> IO (Sentence, [Sentence], ProofTree)
getHaskellProofWithoutDeduction logicName proofName = do
    (goal, deductionArgs, userLines) <- parseUserProofFile logicName proofName
    let userProof = linesToProofTree userLines
    afterCitingAxioms <- useCitedAxioms (getLogic logicName) userProof
    let afterDerivedRules = applyDerivedRules afterCitingAxioms -- this way, derived rules can use cited thms
    afterCitingTheorems <- useCitedTheorems afterDerivedRules
    pure (goal, deductionArgs, afterCitingTheorems) -- this is what we return for the FINAL pass, which is deduction (below)

getHaskellProof :: String -> String -> IO (Sentence, ProofTree)
getHaskellProof logicName proofName = do
    (goal, deductionArgs, pf) <- getHaskellProofWithoutDeduction logicName proofName
    pure (goal, (makeDeductionsFunc deductionArgs) pf)

-- not quite what you want bc don't avoid repetitions
seeHaskellProof :: String -> String -> IO ()
seeHaskellProof logicName proofName = do
    (_, pf) <- getHaskellProof logicName proofName
    let lns = proofTreeToLines pf
    let relevantContents = map (\l -> (lineNumber l, lineContent l, justification l, refLines l)) lns
    mapM_ print relevantContents


-- placeholder
-- really all of this could go to rules tbh. None of the machinery is specific to here. 





applySubstToSent :: Map.Map String Sentence -> Sentence -> Sentence
applySubstToSent varMap (Atom a) = instantiateVar varMap a
applySubstToSent varMap (OpNode op args) = (OpNode op (map (applySubstToSent varMap) args))

applySubstToProof :: Map.Map String Sentence -> ProofTree -> ProofTree
applySubstToProof varMap pfTree = 
    ProofTree 
        (applySubstToSent varMap (pfContent pfTree)) 
        (pfJustification pfTree) 
        (map (applySubstToProof varMap) (subProofs pfTree))

makeCitedTheoremInstance :: ProofTree -> Sentence
makeCitedTheoremInstance (ProofTree pfc pfj spfs) = 
    makeChain cond (map pfContent spfs) pfc

getVarMapFromState :: ProofTree -> Sentence -> Map.Map String Sentence
getVarMapFromState pfTree schema =
    getVarMap (makeCitedTheoremInstance pfTree) schema

stripBrackets :: String -> String
stripBrackets ('[':rest)
    | not (null rest) && last rest == ']' = init rest
stripBrackets subsStr = error ("somthing wrong w the user-inputted substitution: " ++ subsStr)

getTheoremInfo :: String -> (String, String)
getTheoremInfo jus =
    let jus' = dropWhile (/= ' ') (dropWhile isSpace jus) in
        let ((proofName'), rest) = break (=='(') (dropWhile isSpace jus') in
            let (logicName, rest') = break (==')') (dropWhile isSpace (fromJust (stripPrefix "(from" rest))) in
                    (logicName, dropWhileEnd isSpace proofName')

-- [Sentence] are the deductionArgs, [ProofTree] are the subproofs supplied in the line
getInfoForCut :: [Sentence] -> [ProofTree] -> ([(Sentence, ProofTree)], Either [Sentence] [ProofTree])
getInfoForCut deductionArgs [] = ([], Left deductionArgs)
getInfoForCut [] spfs = ([], Right spfs)
getInfoForCut (dArg:remArgs) (newRef:remRefs) =
    let (remPairs, leftovers) = getInfoForCut remArgs remRefs in
        ((dArg, newRef) : remPairs, leftovers)

makeModusPonensLines :: [ProofTree] -> ProofTree -> ProofTree
makeModusPonensLines [] pfTree = pfTree
makeModusPonensLines (spf:rem) pfTree = 
    makeModusPonensLines rem (ProofTree consq "Modus Ponens" [spf, pfTree])
    where 
        [_, consq] = args (pfContent pfTree)

instantiateAssumedPfs :: Map.Map Sentence ProofTree -> ProofTree -> ProofTree
instantiateAssumedPfs pairsDict (ProofTree pfc pfj spfs) =
    if pfj == "Assumption" 
        then fromJust (pairsDict Map.!? pfc)
        else ProofTree pfc pfj (map (instantiateAssumedPfs pairsDict) spfs)

simulateCut :: Map.Map Sentence ProofTree -> (Either [Sentence] [ProofTree]) -> ProofTree -> ProofTree
simulateCut pairsDict leftovers pfTree = -- you want to turn the pfTree into something that you will later feed it a line to
    case leftovers of
        Left deductionArgs -> instantiateAssumedPfs pairsDict ((makeDeductionsFunc deductionArgs) pfTree)
        Right spfs -> makeModusPonensLines spfs pfTree

insertDerivedRule :: Sentence -> [Sentence] -> ProofTree -> ProofTree -> IO ProofTree
insertDerivedRule citedGoal deductionArgs citedPf pfTree = do
    -- make the varMap from the current and cited lines and cited thm goal
    let varMap = getVarMapFromState pfTree citedGoal 

    -- apply substitutions to the theorem and proof schemata that you got
    let citedPfSubstd = applySubstToProof varMap citedPf 
    let deductionArgsSubstd = map (applySubstToSent varMap) deductionArgs

    -- simulate cut
    let (pairs, leftovers) = getInfoForCut deductionArgsSubstd (subProofs pfTree)
    let postApp = simulateCut (Map.fromList pairs) leftovers citedPfSubstd
    pure postApp

insertTheoremDerivedRule :: String -> String -> ProofTree -> IO ProofTree
insertTheoremDerivedRule thmLogicName thmName pfTree = do
    -- unfold everything but deduction in the cited proof
    (thmGoal, deductionArgs, citedPf) <- getHaskellProofWithoutDeduction thmLogicName thmName
    insertDerivedRule thmGoal deductionArgs citedPf pfTree
    -- -- make the varMap from the current and cited lines and cited thm goal
    -- let varMap = getVarMapFromState pfTree thmGoal 

    -- -- apply substitutions to the theorem and proof schemata that you got
    -- let citedPfSubstd = applySubstToProof varMap citedPf 
    -- let deductionArgsSubstd = map (applySubstToSent varMap) deductionArgs

    -- -- simulate cut
    -- let (pairs, leftovers) = getInfoForCut deductionArgsSubstd (subProofs pfTree)
    -- let postApp = simulateCut (Map.fromList pairs) leftovers citedPfSubstd
    -- pure postApp

citedTheoremDerivedRule :: ProofTree -> IO ProofTree
citedTheoremDerivedRule pfTree = do
    let (thmLogicName, thmName) = getTheoremInfo (pfJustification pfTree)
    insertTheoremDerivedRule thmLogicName thmName pfTree

useCitedTheorems' :: ProofTree -> IO ProofTree
useCitedTheorems' pfTree =
    if "(from " `isInfixOf` (pfJustification pfTree)
    -- if "applying" `isInfixOf` (pfJustification pfTree) || 
    --     "using" `isInfixOf` (pfJustification pfTree) || 
    --     "citing" `isInfixOf` (pfJustification pfTree)
        then do citedTheoremDerivedRule pfTree
        else do pure pfTree

useCitedTheorems :: ProofTree -> IO ProofTree
useCitedTheorems = applyOverTreeM useCitedTheorems'

insertAxiomDerivedRule :: Axiom -> ProofTree -> IO ProofTree
insertAxiomDerivedRule axiom pfTree = do
    let axc = axiomContent axiom
    insertDerivedRule axc [] (ProofTree axc (axiomName axiom) []) pfTree

citedAxiomDerivedRule :: ProofTree -> IO ProofTree
citedAxiomDerivedRule pfTree = do
    let (thmLogicName, thmName) = getTheoremInfo (pfJustification pfTree)
    insertTheoremDerivedRule thmLogicName thmName pfTree

useCitedAxioms' :: Logic -> ProofTree -> IO ProofTree
useCitedAxioms' logic pfTree =
    if (pfJustification pfTree) `elem` (map axiomName (axioms logic)) && (subProofs pfTree /= [])
        then do citedTheoremDerivedRule pfTree
        else do pure pfTree

useCitedAxioms :: Logic -> ProofTree -> IO ProofTree
useCitedAxioms logic = applyOverTreeM (useCitedAxioms' logic)