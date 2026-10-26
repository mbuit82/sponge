module ProofTrees where

import Core
import Parse.Sentences
import Parse.Proofs

import Deduction
import Defs.Operators
-- import Defs.Rules
import Defs.Specs

import PruneProofTrees

import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map


-- placeholder
derivedRules :: Map.Map String (ProofTree -> ProofTree)
derivedRules = Map.empty

applyDerivedRules' :: Map.Map String (ProofTree -> ProofTree) -> ProofTree -> ProofTree
applyDerivedRules' derRulesDict pfTree =
    case derRulesDict Map.!? pfJustification pfTree of 
        Nothing -> pfTree
        Just func -> func pfTree

applyDerivedRules :: Map.Map String (ProofTree -> ProofTree) -> ProofTree -> ProofTree
applyDerivedRules derRulesDict = applyOverTree (applyDerivedRules' derRulesDict)



-- pandqPf should go first? 
andElimLDerivedRule :: ProofTree -> ProofTree
andElimLDerivedRule (ProofTree p pfj spfs) =
    ProofTree p "Modus Ponens"
        [pandqPf,
        ProofTree (applySubst "PandQ -> P" [("PandQ", pandq), ("P", p)]) "And-EL" []]
    where 
        applySubst = parseWithSubst [cond] []
        [pandqPf] = spfs
        pandq = pfContent pandqPf

andElimRDerivedRule :: ProofTree -> ProofTree
andElimRDerivedRule (ProofTree q pfj spfs) =
    ProofTree q "Modus Ponens"
        [pandqPf,
        ProofTree (applySubst "PandQ -> Q" [("PandQ", pandq), ("Q", q)]) "And-ER" []]
    where 
        applySubst = parseWithSubst [cond] []
        [pandqPf] = spfs
        pandq = pfContent pandqPf

adjunctionDerivedRule :: ProofTree -> ProofTree
adjunctionDerivedRule (ProofTree pandq pfj spfs) =
    ProofTree pandq "Modus Ponens"
        [
            qPf,
            ProofTree (applySubst "Q -> (P & Q)" [("P", p), ("Q", q)]) "Modus Ponens"
            [
                pPf,
                ProofTree (applySubst "P -> (Q -> (P & Q))" [("P", p), ("Q", q)]) "And-I" []
            ]
        ]
    where
        applySubst = parseWithSubst [cond, andOp] []
        [pPf, qPf] = spfs
        [p, q] = map pfContent spfs

-- makeJustificationPoop :: ProofTree -> ProofTree
-- makeJustificationPoop (ProofTree pfc pfj spfs) =
--     ProofTree pfc "POOP" spfs






applySubstToSent :: Map.Map String Sentence -> Sentence -> Sentence
applySubstToSent varMap (Atom a) = instantiateVar varMap a
applySubstToSent varMap (OpNode op args) = (OpNode op (map (applySubstToSent varMap) args))

-- replaces applyOffsetAndSubstsToInsertedTheorem
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


-- copied exactly. No need to change
stripBrackets :: String -> String
stripBrackets ('[':rest)
    | not (null rest) && last rest == ']' = init rest
stripBrackets subsStr = error ("somthing wrong w the user-inputted substitution: " ++ subsStr)

-- the string here is the justification
getTheoremInfo :: String -> (String, String)
getTheoremInfo jus =
    let jus' = dropWhile (/= ' ') (dropWhile isSpace jus) in
        let ((proofName'), rest) = break (=='(') (dropWhile isSpace jus') in
            let (logicName, rest') = break (==')') (dropWhile isSpace (fromJust (stripPrefix "(from" rest))) in
                    (logicName, dropWhileEnd isSpace proofName')

-- [Sentence] are the deductionArgs, [ProofTree] are the subproofs supplied in the line
getSentPfPairs :: [Sentence] -> [ProofTree] -> ([(Sentence, ProofTree)], Either [Sentence] [ProofTree])
getSentPfPairs deductionArgs [] = ([], Left deductionArgs)
getSentPfPairs [] spfs = ([], Right spfs)
getSentPfPairs (dArg:remArgs) (newRef:remRefs) =
    let (remPairs, leftovers) = getSentPfPairs remArgs remRefs in
        ((dArg, newRef) : remPairs, leftovers)

makeModusPonensLines :: [ProofTree] -> ProofTree -> ProofTree
makeModusPonensLines [] pfTree = pfTree
makeModusPonensLines (spf:rem) pfTree = 
    makeModusPonensLines 
        rem 
        (ProofTree 
            consq
            "Modus Ponens"
            [spf, pfTree])
    where 
        [_, consq] = args (pfContent pfTree)

addAppStuff :: Map.Map Sentence ProofTree -> (Either [Sentence] [ProofTree]) -> ProofTree -> ProofTree
addAppStuff pairsDict leftovers pfTree = -- you want to turn the pfTree into something that you will later feed it a line to
    case leftovers of
        Left deductionArgs -> instantiateAssumptions pairsDict ((makeDeductionsFunc deductionArgs) pfTree)
        Right spfs -> makeModusPonensLines spfs pfTree

instantiateAssumptions :: Map.Map Sentence ProofTree -> ProofTree -> ProofTree
instantiateAssumptions pairsDict (ProofTree pfc pfj spfs) =
    -- error (show (Map.toList pairsDict))
    if pfj == "Assumption" 
        then fromJust (pairsDict Map.!? pfc)
        else ProofTree pfc pfj (map (instantiateAssumptions pairsDict) spfs)

    -- case pairsDict Map.!? pfc of
    --     Nothing -> ProofTree pfc pfj (map (instantiateAssumptions pairsDict) spfs)
    --     Just pf -> if pfj == "Assumption" 
    --                 then pf
    --                 else ProofTree pfc pfj (map (instantiateAssumptions pairsDict) spfs)

insertTheoremDerivedRule :: String -> String -> ProofTree -> IO ProofTree
insertTheoremDerivedRule thmLogicName thmName pfTree = do
    (thmGoal, deductionArgs, citedPf) <- getHaskellProofWithoutDeduction thmLogicName thmName -- unfold everything but deduction in the cited proof
    let varMap = getVarMapFromState pfTree thmGoal -- make the varMap from the current and cited lines and cited thm goal

    let citedPfSubstd = applySubstToProof varMap citedPf 
    let deductionArgsSubstd = map (applySubstToSent varMap) deductionArgs -- need this


    let (pairs, leftovers) = getSentPfPairs deductionArgsSubstd (subProofs pfTree)
    -- error ((show deductionArgsSubstd) ++ "\n" ++ (show ((subProofs pfTree))) ++ thmName)
    -- error (show (pairs, leftovers))
    let postApp = addAppStuff (Map.fromList pairs) leftovers citedPfSubstd -- need this
    pure postApp

citedTheoremDerivedRule :: ProofTree -> IO ProofTree
citedTheoremDerivedRule pfTree = do
    let (thmLogicName, thmName) = getTheoremInfo (pfJustification pfTree)
    insertTheoremDerivedRule thmLogicName thmName pfTree




-- useCitedTheorems' :: ProofTree -> IO (ProofTree)
-- useCitedTheorems' state = do
--     case curr state of
--         Nothing -> pure state
--         Just line -> 
--             if "applying" `isInfixOf` (justification line) || 
--                 "using" `isInfixOf` (justification line) || 
--                 "citing" `isInfixOf` (justification line)
--                 then do 
--                     step <- applyIOTransformation citedTheoremIOTransformation state -- CHANGED TO USE APPLYING
--                     useCitedTheorems' step
--                 else 
--                     useCitedTheorems' (applyTransformation identityTransformation state)

-- useCitedTheorems :: [Line] -> IO [Line]
-- useCitedTheorems ProofTree -> IO (ProofTree)
--     (resetUserNumbers . reverse. transformata) <$> (useCitedTheorems' (intoTransformant oldProof))



useCitedTheorems' :: ProofTree -> IO ProofTree
useCitedTheorems' pfTree =
    if "applying" `isInfixOf` (pfJustification pfTree) || 
        "using" `isInfixOf` (pfJustification pfTree) || 
        "citing" `isInfixOf` (pfJustification pfTree)
        then do 
            citedTheoremDerivedRule pfTree
        else 
            do pure pfTree

useCitedTheorems :: ProofTree -> IO ProofTree
useCitedTheorems = applyOverTreeM useCitedTheorems'
    

-- moving up top in case add more stuff at bottom
getHaskellProofWithoutDeduction :: String -> String -> IO (Sentence, [Sentence], ProofTree)
getHaskellProofWithoutDeduction logicName proofName = do
    (goal, deductionArgs, userLines) <- parseUserProofFile logicName proofName
    let userProof = linesToProofTree userLines
    let afterDerivedRules = applyDerivedRules derivedRules userProof -- this way, derived rules can use cited thms
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