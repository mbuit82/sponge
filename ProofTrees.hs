module ProofTrees where

import Core
import Parse.Sentences

import Defs.Operators

import Data.Maybe
import Data.List
import qualified Data.Map as Map

data ProofTree = ProofTree {
    pfContent :: Sentence,
    pfJustification :: String,
    subProofs :: [ProofTree]
} deriving Show

findLineWithLNum :: [Line] -> Int -> Line
findLineWithLNum [] _ = error "no line with that number"
findLineWithLNum (ln:lns) lNum
    | lineNumber ln == lNum = ln
    | otherwise = findLineWithLNum lns lNum

linesToProofTree' :: [Line] -> Line -> ProofTree
linesToProofTree' [] _ = error "empty proof"
linesToProofTree' lns currLine = 
    ProofTree 
        (lineContent currLine) 
        (justification currLine) 
        (map ((linesToProofTree' lns) . (findLineWithLNum lns)) (refLines currLine))

linesToProofTree :: [Line] -> ProofTree
linesToProofTree lns = 
    case (reverse lns) of
        [] -> error "empty proof"
        (lastLn:remLns) ->
            linesToProofTree' (lastLn:remLns) lastLn

applyOverProofTree :: (ProofTree -> ProofTree) -> ProofTree -> ProofTree
applyOverProofTree func (ProofTree pfc pfj spfs) =
    func (ProofTree pfc pfj (map (applyOverProofTree func) spfs))



hypCaseDerivedRule :: ProofTree -> ProofTree
hypCaseDerivedRule = undefined

axiomCaseDerivedRule :: Sentence -> ProofTree -> ProofTree
axiomCaseDerivedRule = undefined

modusPonensCaseDerivedRule :: Sentence -> ProofTree -> ProofTree
modusPonensCaseDerivedRule = undefined

-- deduction should be the last transformation that happens
useDeduction' :: Sentence -> ProofTree -> ProofTree
useDeduction' hyp pfTree =
    case pfJustification pfTree of
        "Modus Ponens" -> modusPonensCaseDerivedRule hyp pfTree
        "Assumption" -> if pfContent pfTree == hyp
                            then axiomCaseDerivedRule hyp pfTree
                            else modusPonensCaseDerivedRule hyp pfTree
        j -> modusPonensCaseDerivedRule hyp pfTree

useDeduction :: Sentence -> ProofTree -> ProofTree
useDeduction hyp = applyOverProofTree (useDeduction' hyp)












andElimLDerivedRule :: ProofTree -> ProofTree
andElimLDerivedRule (ProofTree p pfj spfs) =
    ProofTree p "Modus Ponens"
        [ProofTree (applySubst "PandQ -> P" [("PandQ", pandq), ("P", p)]) "And-EL" [],
        pandqPf]
    where 
        applySubst = parseWithSubst [cond] []
        [pandqPf] = spfs
        pandq = pfContent pandqPf

andElimRDerivedRule :: ProofTree -> ProofTree
andElimRDerivedRule (ProofTree q pfj spfs) =
    ProofTree q "Modus Ponens"
        [ProofTree (applySubst "PandQ -> Q" [("PandQ", pandq), ("Q", q)]) "And-ER" [],
        pandqPf]
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

applyDerivedRules' :: Map.Map String (ProofTree -> ProofTree) -> ProofTree -> ProofTree
applyDerivedRules' derRulesDict pfTree =
    case derRulesDict Map.!? pfJustification pfTree of 
        Nothing -> pfTree
        Just func -> func pfTree

applyDerivedRules :: Map.Map String (ProofTree -> ProofTree) -> ProofTree -> ProofTree
applyDerivedRules derRulesDict =
    applyOverProofTree (applyDerivedRules' derRulesDict)








-- -- machinery for applying derived rules
-- applyDerivedRules' :: Map.Map String Transformation -> Transformant -> Transformant
-- applyDerivedRules' derRulesDict state =
--     case (curr state) of
--         Nothing -> state -- we've reached the end! 
--         Just line -> case derRulesDict Map.!? (justification line) of
--             Nothing -> applyDerivedRules' derRulesDict (applyTransformation identityTransformation state)
--             Just transformation -> applyDerivedRules' derRulesDict (applyTransformation transformation state)
    
-- applyDerivedRules :: Map.Map String Transformation -> [Line] -> [Line]
-- applyDerivedRules derRulesDict = 
--     resetUserNumbers . reverse . transformata . (applyDerivedRules' derRulesDict) . intoTransformant

-- proofTreeToLines :: ProofTree -> Int -> [Line]
-- proofTreeToLines pfTree currNum =
--     case pfJustification pfTree of
--         [] -> Line currNum 



-- data Line = Line {
--     lineNumber :: Int,
--     lineContent :: Sentence,
--     justification :: String,
--     refLines :: [Int],
--     userNumber :: Maybe Int -- the original line number the user used (NOTE: actually this is not that lol it's like an old pointer type thing lol)
-- } deriving Eq

data DefinedOperator = DefinedOperator {
    defOpName :: String,
    defOpSymbol :: String, 
    defOpArity :: Int,
    definition :: [Sentence] -> Sentence
} 



