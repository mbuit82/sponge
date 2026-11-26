module DerivedRules.Deduction where

import Core
import Parse.Sentences

import Defs.Operators

import DerivedRules.Utils

import qualified Data.Map as Map


hypCaseDerivedRule :: ProofTree -> ProofTree
hypCaseDerivedRule (ProofTree h _ _) =
    ProofTree (applySubst "H -> H" [("H", h)]) "Modus Ponens" 
        [ProofTree (applySubst "H -> (H -> H)" [("H", h)]) "Simp" [],
        ProofTree (applySubst "(H -> (H -> H)) -> (H -> H))" [("H", h)]) "Modus Ponens" 
            [ProofTree (applySubst "H -> ((H -> H) -> H)" [("H", h)]) "Simp" [],
            ProofTree (applySubst "((H -> ((H -> H) -> H)) -> ((H -> (H -> H)) -> (H -> H)))" [("H", h)]) "Frege" []]]
    where 
        applySubst = parseWithSubst [cond] []

axiomCaseDerivedRule :: Sentence -> ProofTree -> ProofTree
axiomCaseDerivedRule hyp (ProofTree pfc pfj spfs) =
    ProofTree (applySubst "H -> C" [("H", hyp), ("C", pfc)]) "Modus Ponens" 
        [ProofTree pfc pfj [],
        ProofTree (applySubst "C -> (H -> C)" [("H", hyp), ("C", pfc)]) "Simp" []]
    where 
        applySubst = parseWithSubst [cond] []


modusPonensCaseDerivedRule :: Sentence -> ProofTree -> ProofTree
modusPonensCaseDerivedRule hyp (ProofTree pfc pfj spfs)= 
    ProofTree (applySubst "H -> Q" [("H", hyp), ("Q", pfc)]) "Modus Ponens"
        [hpPf,
        ProofTree (applySubst "HP -> (H -> Q)" [("HP", hp), ("H", hyp), ("Q", pfc)]) "Modus Ponens" 
                [hpqPf,
                ProofTree (applySubst "HPQ -> (HP -> (H -> Q))" [("HP", hp), ("HPQ", hpq), ("H", hyp), ("Q", pfc)]) "Frege" []]]
    where
        applySubst = parseWithSubst [cond] []
        [hpPf, hpqPf] = spfs
        [hp, hpq] = map pfContent spfs


-- deduction should be the last transformation that happens
-- useDeduction' :: Sentence -> ProofTree -> ProofTree
-- useDeduction' hyp pfTree =
--     case pfJustification pfTree of
--         "Modus Ponens" -> modusPonensCaseDerivedRule hyp pfTree
--         "Assumption" -> if pfContent pfTree == hyp
--                             then hypCaseDerivedRule pfTree
--                             else axiomCaseDerivedRule hyp pfTree
--         j -> axiomCaseDerivedRule hyp pfTree


eliminateDeduction' :: ProofTree -> ProofTree
eliminateDeduction' (ProofTree pfc "deduction" [spf]) =
    let [dArg] = getNEmbeddedAntecedents cond 1 pfc in
    useDeduction dArg spf
eliminateDeduction' (ProofTree pfc "deduction" spfs) =
    error ("deduction should have one arg but has two: " ++ show spfs)
eliminateDeduction' pft = pft

eliminateDeduction :: ProofTree -> ProofTree
eliminateDeduction = applyOverTree eliminateDeduction'

-- right now have problem (see remarkable). 
-- I think we can fix it by making deduction top-down. 
-- if subterms are not closed, then we need to do full deduction. 
-- if subterms are closed, we don't need to do full deduction: we only need to do weakening (axiomCase) on top level.
-- (This is the observation that allows for using axiomCaseDerivedRule in useDeduction' above)

closedUnderSent :: Sentence -> ProofTree -> Bool
closedUnderSent hyp (ProofTree pfc pfj spfs) =
    not (pfc == hyp && pfj == "Assumption") || or (map (closedUnderSent hyp) spfs)
-- closedUnderSent hyp (ProofTree _ _ spfs) =
--     or (map (closedUnderSent hyp) spfs)

useDeduction'' :: Sentence -> ProofTree -> ProofTree
useDeduction'' hyp pfTree =
    case pfJustification pfTree of
        "Modus Ponens" -> modusPonensCaseDerivedRule hyp pfTree
        "Assumption" -> if pfContent pfTree == hyp
                            then hypCaseDerivedRule pfTree
                            else axiomCaseDerivedRule hyp pfTree
        j -> axiomCaseDerivedRule hyp pfTree

useDeduction' :: Sentence -> ProofTree -> ProofTree
useDeduction' hyp pft@(ProofTree pfc pfj spfs) 
    | closedUnderSent hyp pft = pft
    | otherwise =
        let recCalls = map (useDeduction'' hyp) spfs in
        useDeduction'' hyp (ProofTree pfc pfj recCalls)

useDeduction :: Sentence -> ProofTree -> ProofTree
useDeduction hyp = applyOverTree (useDeduction' hyp)


-- makeDeductionsFunc :: [Sentence] -> ProofTree -> ProofTree
-- makeDeductionsFunc deductionAntecedents =
--     foldl' (.) id (map useDeduction deductionAntecedents) -- used to be foldl... still works tho



normalize' :: ProofTree -> ProofTree
normalize' (ProofTree q "Modus Ponens" [pPf, ProofTree pq "deduction" [spf]]) =
    composeDerivations (mkSentSubsts [pPf]) spf
    -- spf should be a proof of q. so we are good
normalize' pft = pft

normalize :: ProofTree -> ProofTree
normalize = applyOverTree normalize'