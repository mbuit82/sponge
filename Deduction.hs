module Deduction where

import Core
import Parse.Sentences

import Defs.Operators

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
useDeduction' :: Sentence -> ProofTree -> ProofTree
useDeduction' hyp pfTree =
    case pfJustification pfTree of
        "Modus Ponens" -> modusPonensCaseDerivedRule hyp pfTree
        "Assumption" -> if pfContent pfTree == hyp
                            then hypCaseDerivedRule pfTree
                            else axiomCaseDerivedRule hyp pfTree
        j -> axiomCaseDerivedRule hyp pfTree

useDeduction :: Sentence -> ProofTree -> ProofTree
useDeduction hyp = applyOverTree (useDeduction' hyp)

makeDeductionsFunc :: [Sentence] -> ProofTree -> ProofTree
makeDeductionsFunc deductionAntecedents =
    foldl (.) id (map useDeduction deductionAntecedents)