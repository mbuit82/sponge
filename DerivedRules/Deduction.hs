module DerivedRules.Deduction where

import Core
import Parse.Sentences

import Defs.Operators
import Defs.Rules

import DerivedRules.Utils

import qualified Data.Map as Map
import Data.Maybe

hypCaseDerivedRule :: ProofTree -> ProofTree
hypCaseDerivedRule (ProofTree h _ _) =
    ProofTree (applySubst "H -> H" [("H", h)]) "Modus Ponens" 
        [ProofTree (applySubst "H -> (H -> H)" [("H", h)]) "Simp" [],
        ProofTree (applySubst "(H -> (H -> H)) -> (H -> H))" [("H", h)]) "Modus Ponens" 
            [ProofTree (applySubst "H -> ((H -> H) -> H)" [("H", h)]) "Simp" [],
            ProofTree (applySubst "((H -> ((H -> H) -> H)) -> ((H -> (H -> H)) -> (H -> H)))" [("H", h)]) "Frege" []]]
    where 
        applySubst = parseWithSubst [cond] []

-- axiomCaseDerivedRule :: Sentence -> ProofTree -> ProofTree
-- axiomCaseDerivedRule hyp pft@(ProofTree pfc pfj _) =
--     ProofTree (applySubst "H -> C" [("H", hyp), ("C", pfc)]) "Modus Ponens" 
--         [pft,
--         ProofTree (applySubst "C -> (H -> C)" [("H", hyp), ("C", pfc)]) "Simp" []]
--     where 
--         applySubst = parseWithSubst [cond] []



unify :: [Sentence] -> [Sentence] -> Maybe Substitution
unify schemas currs = foldl' sumIfCoherent' (Just []) (zipWith getSubst schemas currs)

hypSyll :: ([Sentence], Sentence)
hypSyll = ([parse [cond] [] "H -> P", parse [cond] [] "P -> Q"], (parse [cond] [] "H -> Q"))

middleP :: ([Sentence], Sentence)
middleP = ([parse [cond] [] "P", parse [cond] [] "H -> (P -> Q)"], (parse [cond] [] "H -> Q"))

recMP :: ([Sentence], Sentence)
recMP = ([parse [cond] [] "H -> P", parse [cond] [] "H -> (P -> Q)"], (parse [cond] [] "H -> Q"))
    

modusPonensCaseDerivedRule :: ProofTree -> ProofTree
modusPonensCaseDerivedRule (ProofTree pfc pfj spfs) = 
    ProofTree (p "H -> Q") "Modus Ponens"
        [hpPf,
        ProofTree (p "(H -> P) -> (H -> Q)") "Modus Ponens" 
                [hpqPf,
                ProofTree (p "(H -> (P -> Q)) -> ((H -> P) -> (H -> Q))") "Frege" []]]
    where
        subst = fromJust (unify (fst recMP) (map pfContent spfs))
        p = \str -> parseWithSubst [cond] [] str subst
        [hpPf, hpqPf] = spfs

hypSyllCaseDerivedRule :: ProofTree -> ProofTree
hypSyllCaseDerivedRule (ProofTree pfc pfj spfs) = 
    ProofTree (p "H -> Q") "Modus Ponens"
        [hpPf,
        ProofTree (p "(H -> P) -> (H -> Q)") "Modus Ponens" 
            [ProofTree (p "H -> (P -> Q)") "Modus Ponens" 
                [pqPf,
                ProofTree (p "(P -> Q) -> (H -> (P -> Q))") "Simp" []],
            ProofTree (p "(H -> (P -> Q)) -> ((H -> P) -> (H -> Q))") "Frege" []]]
    where
        subst = fromJust (unify (fst hypSyll) (map pfContent spfs))
        p = \str -> parseWithSubst [cond] [] str subst
        [hpPf, pqPf] = spfs

middlePCaseDerivedRule :: ProofTree -> ProofTree
middlePCaseDerivedRule (ProofTree pfc pfj spfs) = 
    ProofTree (p "H -> Q") "Modus Ponens"
        [ProofTree (p "H -> P") "Modus Ponens"
            [pPf,
            ProofTree (p "P -> (H -> P)") "Simp" []],
        ProofTree (p "(H -> P) -> (H -> Q)") "Modus Ponens" 
            [hpqPf,
            ProofTree (p "(H -> (P -> Q)) -> ((H -> P) -> (H -> Q))") "Frege" []]]
    where
        subst = fromJust (unify (fst middleP) (map pfContent spfs))
        p = \str -> parseWithSubst [cond] [] str subst
        [pPf, hpqPf] = spfs




-- deduction should be the last transformation that happens
useDeduction' :: Sentence -> ProofTree -> ProofTree
useDeduction' hyp pfTree@(ProofTree pfc pfj spfs) =
    case pfj of
        "Modus Ponens" -> 
            let currPrems = map pfContent spfs in
            case unify (premises modusPonens) currPrems of
                Just s -> pfTree
                Nothing -> case unify (fst hypSyll) currPrems of
                    Just s -> hypSyllCaseDerivedRule pfTree
                    Nothing -> case unify (fst middleP) currPrems of
                        Just s -> middlePCaseDerivedRule pfTree
                        Nothing -> case unify (fst recMP) currPrems of
                            Just s -> modusPonensCaseDerivedRule pfTree
                            Nothing -> error "something wrong in new deduction fock"
        "Assumption" -> if pfContent pfTree == hyp
                            then hypCaseDerivedRule pfTree
                            else pfTree
        _ -> pfTree

useDeduction :: Sentence -> ProofTree -> ProofTree
useDeduction hyp = applyOverTree (useDeduction' hyp)

makeDeductionsFunc :: [Sentence] -> ProofTree -> ProofTree
makeDeductionsFunc deductionAntecedents =
    foldl' (.) id (map useDeduction deductionAntecedents) -- used to be foldl... still works tho

eliminateDeduction' :: ProofTree -> ProofTree
eliminateDeduction' (ProofTree pfc "deduction" [spf]) =
    let [dArg] = getNEmbeddedAntecedents cond 1 pfc in
    useDeduction dArg spf
eliminateDeduction' (ProofTree pfc "deduction" spfs) =
    error ("deduction should have one arg but has two: " ++ show spfs)
eliminateDeduction' pft = pft

eliminateDeduction :: ProofTree -> ProofTree
eliminateDeduction = applyOverTree eliminateDeduction'



normalize' :: ProofTree -> ProofTree
normalize' (ProofTree q "Modus Ponens" [pPf, ProofTree pq "deduction" [spf]]) =
    composeDerivations (mkSentSubsts [pPf]) spf
    -- spf should be a proof of q. so we are good
normalize' pft = pft

normalize :: ProofTree -> ProofTree
normalize = applyOverTree normalize'