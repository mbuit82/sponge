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
    ProofTree (p "H -> H") "Modus Ponens" 
        [ProofTree (p "H -> (H -> H)") "Simp" [],
        ProofTree (p "(H -> (H -> H)) -> (H -> H))") "Modus Ponens" 
            [ProofTree (p "H -> ((H -> H) -> H)") "Simp" [],
            ProofTree (p "((H -> ((H -> H) -> H)) -> ((H -> (H -> H)) -> (H -> H)))") "Frege" []]]
    where 
        p = \str -> parseWithSubst [cond] [] str [("H", h)]

axiomCaseDerivedRule :: Sentence -> ProofTree -> ProofTree
axiomCaseDerivedRule hyp pft@(ProofTree pfc pfj _) =
    ProofTree (p "H -> C") "Modus Ponens" 
        [pft,
        ProofTree (p "C -> (H -> C)") "Simp" []]
    where 
        p = \str -> parseWithSubst [cond] [] str [("H", hyp), ("C", pfc)]



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

-- OLD deduction
oldUseDeduction' :: Sentence -> ProofTree -> ProofTree
oldUseDeduction' hyp pfTree@(ProofTree pfc pfj spfs) =
    case pfj of
        "Modus Ponens" -> modusPonensCaseDerivedRule pfTree
        "Assumption" -> if pfContent pfTree == hyp
                            then hypCaseDerivedRule pfTree
                            else axiomCaseDerivedRule hyp pfTree
        _ -> axiomCaseDerivedRule hyp pfTree

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
                            Nothing -> error (
                                "something wrong in new deduction fock" ++ "\n" ++
                                show hyp ++ "\n" ++ 
                                show pfc ++ "\n" ++ 
                                show pfj ++ "\n" ++ 
                                show (map pfContent spfs))
        "Assumption" -> if pfContent pfTree == hyp
                            then hypCaseDerivedRule pfTree
                            else pfTree
        _ -> pfTree

useDeduction :: Sentence -> ProofTree -> ProofTree
useDeduction hyp = applyOverTree (useDeduction' hyp)

eliminateDeduction' :: ProofTree -> ProofTree
eliminateDeduction' (ProofTree pfc "Deduction Lemma" [spf]) =
    let [dArg] = getNEmbeddedAntecedents cond 1 pfc in
    let deducted = (useDeduction dArg spf) in
    if deducted == spf -- happens if you never use the assumption
        -- only happens in compiler, contrapositive
        then axiomCaseDerivedRule dArg deducted
        else deducted
eliminateDeduction' (ProofTree pfc "Deduction Lemma" spfs) =
    error ("deduction should have one arg but has two: " ++ show spfs)
eliminateDeduction' pft = pft

eliminateDeduction :: ProofTree -> ProofTree
eliminateDeduction = applyOverTree eliminateDeduction'

normalize' :: ProofTree -> ProofTree
normalize' (ProofTree q "Modus Ponens" [pPf, ProofTree pq "Deduction Lemma" [spf]]) =
    composeDerivations (mkSentSubsts [pPf]) spf -- spf should be a proof of q. so we are good
normalize' pft = pft

-- inefficient
-- potentially endlessly looping
-- but I'm like 99% sure strong normalization holds for the system I'm working in
-- since it's basically a stripped down version of ND
-- so endless looping does not happen
normalize :: ProofTree -> ProofTree
normalize pft =
    let normed = applyOverTree normalize' pft in
    if pft == normed
        then pft
        else applyOverTree normalize' normed