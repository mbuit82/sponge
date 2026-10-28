module DerivedRules.Classical where

import Core
import Parse.Sentences

import Defs.Operators

import DerivedRules.Utils

import qualified Data.Map as Map



contrapositionDerivedRule :: ProofTree -> ProofTree
contrapositionDerivedRule = undefined



-- strengthen
strengtheningDerivedRule' :: [Sentence] -> ProofTree -> ProofTree
strengtheningDerivedRule' [] (ProofTree pfc pfj [spf]) = spf
strengtheningDerivedRule' [] _ = error "trick for strengthening doesn't work"
strengtheningDerivedRule' (p:rest) (ProofTree pfc pfj spfs) =
    ProofTree (applySubst "(P -> X) -> (P -> Y)" [("P", p), ("X", x), ("Y", y)]) "Modus Ponens"
        [ProofTree (applySubst "P -> (X -> Y)" [("P", p), ("X", x), ("Y", y)]) "Modus Ponens"
            [xyPf,
            ProofTree (applySubst "(X -> Y) -> ((P -> (X -> Y)))" [("P", p), ("X", x), ("Y", y)]) "Simp" []],
        ProofTree (applySubst "(P -> (X -> Y)) -> ((P -> X) -> (P -> Y))" [("P", p), ("X", x), ("Y", y)]) "Frege" []]
    where 
        applySubst = parseWithSubst [cond] []
        xyPf = strengtheningDerivedRule' rest (ProofTree pfc pfj spfs)
        [x, y] = args (pfContent xyPf)

strengtheningDerivedRule :: ProofTree -> ProofTree
strengtheningDerivedRule pfTree = 
    makeModusPonensLines
        mpSubPfs
        (strengtheningDerivedRule' 
            (getEmbeddedAntecedentsUpTo cond x arg1) 
            (ProofTree (strengthenCond) (pfJustification pfTree) [xyPf]))
    where 
        xyPf:mpSubPfs = subProofs pfTree
        strengthenCond = makeChain cond (map pfContent mpSubPfs) (pfContent pfTree)
        [arg1, _] = args strengthenCond
        [x, _] = args (pfContent xyPf)



-- weaken
weakeningDerivedRule :: ProofTree -> ProofTree
weakeningDerivedRule pfTree =
    makeModusPonensLines 
        mpSubPfs
        (strengtheningDerivedRule 
            (ProofTree strengthenCond "strengthening" 
                [ProofTree 
                    (applySubst "(Y -> Q) -> (X -> Q)" [("Y", y), ("X", x), ("Q", forHypSyll)]) 
                    "applying hypothetical_syllogism (from minimal)"
                    [xyPf]]))
    where
        xyPf:mpSubPfs = subProofs pfTree
        strengthenCond = makeChain cond (map pfContent mpSubPfs) (pfContent pfTree)
        applySubst = parseWithSubst [cond] []
        [x, y] = args (pfContent xyPf)
        [weakenedCond1, _] = args strengthenCond
        forHypSyll = getEmbeddedConsequentAfter cond y weakenedCond1



-- embed
embeddingDerivedRule' :: Int -> ProofTree -> ProofTree
embeddingDerivedRule' 0 pfTree = error "don't expect this case to be triggered"
embeddingDerivedRule' 1 pfTree = strengtheningDerivedRule pfTree
embeddingDerivedRule' n pfTree = 
    strengtheningDerivedRule
        (ProofTree (pfContent pfTree) "" 
            [ProofTree (applySubst "(X -> (Y -> Z)) -> ((X -> Y) -> (X -> Z))" [("X", x), ("Y", y), ("Z", z)]) "Frege" [],
            embeddingDerivedRule' (n-1) pfTree])
    where
        recCall = embeddingDerivedRule' (n-1) pfTree
        applySubst = parseWithSubst [cond] []
        fregeAntecedent = getNthConsequent cond (n-1) (pfContent recCall)
        [x, yz] = args fregeAntecedent
        [y, z] = args yz

embeddingDerivedRule :: ProofTree -> ProofTree
embeddingDerivedRule pfTree =
    embeddingDerivedRule' (getChainLength cond (pfContent spf)) pfTree
    where
        [spf] = subProofs pfTree

-- Case 0: nothing

-- Case 1: |- P -> Q => |- (X -> P) -> (X -> Q)
-- This is just strengthening? ye

-- Case 2: |- P -> Q -> R => |- (X -> P) -> (X -> Q) -> (X -> R)
-- i. (X -> P) -> (X -> (Q -> R)) from recursive call
-- i+1. (X -> (Q -> R)) -> ((X -> Q) -> (X -> R)) by Frege
-- i+2. strengthening: i+1 i

-- Case 3: |- P -> Q -> R -> S |- (X -> P) -> (X -> Q) -> (X -> R) -> (X -> S)
-- (X -> P) -> (X -> Q) -> (X -> (R -> S)) from recursive call
-- Frege based on guy at end, then strengthen on the Frege, and then MP