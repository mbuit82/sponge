module DerivedRules.KReasoning where

import Core
import Parse.Sentences

import Defs.Operators

import DerivedRules.Utils
import DerivedRules.Classical

import qualified Data.Map as Map


-- K derived rules
countConds :: Int -> Sentence -> Int
countConds n (OpNode op args)
    | op == cond = countConds (n+1) (args !! 1) 
    | op == box = n
    | otherwise = error "somethings up"

-- we apply this on the current state of the transformant
getNForBoxes :: Sentence -> Int
getNForBoxes = countConds (-1)

-- This is for a UNBOXED SENTENCE. 
makeKAxiom :: Sentence -> Sentence
makeKAxiom (OpNode opCond [arg1, arg2])
    | opCond == cond =
        parseWithSubst [cond, box] [] "L(A1 -> A2) -> (LA1 -> LA2)" [("A1", arg1), ("A2", arg2)]
    | otherwise = error "cited line for distributing boxes is not of form L(A1 -> A2) but ALMOST AAGGHHH"
makeKAxiom _ = error "cited line for distributing boxes is not of form L(A1 -> A2)"

pushingBoxDerivedRule' :: Int -> ProofTree -> ProofTree
pushingBoxDerivedRule' 0 pfTree =
    ProofTree kConsq "Modus Ponens" 
        [boxOutPf,
        ProofTree kInstance "K Axiom" []]
    where 
        [boxOutPf] = subProofs pfTree
        boxOut = pfContent boxOutPf
        [unboxed] = args boxOut
        kInstance = makeKAxiom unboxed
        [_, kConsq] = args kInstance
pushingBoxDerivedRule' k pfTree =
    ProofTree (embed kConsq) "Modus Ponens"
        [pushingBoxDerivedRule' (k - 1) pfTree,
        strengtheningDerivedRule (ProofTree strengthenedContent "strengthening" [ProofTree kInstance "K Axiom" []])]
    where
        [boxOutPf] = subProofs pfTree
        boxOut = pfContent boxOutPf
        [unboxed] = args boxOut
        kInstance = makeKAxiom (getNthConsequent cond k unboxed)
        [kAnt, kConsq] = args kInstance
        embed = makeChain cond (getNEmbeddedAntecedents cond k (pfContent pfTree))
        strengthenedContent = OpNode cond [embed kAnt, embed kConsq]

pushingBoxDerivedRule :: ProofTree -> ProofTree
pushingBoxDerivedRule pfTree = 
    pushingBoxDerivedRule' (getNForBoxes (pfContent pfTree)) pfTree

distributingBoxDerivedRule :: ProofTree -> ProofTree
distributingBoxDerivedRule pfTree =
    pushingBoxDerivedRule 
        (ProofTree (pfContent pfTree) "K reasoning" 
            [ProofTree (applySubst "LC" [("C", unboxed)]) "Necessitation" 
                [unboxedProof]])
    where
        applySubst = parseWithSubst [cond, box] []
        [unboxedProof] = subProofs pfTree
        unboxed = pfContent unboxedProof

distributingDiamondsDerivedRule :: ProofTree -> ProofTree
distributingDiamondsDerivedRule pfTree =
    ProofTree (applySubst "MP -> MQ" [("P", p), ("Q", q)]) "Contrapositive"
        [ProofTree (applySubst "L~Q -> L~P" [("P", p), ("Q", q)]) "Modus Ponens" 
            [ProofTree (applySubst "L(~Q -> ~P)" [("P", p), ("Q", q)]) "Necessitation" 
                [ProofTree (applySubst "~Q -> ~P" [("P", p), ("Q", q)]) "Contrapositive" 
                    [spf]],
            ProofTree (applySubst "L(~Q -> ~P) -> (L~Q -> L~P)" [("P", p), ("Q", q)]) "K Axiom" []]]
    where
        [spf] = subProofs pfTree
        applySubst = parseWithSubst [cond, box, negOp] [diamond]
        [p, q] = args (pfContent spf)

kReasoningDerivedRule :: ProofTree -> ProofTree
kReasoningDerivedRule pfTree
    | isInstance (pfContent pfTree) (parse [cond] [diamond] "MP -> MQ") =
        distributingDiamondsDerivedRule pfTree
    | topOp (pfContent spf) == box = 
        pushingBoxDerivedRule pfTree
    | otherwise = 
        distributingBoxDerivedRule pfTree
    where 
        [spf] = subProofs pfTree