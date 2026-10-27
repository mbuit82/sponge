module Defs.Rules where

import Core
import Parse.Sentences

import Defs.Operators

import Data.Maybe
import qualified Data.Map as Map



-- INFERENCE RULES
modusPonens :: InferenceRule
modusPonens = InferenceRule "Modus Ponens" (parse [] [] "P", Just (parse [cond] [] "P -> Q")) (parse [] [] "Q")

necessitation :: InferenceRule
necessitation = InferenceRule "Necessitation" (parse [] [] "P", Nothing) (parse [box] [] "L P")



-- DERIVED RULES
-- The way derived rules work is that they're applied on everything. If you use one for a logic that doesn't have the required operators or axioms, then the Datalog proof just won't go through (and eventually we'll get an error pointing to the right user line). Nothing too terrible. And they _really_, really don't belong in the logics. 
derivedRules :: Map.Map String (ProofTree -> ProofTree)
derivedRules = Map.fromList [ 
    -- ("And Elim L", andElimLDerivedRule), -- from |- A & B infer |- A
    -- ("And Elim R", andElimRDerivedRule),  -- from |- A & B infer |- B
    -- ("Adjunction", adjunctionDerivedRule), -- from |- A and |- B infer |- A & B
    -- ("Or Elim", orElimDerivedRule), -- from |- A -> C and |- B -> C infer |- (A v B) -> C
    -- forget about the ones below for now
    -- contrapositionDerivedRule,
    ("Strengthening", strengtheningDerivedRule), -- from |- x -> y infer |- (P -> ... -> x) -> (P -> ... -> y) (any depth you'd like!)
    -- distributingDiamondsDerivedRule, 
    ("K reasoning", kReasoningDerivedRule) -- distribute boxes, push boxes through; hope to add diamonds
    ]

applyDerivedRules' :: Map.Map String (ProofTree -> ProofTree) -> ProofTree -> ProofTree
applyDerivedRules' derRulesDict pfTree =
    case derRulesDict Map.!? pfJustification pfTree of 
        Nothing -> pfTree
        Just func -> func pfTree

applyDerivedRules :: ProofTree -> ProofTree
applyDerivedRules = applyOverTree (applyDerivedRules' derivedRules)



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
        [qPf,
        ProofTree (applySubst "Q -> (P & Q)" [("P", p), ("Q", q)]) "Modus Ponens"
            [pPf,
            ProofTree (applySubst "P -> (Q -> (P & Q))" [("P", p), ("Q", q)]) "And-I" []]]
    where
        applySubst = parseWithSubst [cond, andOp] []
        [pPf, qPf] = spfs
        [p, q] = map pfContent spfs

orElimDerivedRule :: ProofTree -> ProofTree
orElimDerivedRule (ProofTree porqr pfj spfs) =
    ProofTree porqr "Modus Ponens"
        [qrPf,
        ProofTree (applySubst "QR -> PorQR" [("QR", qr), ("PorQR", porqr)]) "Modus Ponens"
            [prPf,
            ProofTree (applySubst "PR -> (QR -> PorQR)" [("PR", pr), ("QR", qr), ("PorQR", porqr)]) "Or-E" []]]
    where 
        applySubst = parseWithSubst [cond] []
        [prPf, qrPf] = spfs
        [pr, qr] = map pfContent spfs

contrapositionDerivedRule :: ProofTree -> ProofTree
contrapositionDerivedRule = undefined



-- STRENGTHENING
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
    strengtheningDerivedRule' (getEmbeddedAntecedentsUpTo cond x arg1) pfTree
    where 
        [arg1, _] = args (pfContent pfTree)
        [xyPf] = subProofs pfTree
        [x, _] = args (pfContent xyPf)



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
        strengtheningDerivedRule (ProofTree strengthenedContent "Strengthening" [ProofTree kInstance "K Axiom" []])]
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
    -- error "poopybutt"
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

-- I think this is what i had in mind
chainRulesStep :: (ProofTree -> ProofTree) -> (ProofTree -> ProofTree) -> ProofTree -> ProofTree
chainRulesStep derRule1 derRule2 (ProofTree pfc pfj spfs) =
    derRule2 (ProofTree pfc pfj [derRule1 (ProofTree pfc pfj spfs)])

chainRules :: [ProofTree -> ProofTree] -> ProofTree -> ProofTree
chainRules [] = id
chainRules (rl:remrls) = chainRulesStep rl (chainRules remrls)
    -- undefined
    -- what do we need to do? We need to:
        -- zero out the userNumbers of the result of trans1 (we should do that at the end?)
            -- we actually don't need to do that
        -- feed the last line of trans1's result to trans2
    -- hitting a roadblock. Usually, in transformations, you want to end up with the content of the current line. 
    -- with this way of doing things, you kind of lose the content of the current line, and you need to add
    -- intermediate contents. (The contents of the line you feed to the dummy transformant)
    -- Really, what you are doing is syntactic sugar at the proof level. We just need to insert a few lines, that's it
    -- the problem for the diamond derived rule is that it has a cited theorem and a derived rule. So yeah, we can make it
    -- so that the derived rule can cite theorems, but we can't make it so that the derived rule cites other derived rules. 
    -- not at the object level. But at the action level yeah. To do tht at the object level is odd