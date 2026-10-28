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
    -- contrapositionDerivedRule,
    ("strengthening", strengtheningDerivedRule), -- from |- x -> y infer |- (P -> ... -> x) -> (P -> ... -> y) (any depth you'd like!)
    ("weakening", weakeningDerivedRule),
    ("embedding", embeddingDerivedRule),
    ("K reasoning", kReasoningDerivedRule) -- distribute boxes, push boxes through; hope to add diamonds
    ]

applyDerivedRules' :: Map.Map String (ProofTree -> ProofTree) -> ProofTree -> ProofTree
applyDerivedRules' derRulesDict pfTree =
    case derRulesDict Map.!? pfJustification pfTree of 
        Nothing -> pfTree
        Just func -> func pfTree

applyDerivedRules :: ProofTree -> ProofTree
applyDerivedRules = applyOverTree (applyDerivedRules' derivedRules)


contrapositionDerivedRule :: ProofTree -> ProofTree
contrapositionDerivedRule = undefined




makeModusPonensLines :: [ProofTree] -> ProofTree -> ProofTree
makeModusPonensLines [] pfTree = pfTree
makeModusPonensLines (spf:rem) pfTree = 
    makeModusPonensLines rem (ProofTree consq "Modus Ponens" [spf, pfTree])
    where 
        [_, consq] = args (pfContent pfTree)



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
-- won't work bc pfc is repeated. idk if there's an easy way to do this
-- because derived rules don't just grow leaves; they grow branches. We need to know what the branches look like before
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



