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
derivedRules :: Map.Map String Transformation
derivedRules = Map.fromList [ 
    andElimLDerivedRule, -- from |- A & B infer |- A
    andElimRDerivedRule,  -- from |- A & B infer |- B
    adjunctionDerivedRule, -- from |- A and |- B infer |- A & B
    orElimDerivedRule, -- from |- A -> C and |- B -> C infer |- (A v B) -> C
    modusTollens, -- special case of hypothetical syllogism with C=Bot
    -- forget about the ones below for now
    contrapositionDerivedRule,
    strengtheningDerivedRule, -- from |- x -> y infer |- (P -> ... -> x) -> (P -> ... -> y) (any depth you'd like!)
    distributingDiamondsDerivedRule, 
    kReasoningDerivedRule -- distribute boxes, push boxes through; hope to add diamonds
    ]

-- some things need to happen on every transformation. For example, making the last line have the right userNumber reference
-- why don't we do that at the moment of application? 
-- And I think transformations in general should only search previous lines by userNumber.
-- which would mean, when stacking transformations, it's actually good to have the last one have the wrong userNumber reference
-- so when do we fix them? 

andElimLTransformation :: Transformation
andElimLTransformation transformant =
    [Line n (applySubst "PandQ -> P" [("PandQ", pandq), ("P", p)]) "And-EL" [] Nothing,
     Line (n + 1) p "Modus Ponens" [lineNumber pandqLine, n] (userNumber currLine)]
    where 
        n = lineNumber currLine + offset transformant
        currLine = fromJust (curr transformant)
        applySubst = parseWithSubst [cond] []
        [pandqLine] = getCurrentRefLines transformant
        (pandq, p) = (lineContent pandqLine, lineContent currLine)
andElimLDerivedRule :: DerivedRule
andElimLDerivedRule = ("And Elim L", andElimLTransformation)

andElimRTransformation :: Transformation
andElimRTransformation transformant =
    [Line n (applySubst "PandQ -> Q" [("PandQ", pandq), ("Q", q)]) "And-ER" [] Nothing,
     Line (n + 1) q "Modus Ponens" [lineNumber pandqLine, n] (userNumber currLine)]
    where 
        n = lineNumber currLine + offset transformant
        currLine = fromJust (curr transformant)
        applySubst = parseWithSubst [cond] []
        [pandqLine] = getCurrentRefLines transformant
        (pandq, q) = (lineContent pandqLine, lineContent currLine)
andElimRDerivedRule :: DerivedRule
andElimRDerivedRule = ("And Elim R", andElimRTransformation)

adjunctionTransformation :: Transformation
adjunctionTransformation transformant =
    [
        Line n (applySubst "P -> (Q -> (P & Q))" [("P", p), ("Q", q)]) "And-I" [] Nothing,
        Line (n + 1) (applySubst "Q -> (P & Q)" [("P", p), ("Q", q)]) "Modus Ponens" [lineNumber pLine, n] Nothing,
        Line (n + 2) (applySubst "P & Q" [("P", p), ("Q", q)]) "Modus Ponens" [lineNumber qLine, n +1] (userNumber currLine)
    ]
    where 
        applySubst = parseWithSubst [cond, andOp] []
        currLine = fromJust (curr transformant)
        (p, q) = (lineContent pLine, lineContent qLine)
        n = lineNumber (currLine) + (offset transformant)
        [pLine, qLine] = getCurrentRefLines transformant
adjunctionDerivedRule :: DerivedRule
adjunctionDerivedRule = ("Adjunction", adjunctionTransformation)

-- -- for Or Intro L and Or Intro R, we need to be able to add arbitrary sentences to the additional material
-- -- can now do that, just need to figure out parsing
-- orIntroLTransformation :: Transformation
-- orIntroLTransformation transformant =
--     [
--         Line n (OpNode cond [])
--     ]
--     where 
--         currLine = fromJust (curr transformant)
--         n = lineNumber (currLine) + (offset transformant)
--         [pLine] = getCurrentRefLines transformant

orElimTransformation :: Transformation
orElimTransformation transformant =
    [
        Line n (applySubst "PR -> (QR -> PorQR)" [("PR", pr), ("QR", qr), ("PorQR", porqr)]) "Or-E" [] Nothing,
        Line (n + 1) (applySubst "QR -> PorQR" [("QR", qr), ("PorQR", porqr)]) "Modus Ponens" [lineNumber prLine, n] Nothing,
        Line (n + 2) porqr "Modus Ponens" [lineNumber qrLine, n + 1] (userNumber currLine)
    ]
    where 
        applySubst = parseWithSubst [cond] []
        [prLine, qrLine] = getCurrentRefLines transformant
        currLine = fromJust (curr transformant)
        pr = lineContent prLine
        qr = lineContent qrLine
        porqr = lineContent currLine
        n = lineNumber currLine + offset transformant
orElimDerivedRule :: DerivedRule
orElimDerivedRule = ("Or Elim", orElimTransformation)

hypSyllTransformation :: Transformation
hypSyllTransformation transformant =
    [
        Line n (applySubst "(P -> QR) -> (PQ -> PR)" [("P", p), ("PQ", pq), ("QR", qr), ("PR", pr)]) "Frege" [] Nothing,
        Line (n + 1) (applySubst "QR -> (P -> QR)" [("P", p), ("PQ", pq), ("QR", qr), ("PR", pr)]) "Simp" [] Nothing,
        Line (n + 2) (applySubst "P -> QR" [("P", p), ("PQ", pq), ("QR", qr), ("PR", pr)]) "Modus Ponens" [lineNumber qrLine, n + 1] Nothing,
        Line (n + 3) (applySubst "PQ -> PR" [("P", p), ("PQ", pq), ("QR", qr), ("PR", pr)]) "Modus Ponens" [n + 2, n] Nothing,
        Line (n + 4) pr "Modus Ponens" [lineNumber pqLine, n + 3] (userNumber currLine)
    ]
    where 
        applySubst = parseWithSubst [cond] []
        currLine = fromJust (curr transformant)
        [pqLine, qrLine] = getCurrentRefLines transformant
        pq = lineContent pqLine
        qr = lineContent qrLine
        pr = lineContent currLine
        [p, _] = args pr
        n = lineNumber currLine + offset transformant
hypSyllDerivedRule :: DerivedRule
hypSyllDerivedRule = ("Hypothetical Syllogism", hypSyllTransformation)

modusTollens :: DerivedRule
modusTollens = ("Modus Tollens", hypSyllTransformation) -- works because modus tollens is a subcase of hypSyll when we don't define neg hehe

-- adjunctionConsequentTransformation :: Transformation
-- adjunctionConsequentTransformation state =
--     [
--         Line n (applySubst "(P -> (Q -> (R -> (Q & R)))) -> ((P -> Q) -> (P -> (R -> (Q & R))))" [("P", p), ("Q", q), ("R", r)]) "Frege" [] Nothing,
--         Line (n+1) (applySubst "(Q -> (R -> (Q & R))) -> (P -> (Q -> (R -> (Q & R))))" [("P", p), ("Q", q), ("R", r)]) "Simp" [] Nothing,
--         Line (n+2) (applySubst "Q -> (R -> (Q & R))" [("P", p), ("Q", q), ("R", r)]) "And-I" [] Nothing,
--         Line (n+3) (applySubst "P -> (Q -> (R -> (Q & R)))" [("P", p), ("Q", q), ("R", r)]) "Modus Ponens" [n+2, n+1] Nothing,
--         Line (n+4) (applySubst "(P -> Q) -> (P -> (R -> (Q & R)))" [("P", p), ("Q", q), ("R", r)]) "Modus Ponens" [n+3, n] Nothing,
--         Line (n+5) (applySubst "P -> (R -> (Q & R))" [("P", p), ("Q", q), ("R", r)]) "Modus Ponens" [i, n+4] Nothing,
--         Line (n+6) (applySubst "(P -> (R -> (Q & R))) -> ((P -> R) -> (P -> (Q & R)))" [("P", p), ("Q", q), ("R", r)]) "Frege" [] Nothing,
--         Line (n+7) (applySubst "(P -> R) -> (P -> (Q & R))" [("P", p), ("Q", q), ("R", r)]) "Modus Ponens" [n+5, n+6] Nothing,
--         Line (n+8) c "Modus Ponens" [j, n+7] Nothing 
--     ]
--     where
--         currLine = fromJust (curr state)
--         c = lineContent currLine
--         n = lineNumber currLine + offset state
--         applySubst = parseWithSubst [cond, andOp] []
--         refdLines = getCurrentRefLines state
--         [i, j] = map lineNumber refdLines
--         [pq, pr] = map lineContent refdLines
--         [p, q] = args pq
--         [_, r] = args pr
-- adjunctionConsequentDerivedRule :: DerivedRule
-- adjunctionConsequentDerivedRule = ("Adjunction in consequent", adjunctionConsequentTransformation)

-- inversionTransformation :: Transformation
-- inversionTransformation state = 
--     [
--         Line n (applySubst "(P -> Q) -> ((Q -> R) -> (P -> Q))" substList) "Simp" [] Nothing,
--         Line (n+1) (applySubst "(Q -> R) -> (P -> Q)" substList) "Modus Ponens" [i, n] Nothing,
--         Line (n+2) (applySubst "(Q -> R) -> (P -> (Q -> R))" substList) "Simp" [] Nothing,
--         Line (n+3) (applySubst "(P -> (Q -> R)) -> ((P -> Q) -> (P -> R))" substList) "Frege" [] Nothing,
--         Line (n+4) (applySubst "((P -> (Q -> R)) -> ((P -> Q) -> (P -> R))) -> ((Q -> R) -> ((P -> (Q -> R)) -> ((P -> Q) -> (P -> R))))" substList) "Simp" [] Nothing,
--         Line (n+5) (applySubst "(Q -> R) -> ((P -> (Q -> R)) -> ((P -> Q) -> (P -> R)))" substList) "Modus Ponens" [n+3, n+4] Nothing,
--         Line (n+6) (applySubst "((Q -> R) -> ((P -> (Q -> R)) -> ((P -> Q) -> (P -> R)))) -> (((Q -> R) -> (P -> (Q -> R))) -> ((Q -> R) -> ((P -> Q) -> (P -> R))))" substList) "Frege" [] Nothing,
--         Line (n+7) (applySubst "((Q -> R) -> (P -> (Q -> R))) -> ((Q -> R) -> ((P -> Q) -> (P -> R)))" substList) "Modus Ponens" [n+5, n+6] Nothing,
--         Line (n+8) (applySubst "(Q -> R) -> ((P -> Q) -> (P -> R))" substList) "Modus Ponens" [n+2, n+7] Nothing,
--         Line (n+9) (applySubst "((Q -> R) -> ((P -> Q) -> (P -> R))) -> (((Q -> R) -> (P -> Q)) -> ((Q -> R) -> (P -> R)))" substList) "Frege" [] Nothing,
--         Line (n+10) (applySubst "((Q -> R) -> (P -> Q)) -> ((Q -> R) -> (P -> R))" substList) "Modus Ponens" [n+8, n+9] Nothing,
--         Line (n+11) (applySubst "(Q -> R) -> (P -> R)" substList) "Modus Ponens" [n+1, n+10] (userNumber currLine)
--     ]
--     where 
--         n = lineNumber currLine + offset state
--         currLine = fromJust (curr state)
--         c = lineContent currLine
--         [qr, pr] = args c
--         [p, r] = args pr
--         [q, _] = args qr
--         [i] = getUpdatedCurrentRefs state
--         applySubst = parseWithSubst [cond] []
--         substList = [("P", p), ("Q", q), ("R", r)]
-- inversionDerivedRule :: DerivedRule
-- inversionDerivedRule = ("Inversion", inversionTransformation)

-- contrapositionBackwardTransformation :: Transformation
-- contrapositionBackwardTransformation state = undefined

contrapositionTransformation :: Transformation
contrapositionTransformation state = undefined
--     | curr1 == OpNode cond [refd2, OpNode bot []] &&
--         curr2 == OpNode cond [refd1, OpNode bot []] =
--             inversionTransformation state
--     | refd2 == OpNode cond [curr1, OpNode bot []] &&
--         refd1 == OpNode cond [curr2, OpNode bot []] = 
--             contrapositionBackwardTransformation state
--     | otherwise = error "error in using contraposition. seems like don't match reqs for contraposition"
--     where 
--         currContent = lineContent (fromJust (curr state))
--         [refdLine] = getCurrentRefLines state
--         refdContent = lineContent refdLine
--         [curr1, curr2] = args currContent
--         [refd1, refd2] = args refdContent
contrapositionDerivedRule :: (String, Transformation)
contrapositionDerivedRule = ("Contraposition", contrapositionTransformation)

-- switchArgsTransformation :: Transformation
-- switchArgsTransformation state =
--     [
--         Line n (applySubst "(A -> (B -> C)) -> (B -> (A -> (B -> C)))" substList) "Simp" [] Nothing,
--         Line (n+1) (applySubst "B -> (A -> (B -> C))" substList) "Modus Ponens" [i, n] Nothing, 
--         Line (n+2) (applySubst "B -> (A -> B)" substList) "Simp" [] Nothing, 
--         Line (n+3) (applySubst "(A -> (B -> C)) -> ((A -> B) -> (A -> C))" substList) "Frege" [] Nothing, 
--         Line (n+4) (applySubst "((A -> (B -> C)) -> ((A -> B) -> (A -> C))) -> (B -> ((A -> (B -> C)) -> ((A -> B) -> (A -> C))))" substList) "Simp" [] Nothing, 
--         Line (n+5) (applySubst "B -> ((A -> (B -> C)) -> ((A -> B) -> (A -> C)))" substList) "Modus Ponens" [n+3, n+4] Nothing, 
--         Line (n+6) (applySubst "(B -> ((A -> (B -> C)) -> ((A -> B) -> (A -> C)))) -> ((B -> (A -> (B -> C))) -> (B -> ((A -> B) -> (A -> C))))" substList) "Frege" [] Nothing, 
--         Line (n+7) (applySubst "(B -> (A -> (B -> C))) -> (B -> ((A -> B) -> (A -> C)))" substList) "Modus Ponens" [n+5, n+6] Nothing, 
--         Line (n+8) (applySubst "B -> ((A -> B) -> (A -> C))" substList) "Modus Ponens" [n+1, n+7] Nothing, 
--         Line (n+9) (applySubst "(B -> ((A -> B) -> (A -> C))) -> ((B -> (A -> B)) -> (B -> (A -> C)))" substList) "Frege" [] Nothing, 
--         Line (n+10) (applySubst "(B -> (A -> B)) -> (B -> (A -> C))" substList) "Modus Ponens" [n+8, n+9] Nothing, 
--         Line (n+11) (applySubst "B -> (A -> C)" substList) "Modus Ponens" [n+2, n+10] (userNumber currLine)
--     ]
--     where 
--         n = lineNumber currLine + offset state
--         currLine = fromJust (curr state)
--         abc = lineContent currLine
--         [b, ac] = args abc
--         [a, c] = args ac
--         [i] = getUpdatedCurrentRefs state
--         applySubst = parseWithSubst [cond] []
--         substList = [("A", a), ("B", b), ("C", c)]
-- switchArgsDerivedRule :: DerivedRule
-- switchArgsDerivedRule = ("switching arguments", switchArgsTransformation)



-- STRENGTHENING
strengtheningTransformation' :: [Sentence] -> Transformant -> [Line]
strengtheningTransformation' [] _ = []
strengtheningTransformation' [p] state =
    [
        Line n (applySubst "(X -> Y) -> ((P -> (X -> Y)))" [("P", p), ("X", x), ("Y", y)]) "Simp" [] Nothing,
        Line (n+1) (applySubst "P -> (X -> Y)" [("P", p), ("X", x), ("Y", y)]) "Modus Ponens" [lineNumber xyLine, n] Nothing,
        Line (n+2) (applySubst "(P -> (X -> Y)) -> ((P -> X) -> (P -> Y))" [("P", p), ("X", x), ("Y", y)]) "Frege" [] Nothing,
        Line (n+3) (applySubst "(P -> X) -> (P -> Y)" [("P", p), ("X", x), ("Y", y)]) "Modus Ponens" [n+1, n+2] (userNumber currLine)
    ]
    where 
        currLine = fromJust (curr state)
        [xyLine] = getCurrentRefLines state
        [x, y] = args (lineContent xyLine)
        applySubst = parseWithSubst [cond] []
        n = lineNumber currLine + offset state
-- technically wrong bc will have multiple lines with userNumber currLine but I think any resulting searches will find the first one
-- would matter if we invoke a derived rule on the result of this. so in K! Well no bc I'll avoid that by construction lol
-- actually wouldn't even matter in that case bc unfolding is strictly increasing in line number
-- in K you used to have a mapping function that avoided this. removed it and it works
strengtheningTransformation' (p:rest) state =
    strengthenRest ++ -- the last line looks like chainX -> chainY
    [
        Line n (applySubst "(X' -> Y') -> (P -> (X' -> Y'))" [("X'", x'), ("Y'", y'), ("P", p)]) "Simp" [] Nothing,
        Line (n+1) (applySubst "P -> (X' -> Y')" [("P", p), ("X'", x'), ("Y'", y')]) "Modus Ponens" [lineNumber (last strengthenRest), n] Nothing,
        Line (n+2) (applySubst "(P -> (X' -> Y')) -> ((P -> X') -> (P -> Y'))" [("P", p), ("X'", x'), ("Y'", y')]) "Frege" [] Nothing,
        Line (n+3) (applySubst "(P -> X') -> (P -> Y')" [("P", p), ("X'", x'), ("Y'", y')]) "Modus Ponens" [n+1, n+2] (userNumber currLine)
    ]
    where 
        currLine = fromJust (curr state)
        applySubst = parseWithSubst [cond] []
        strengthenRest = strengtheningTransformation' rest state
        [x', y'] = args (lineContent (last strengthenRest))
        n = lineNumber currLine + offset state + length strengthenRest

strengtheningTransformation :: Transformation
strengtheningTransformation state = 
    strengtheningTransformation' (getEmbeddedAntecedentsUpTo cond x arg1) state
    where 
        currLine = fromJust (curr state)
        [arg1, _] = args (lineContent currLine)
        [xyLine] = getCurrentRefLines state
        [x, _] = args (lineContent xyLine)
strengtheningDerivedRule :: DerivedRule
strengtheningDerivedRule = ("Strengthening", strengtheningTransformation)



-- K derived rules
countConds :: Int -> Sentence -> Int
countConds n (OpNode op args)
    | op == cond = countConds (n+1) (args !! 1) 
    | op == box = n
    | otherwise = error "somethings up"

-- we apply this on the current state of the transformant
getNForBoxes :: Sentence -> Int
getNForBoxes = countConds (-1)

-- This is for a BOXED SENTENCE. Particularly, exactly the cited line
makeKAxiom :: Sentence -> Sentence
makeKAxiom (OpNode opCond [arg1, arg2])
    | opCond == cond =
        parseWithSubst [cond, box] [] "L(A1 -> A2) -> (LA1 -> LA2)" [("A1", arg1), ("A2", arg2)]
    | otherwise = error "cited line for distributing boxes is not of form L(A1 -> A2) but ALMOST AAGGHHH"
makeKAxiom _ = error "cited line for distributing boxes is not of form L(A1 -> A2)"

pushingBoxTransformation' :: Int -> Transformation
pushingBoxTransformation' 0 state =
    [
        Line n kInstance "K Axiom" [] Nothing,
        Line (n+1) kConsq "Modus Ponens" [boxOutRef, n] (userNumber currLine) 
    ]
    where
        n = lineNumber currLine + offset state
        currLine = fromJust (curr state)
        [boxOutLine] = getCurrentRefLines state
        (boxOut, boxOutRef) = (lineContent boxOutLine, lineNumber boxOutLine)
        [unboxed] = args boxOut
        kInstance = makeKAxiom unboxed
        [_, kConsq] = args kInstance
pushingBoxTransformation' k state =
    recKRuleCall ++
    kLine ++
    strengtheningK ++
    [Line (n + 1 + length strengtheningK) (embed kConsq) "Modus Ponens" [n - 1, n + length strengtheningK] (userNumber currLine)]
    where
        recKRuleCall = (pushingBoxTransformation' (k-1) state)
        n = lineNumber currLine + offset state + length recKRuleCall
        currLine = fromJust (curr state)
        c = lineContent currLine
        [boxOutLine] = getCurrentRefLines state
        boxOut = lineContent boxOutLine
        boxOutRef = lineNumber boxOutLine
        [unboxed] = args boxOut
        kInstance = makeKAxiom (getNthConsequent cond k unboxed)
        kLine = [Line n kInstance "K Axiom" [] (Just 1000)] -- so it can be found in the transformation applied to dummyState
        [kAnt, kConsq] = args kInstance
        embed = makeChain cond (getNEmbeddedAntecedents cond k c)
        strengthenedContent = OpNode cond [embed kAnt, embed kConsq]
        dummyState = Transformant kLine (Just (Line (n + 1) strengthenedContent "" [1000] Nothing)) [] 0
        strengtheningK = (strengtheningTransformation dummyState)

pushingBoxTransformation :: Transformation
pushingBoxTransformation state =
    pushingBoxTransformation' (getNForBoxes boxesIn) state
    where 
        currLine = fromJust (curr state)
        [boxOutLine] = getCurrentRefLines state
        boxOut = lineContent boxOutLine
        boxOutRef = lineNumber boxOutLine
        boxesIn = lineContent currLine
pushingBoxDerivedRule :: DerivedRule
pushingBoxDerivedRule = ("K reasoning (pushing Box)", pushingBoxTransformation)

distributingBoxTransformation :: Transformation
distributingBoxTransformation state =
    [necLine] ++ pushTheBox -- seems like I don't need to delete the user num on necLine
    where 
        n = lineNumber currLine + offset state
        applySubst = parseWithSubst [cond, box] []
        currLine = fromJust (curr state)
        [unboxedLine] = getCurrentRefLines state
        unboxedRef = lineNumber unboxedLine
        unboxed = lineContent unboxedLine
        necLine = Line n (applySubst "LC" [("C", unboxed)]) "Necessitation" [unboxedRef] (Just 1000) -- userNum is that way so can be foudn in pushTheBox transformation
        -- we could even give the current userNumber to necLine. That would be what chaining would do
        pushTheBox = pushingBoxTransformation (Transformant [necLine] (Just (Line (n + 1) (lineContent currLine) "" [1000] (userNumber currLine))) [] 0)
distributingBoxDerivedRule :: DerivedRule
distributingBoxDerivedRule = ("K reasoning (distributing Box)", distributingBoxTransformation)

kReasoningTransformation :: Transformation
kReasoningTransformation state
    | isInstance currContent (parse [cond] [diamond] "MP -> MQ") =
        distributingDiamondsTransformation state
    | topOp referencedLineContent == box = 
        pushingBoxTransformation state
    | otherwise = 
        distributingBoxTransformation state
    where 
        [referencedLine] = getCurrentRefLines state
        referencedLineContent = lineContent referencedLine
        currContent = lineContent (fromJust (curr state))
kReasoningDerivedRule :: DerivedRule
kReasoningDerivedRule = ("K reasoning", kReasoningTransformation)

distributingDiamondsTransformation :: Transformation
distributingDiamondsTransformation state =
    [
        Line n (applySubst "~Q -> ~P" [("P", p), ("Q", q)]) "applying contrapositive_forward (from minimal)" [lineNumber refdLine] Nothing,
        Line (n + 1) (applySubst "L(~Q -> ~P)" [("P", p), ("Q", q)]) "Necessitation" [n] Nothing,
        Line (n + 2) (applySubst "L(~Q -> ~P) -> (L~Q -> L~P)" [("P", p), ("Q", q)]) "K Axiom" [] Nothing,
        Line (n + 3) (applySubst "L~Q -> L~P" [("P", p), ("Q", q)]) "Modus Ponens" [n + 1, n + 2] Nothing,
        Line (n + 4) (applySubst "MP -> MQ" [("P", p), ("Q", q)]) "applying contrapositive_forward (from minimal)" [n + 3] (userNumber currLine)
    ]
    where 
        n = lineNumber currLine + offset state
        applySubst = parseWithSubst [cond, box] [diamond, neg]
        currLine = fromJust (curr state)
        [refdLine] = getCurrentRefLines state
        [p, q] = args (lineContent refdLine)
distributingDiamondsDerivedRule :: DerivedRule
distributingDiamondsDerivedRule = ("K reasoning (distributing diamonds)", distributingDiamondsTransformation)


-- something like this
chainTransformationsStep :: Transformation -> Transformation -> Transformation
chainTransformationsStep trans1 trans2 state =
    trans1Result ++ trans2 (Transformant trans1ResRevRest (Just trans1TopLine) [] 0)
    where
        trans1ResRev = reverse (trans1 state)
        trans1TopLine:trans1ResRevRest = trans1ResRev
        
        trans1Result = trans1 state
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