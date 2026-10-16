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
    hypSyllDerivedRule, -- from |- A -> B and |- B -> C infer |- A -> C
    modusTollens, -- special case of hypothetical syllogism with C=Bot
    adjunctionConsequentDerivedRule, -- from |- P -> Q and |- P -> R infer |- P -> (Q & R)
    strengtheningDerivedRule, -- from |- x -> y infer |- (P -> ... -> x) -> (P -> ... -> y) (any depth you'd like!)
    pushingBoxDerivedRule, distributingBoxDerivedRule, kReasoningDerivedRule -- distribute boxes, push boxes through; hope to add diamonds
    ]

andElimLTransformation :: Transformation
andElimLTransformation transformant =
    [Line n (applySubst "PandQ -> P" [("PandQ", pandq), ("P", p)]) "And-EL" [] Nothing,
     Line (n + 1) p "Modus Ponens" [lineNumber pandqLine, n] (userNumber currLine)]
    where 
        applySubst = parseWithSubst [cond] []
        currLine = fromJust (curr transformant)
        [pandqLine] = getCurrentRefLines transformant
        (pandq, p) = (lineContent pandqLine, lineContent currLine)
        n = lineNumber (currLine) + (offset transformant)
andElimLDerivedRule :: DerivedRule
andElimLDerivedRule = ("And Elim L", andElimLTransformation)

andElimRTransformation :: Transformation
andElimRTransformation transformant =
    [Line n (applySubst "PandQ -> Q" [("PandQ", lineContent pandqLine), ("Q", lineContent currLine)]) "And-ER" [] Nothing,
     Line (n + 1) (lineContent currLine) "Modus Ponens" [lineNumber pandqLine, n] (userNumber currLine)]
    where 
        applySubst = parseWithSubst [cond] []
        currLine = fromJust (curr transformant)
        n = lineNumber (currLine) + (offset transformant)
        [pandqLine] = getCurrentRefLines transformant
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
        p = case pr of
            OpNode cond [p, r] -> p
            _ -> error "a line that should be a conditional isnt"
        n = lineNumber currLine + offset transformant
hypSyllDerivedRule :: DerivedRule
hypSyllDerivedRule = ("Hypothetical Syllogism", hypSyllTransformation)

modusTollens :: DerivedRule
modusTollens = ("Modus Tollens", hypSyllTransformation) -- works because modus tollens is a subcase of hypSyll when we don't define neg hehe

adjunctionConsequentTransformation :: Transformation
adjunctionConsequentTransformation state =
    [
        Line n (applySubst "(P -> (Q -> (R -> (Q & R)))) -> ((P -> Q) -> (P -> (R -> (Q & R))))" [("P", p), ("Q", q), ("R", r)]) "Frege" [] Nothing,
        Line (n+1) (applySubst "(Q -> (R -> (Q & R))) -> (P -> (Q -> (R -> (Q & R))))" [("P", p), ("Q", q), ("R", r)]) "Simp" [] Nothing,
        Line (n+2) (applySubst "Q -> (R -> (Q & R))" [("P", p), ("Q", q), ("R", r)]) "And-I" [] Nothing,
        Line (n+3) (applySubst "P -> (Q -> (R -> (Q & R)))" [("P", p), ("Q", q), ("R", r)]) "Modus Ponens" [n+2, n+1] Nothing,
        Line (n+4) (applySubst "(P -> Q) -> (P -> (R -> (Q & R)))" [("P", p), ("Q", q), ("R", r)]) "Modus Ponens" [n+3, n] Nothing,
        Line (n+5) (applySubst "P -> (R -> (Q & R))" [("P", p), ("Q", q), ("R", r)]) "Modus Ponens" [i, n+4] Nothing,
        Line (n+6) (applySubst "(P -> (R -> (Q & R))) -> ((P -> R) -> (P -> (Q & R)))" [("P", p), ("Q", q), ("R", r)]) "Frege" [] Nothing,
        Line (n+7) (applySubst "(P -> R) -> (P -> (Q & R))" [("P", p), ("Q", q), ("R", r)]) "Modus Ponens" [n+5, n+6] Nothing,
        Line (n+8) c "Modus Ponens" [j, n+7] Nothing 
    ]
    where
        currLine = fromJust (curr state)
        c = lineContent currLine
        n = lineNumber currLine + offset state
        applySubst = parseWithSubst [cond, andOp] []
        refdLines = getCurrentRefLines state
        [i, j] = map lineNumber refdLines
        [pq, pr] = map lineContent refdLines
        [p, q] = args pq
        [_, r] = args pr
adjunctionConsequentDerivedRule :: DerivedRule
adjunctionConsequentDerivedRule = ("Adjunction in consequent", adjunctionConsequentTransformation)



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
    strengtheningTransformation' (getEmbeddedAntecedentsUpTo x arg1) state
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
        c = lineContent currLine
        [boxOutLine] = getCurrentRefLines state
        boxOut = lineContent boxOutLine
        boxOutRef = lineNumber boxOutLine
        -- [boxOutRef] = refLines currLine -- TODO: I think this needs to change. changed to above, leaving in case later have problems
        -- boxOut = lineContent (fromJust (findLineWithUserNum state boxOutRef))
        [unboxed] = args boxOut
        kInstance = makeKAxiom unboxed
        [_, kConsq] = args kInstance
pushingBoxTransformation' k state =
    recKRuleCall ++
    kLine ++
    strengtheningK ++
    [Line (n + 1 + length strengtheningK) (embed kConsq) "Modus Ponens" [n - 1, n + length strengtheningK] (userNumber currLine)]
    where
        recKRuleCall = map (\(Line ln c j r _) -> Line ln c j r Nothing) (pushingBoxTransformation' (k-1) state)
        n = lineNumber currLine + offset state + length recKRuleCall
        currLine = fromJust (curr state)
        c = lineContent currLine
        [boxOutLine] = getCurrentRefLines state
        boxOut = lineContent boxOutLine
        boxOutRef = lineNumber boxOutLine
        -- [boxOutRef] = refLines currLine
        -- boxOut = lineContent (fromJust (findLineWithUserNum state boxOutRef))
        [unboxed] = args boxOut
        kInstance = makeKAxiom (getNthConsequent k unboxed)
        kLine = [Line n kInstance "K Axiom" [] (Just n)]
        [kAnt, kConsq] = args kInstance
        embed = makeChain (getNEmbeddedAntecedents k c)
        strengthenedContent = OpNode cond [embed kAnt, embed kConsq]
        dummyState = Transformant kLine (Just (Line (n + 1) strengthenedContent "" [n] Nothing)) [] 0
        strengtheningK = map (\(Line ln c j r _) -> Line ln c j r Nothing) (strengtheningTransformation dummyState)

pushingBoxTransformation :: Transformation
pushingBoxTransformation state =
    pushingBoxTransformation' (getNForBoxes boxesIn) state
    where 
        currLine = fromJust (curr state)
        [boxOutLine] = getCurrentRefLines state
        boxOut = lineContent boxOutLine
        boxOutRef = lineNumber boxOutLine
        -- [boxOutRef] = getUpdatedCurrentRefs state
        -- [boxOutRef] = refLines currLine
        -- boxOut = lineContent (fromJust (findLineWithUserNum state boxOutRef))
        boxesIn = lineContent currLine
pushingBoxDerivedRule :: DerivedRule
pushingBoxDerivedRule = ("K reasoning (pushing Box)", pushingBoxTransformation)

distributingBoxTransformation :: Transformation
distributingBoxTransformation state =
    [(\(Line ln c j r _) -> Line ln c j r Nothing) necLine] ++ pushTheBox
    where 
        currLine = fromJust (curr state)
        [unboxedLine] = getCurrentRefLines state
        unboxedRef = lineNumber unboxedLine
        -- [unboxedRef] = refLines currLine
        unboxed = lineContent unboxedLine
        necLine = Line n (applySubst "LC" [("C", unboxed)]) "Necessitation" (refLines currLine) (Just n)
        n = lineNumber currLine + offset state
        applySubst = parseWithSubst [cond, box] []
        pushTheBox = pushingBoxTransformation (Transformant [necLine] (Just (Line (n + 1) (lineContent currLine) "" [n] (userNumber currLine))) [] 0)
distributingBoxDerivedRule :: DerivedRule
distributingBoxDerivedRule = ("K reasoning (distributing Box)", distributingBoxTransformation)

kReasoningTransformation :: Transformation
kReasoningTransformation state =
    if topOp referencedLineContent == box
        then pushingBoxTransformation state
        else distributingBoxTransformation state
    where 
        [referencedLine] = getCurrentRefLines state
        referencedLineNum = lineNumber referencedLine
        referencedLineContent = lineContent referencedLine
        -- [referencedLineNum] = refLines (fromJust (curr state))
        -- referencedLineContent = lineContent (fromJust (findLineWithUserNum state referencedLineNum))
kReasoningDerivedRule :: DerivedRule
kReasoningDerivedRule = ("K reasoning", kReasoningTransformation)