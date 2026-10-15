module Defs.Rules where

import Core
import Parse.Sentences

import Defs.Operators

import Data.Maybe
import qualified Data.Map as Map

modusPonens :: InferenceRule
modusPonens = InferenceRule "Modus Ponens" (parse [] [] "P", Just (parse [cond] [] "P -> Q")) (parse [] [] "Q")

necessitation :: InferenceRule
necessitation = InferenceRule "Necessitation" (parse [] [] "P", Nothing) (parse [box] [] "L P")



-- DERIVED RULES
-- The way derived rules work is that they're applied on everything. If you use one for a logic that doesn't have the required axioms, then the Datalog proof just won't go through (and eventually we'll get an error pointing to the right user line). Nothing too terrible. And they _really_, really don't belong in the logics. 
derivedRules :: Map.Map String Transformation
derivedRules = Map.fromList [ andElimLDerivedRule, andElimRDerivedRule, adjunctionDerivedRule,
    orElimDerivedRule, 
    hypSyllDerivedRule, modusTollens,
    strengtheningDerivedRule
    ]

andElimLTransformation :: Transformation
andElimLTransformation transformant =
    [Line n (applySubst "PandQ -> P" [("PandQ", pandq), ("P", p)]) "And-EL" [] Nothing,
     Line (n + 1) p "Modus Ponens" [lineNumber pandqLine, n] (userNumber currLine)]
    where 
        applySubst = getApplySubstFromTransformant transformant
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
        applySubst = getApplySubstFromTransformant transformant
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
        applySubst = getApplySubstFromTransformant transformant
        currLine = fromJust (curr transformant)
        (p, q) = (lineContent pLine, lineContent qLine)
        n = lineNumber (currLine) + (offset transformant)
        [pLine, qLine] = getCurrentRefLines transformant
adjunctionDerivedRule :: DerivedRule
adjunctionDerivedRule = ("Adjunction", adjunctionTransformation)

-- -- for Or Intro L and Or Intro R, we need to be able to add arbitrary sentences to the additional material
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
        applySubst = getApplySubstFromTransformant transformant
        [prLine, qrLine] = getCurrentRefLines transformant
        currLine = fromJust (curr transformant)
        pr = lineContent prLine
        qr = lineContent qrLine
        porqr = lineContent currLine
        n = lineNumber currLine + offset transformant
orElimDerivedRule :: DerivedRule
orElimDerivedRule = ("Or Elim", orElimTransformation)

-- think I'll keep the one with two. Used it once in a modal logic proof lol so reason to have the one with only 2. 
-- orElimTransformation :: Transformation
-- orElimTransformation transformant =
--     [
--         Line n (applySubst "PR -> (QR -> (PorQ -> R))" [("PR", pr), ("QR", qr), ("PorQ", porq), ("R", r)]) "Or-E" [] Nothing,
--         Line (n + 1) (applySubst "QR -> (PorQ -> R)" [("QR", qr), ("PorQ", porq), ("R", r)]) "Modus Ponens" [lineNumber prLine, n] Nothing,
--         Line (n + 2) (applySubst "PorQ -> R" [("PorQ", porq), ("R", r)]) "Modus Ponens" [lineNumber qrLine, n + 1] Nothing,
--         Line (n + 3) r "Modus Ponens" [lineNumber porqLine, n + 2] (userNumber currLine)
--     ]
--     where 
--         applySubst = getApplySubstFromTransformant transformant
--         [prLine, qrLine, porqLine] = getCurrentRefLines transformant
--         currLine = fromJust (curr transformant)
--         pr = lineContent prLine
--         qr = lineContent qrLine
--         porq = lineContent porqLine
--         r = lineContent currLine
--         n = lineNumber currLine + offset transformant
-- orElimDerivedRule :: DerivedRule
-- orElimDerivedRule = ("Or Elim", orElimTransformation)

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
        applySubst = getApplySubstFromTransformant transformant
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







-- STRENGTHENING

getNEmbeddedAntecedents :: Int -> Sentence -> [Sentence]
getNEmbeddedAntecedents 0 _ = []
getNEmbeddedAntecedents n (OpNode op [arg1, arg2])
    | op == cond = arg1 : getNEmbeddedAntecedents (n-1) arg2
    | otherwise = error "can only get N antecedents on a conditional"

getNthConsequent :: Int -> Sentence -> Sentence
getNthConsequent 0 sent = sent
getNthConsequent n (OpNode op [arg1, arg2])
    | op == cond = getNthConsequent (n-1) arg2
    | otherwise = error "can only get Nth consequent on a conditional"

getAllEmbeddedAntecedents :: Sentence -> [Sentence]
getAllEmbeddedAntecedents (Atom a) = []
getAllEmbeddedAntecedents (OpNode op [arg1, arg2])
    | op == cond = arg1 : getAllEmbeddedAntecedents arg2
    | otherwise = error "can only get all antecedents on a chain of conditionals"
    
getLastConsequent :: Sentence -> Sentence
getLastConsequent (Atom a) = Atom a
getLastConsequent (OpNode op [arg1, arg2])
    | op == cond = getLastConsequent arg2
    | otherwise = error "can only get last consequent on a chain of conditionals"

getEmbeddedAntecedentsUpTo :: Sentence -> Sentence -> [Sentence]
getEmbeddedAntecedentsUpTo stopSent sent
    | sent == stopSent = []
    | otherwise = case sent of
        Atom a -> error ("supposed to have reached stopSent " ++ show stopSent ++ " but never did?")
        (OpNode op [arg1, arg2]) -> 
            if op == cond
                then arg1 : getEmbeddedAntecedentsUpTo stopSent arg2
                else error "can only get all antecedents on a chain of conditionals"

makeChain :: [Sentence] -> Sentence -> Sentence
makeChain [] consq = consq
makeChain (p:rem) consq = OpNode cond [p, makeChain rem consq]


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
        [xyLineNum] = refLines currLine
        xyLine = fromJust (findLineWithUserNum state xyLineNum)
        [x, y] = args (lineContent xyLine)
        applySubst = getApplySubstFromTransformant state
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
        applySubst = getApplySubstFromTransformant state
        strengthenRest = strengtheningTransformation' rest state
        [x', y'] = args (lineContent (last strengthenRest))
        n = lineNumber currLine + offset state + length strengthenRest

strengtheningTransformation :: Transformation
strengtheningTransformation state = 
    strengtheningTransformation' (getEmbeddedAntecedentsUpTo x arg1) state
    where 
        currLine = fromJust (curr state)
        [arg1, _] = args (lineContent currLine)
        [xyLineRef] = refLines currLine
        xyLine = fromJust (findLineWithUserNum state xyLineRef)
        [x, _] = args (lineContent xyLine)
strengtheningDerivedRule :: DerivedRule
strengtheningDerivedRule = ("Strengthening", strengtheningTransformation)








-- -- K Box distribution derived rule

-- distributeBoxes :: Int -> Transformation
-- distributeBoxes 0 state =
--     [
--         Line n (applySubst "L(X -> Y) -> (LX -> LY)" [("X", x), ("Y", y)]) "K Axiom" [] Nothing,
--         Line (n+1) (applySubst "LX -> LY" [("X", x), ("Y", y)]) "Modus Ponens" [lpqLineNumber, n] (userNumber currLine) 
--     ]
--     where
--         currLine = fromJust (curr state)
--         applySubst = getApplySubstFromTransformant state
--         n = lineNumber currLine + offset state
--         [lpqLineNumber] = refLines currLine
--         (OpNode _ [OpNode _ [x, y]]) = lineContent (fromJust (findLineWithUserNum state lpqLineNumber))
-- distributeBoxes k state =
--     [
--         Line n (applySubst "L(X -> Y) -> (LX -> LY)" [("X", x), ("Y", y)]) "K Axiom" [] Nothing,
--         -- alright. _this_ is where we build the chain
--     ] ++
--     map (\(Line n c j r u) -> Line (n + 1) c j (map (+1) r) u) strengthenResult ++ --FUCK! This doesn't work because we don't want to add one to the previous ugh
--     recursionOnBoxes ++ 
--     [
--         Line (n + 1 + length strengthenResult + length recursionOnBoxes) 
--     ]
--     where 
--         n = undefined
--         applySubst = getApplySubstFromTransformant state
--         x = undefined
--         y = undefined
--         strengthenResult = undefined -- strengtheningTransformation on the state, except we want the state to have the first line as current
--         recursionOnBoxes = distributeBoxes k-1 state

-- k1 :: Transformation 
-- k1 state = 