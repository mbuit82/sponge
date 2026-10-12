module Defs.Rules where

import Core
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
    hypSyllDerivedRule, modusTollens
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
        Line n (applySubst "PQ -> ((P -> QR) -> PR)" [("P", p), ("PQ", pq), ("QR", qr), ("PR", pr)]) "Axiom3" [] Nothing,
        Line (n + 1) (applySubst "QR -> (P -> QR)" [("P", p), ("QR", qr), ("PR", pr)]) "Axiom2" [] Nothing,
        Line (n + 2) (applySubst "P -> QR" [("P", p), ("QR", qr)]) "Modus Ponens" [lineNumber qrLine, n + 1] Nothing,
        Line (n + 3) (applySubst "(P -> QR) -> PR" [("P", p), ("QR", qr), ("PR", pr)]) "Modus Ponens" [lineNumber pqLine, n] Nothing,
        Line (n + 4) pr "Modus Ponens" [n + 2, n + 3] (userNumber currLine)
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