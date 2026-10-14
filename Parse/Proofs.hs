module Parse.Proofs where

import Core
import Parse.Sentences

import Defs.Specs

import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map
import System.Directory 

-- EXAMPLE: Deduction lemma. 
-- I want this to be what a transformation looks like. 
axiomCaseTransformation :: Sentence -> Transformation
axiomCaseTransformation hyp transformant = 
    [   
        Line n (lineContent currLine) (justification currLine) [] Nothing,
        Line (n + 1) (applySubst "C -> (H -> C)" [("H", hyp), ("C", c)]) "Simp" [] Nothing,
        Line (n + 2) (applySubst "H -> C" [("H", hyp), ("C", c)]) "Modus Ponens" [n, n + 1] (userNumber currLine)
    ]
    where 
        applySubst = getApplySubstFromTransformant transformant
        c = lineContent currLine
        currLine = fromJust (curr transformant)
        n = lineNumber (currLine) + (offset transformant)

hypCaseTransformation :: Transformation
hypCaseTransformation transformant = 
    [
        Line n (applySubst "((H -> ((H -> H) -> H)) -> ((H -> (H -> H)) -> (H -> H)))" [("H", c)]) "Frege" [] Nothing,
        Line (n + 1) (applySubst "H -> ((H -> H) -> H)" [("H", c)]) "Simp" [] Nothing,
        Line (n + 2) (applySubst "(H -> (H -> H)) -> (H -> H))" [("H", c)]) "Modus Ponens" [n + 1, n] Nothing,
        Line (n + 3) (applySubst "H -> (H -> H)" [("H", c)]) "Simp" [] Nothing,
        Line (n + 4) (applySubst "H -> H" [("H", c)]) "Modus Ponens" [n + 3, n + 2] (userNumber currLine)
    ]
    where 
        applySubst = getApplySubstFromTransformant transformant
        currLine = fromJust (curr transformant)
        c = lineContent currLine
        n = lineNumber (currLine) + (offset transformant)

modusPonensCaseTransformation :: Sentence -> Transformation
modusPonensCaseTransformation hyp transformant = -- pLine and pqLine are already transformed
    [
        Line n (applySubst "HPQ -> (HP -> (H -> Q))" [("HP", hp), ("HPQ", hpq), ("H", hyp), ("Q", c)]) "Frege" [] Nothing,
        Line (n + 1) (applySubst "HP -> (H -> Q)" [("HP", hp), ("H", hyp), ("Q", c)]) "Modus Ponens" [lineNumber pqLine, n] Nothing,
        Line (n + 2) (applySubst "H -> Q" [("H", hyp), ("Q", c)]) "Modus Ponens" [lineNumber pLine, n + 1] (userNumber currLine)
    ]
    where 
        applySubst = getApplySubstFromTransformant transformant
        currLine = fromJust (curr transformant)
        n = lineNumber (currLine) + (offset transformant)
        [pLine, pqLine] = getCurrentRefLines transformant
        (hp, hpq, c) = (lineContent pLine, lineContent pqLine, lineContent currLine)

-- deduction should be the last transformation that happens
useDeduction' :: Sentence -> Transformant -> Transformant
useDeduction' hyp state =
    case (curr state) of
        Nothing -> state -- we've reached the end! 
        Just line -> case justification line of
            "Modus Ponens" -> useDeduction' hyp (applyTransformation (modusPonensCaseTransformation hyp) state)
            "Assumption" -> if lineContent line == hyp 
                                then useDeduction' hyp (applyTransformation hypCaseTransformation state) 
                                else useDeduction' hyp (applyTransformation (axiomCaseTransformation hyp) state)
            j -> if j `elem` (map axiomName (axioms (transformantLogic state)))
                        then useDeduction' hyp (applyTransformation (axiomCaseTransformation hyp) state)
                        else error ("unknown justification for deduction" ++ j)

useDeduction :: Logic -> Sentence -> [Line] -> [Line]
useDeduction logic hyp = 
    resetUserNumbers . reverse . transformata . (useDeduction' hyp) . (intoTransformant logic)


-- stuff below is for getting proofs from user input

getLineNumFromLine :: String -> String -> (Int, String)
getLineNumFromLine seen toSee = 
    case toSee of
        '.' : ' ' : '|' : '-' : ' ' : remChars -> (read seen, remChars)
        [] -> error "couldn't find line number split. Maybe you forgot to include \"|-\" in a line?"
        c : remChars -> getLineNumFromLine (seen ++ [c]) remChars

-- here is where automatic use of defined operators happens
getContentFromLine :: Logic -> String -> String -> (Sentence, String)
getContentFromLine logic seen toSee =
    case toSee of
        'b' : 'y' : ' ' : remChars -> (parse (operators logic) (definedOperators logic) seen, remChars)
        [] -> error "line wasn't justified!"
        c : remChars -> getContentFromLine logic (seen ++ [c]) remChars

-- meant to be applied after getting the content
getJustificationFromLine :: String -> String -> (String, [Int])
getJustificationFromLine seen toSee =
    case toSee of
        ':' : remChars -> case remChars of
                            [] -> (seen, [])
                            s -> (seen, map read (words s))
                                    -- [i, j] -> (seen, Just (read i, read j))
                                    -- _ -> error "theres stuff after justification but it's not just ints"
        [] -> (seen, []) -- axiom case (with no trailing comma)
        c : remChars -> getJustificationFromLine (seen ++ [c]) remChars

getLineFromUser :: Logic -> String -> Line
getLineFromUser logic userLine =
    let (lNum, rem1) = getLineNumFromLine "" userLine in
        let (content, rem2) = getContentFromLine logic "" rem1 in
            let (j, rfs) = getJustificationFromLine "" rem2 in
                Line lNum content j rfs (Just lNum)

getProofGoal :: Logic -> String -> String -> Sentence
getProofGoal _ _ [] = error "proof has no goal!"
getProofGoal logic _ ('|' : '-' : remChars) = parse (operators logic) (definedOperators logic) remChars
getProofGoal logic seen (c:remChars) = getProofGoal logic (seen ++ [c]) remChars

getDeductionsFunc :: Logic -> Sentence -> [String] -> [Line] -> [Line]
getDeductionsFunc _ _ [] = id
getDeductionsFunc logic goalModuloDeduction (fl : remPreamble)
    | "deduction" `isInfixOf` fl =
        case goalModuloDeduction of 
            OpNode op [lArg, rArg] -> 
                if op == cond 
                then (useDeduction logic lArg) . getDeductionsFunc logic rArg remPreamble 
                else error "ope should have conditional in goal to use deduction"
            _ -> error "ope should have conditional in goal to use deduction"
    | otherwise = getDeductionsFunc logic goalModuloDeduction remPreamble

splitByGoalLine :: [String] -> (String, [String])
splitByGoalLine [] = error "file has no lines!"
splitByGoalLine (l:tl) = (l, tl)

splitByProofLine :: [String] -> [String] -> ([String], [String])
splitByProofLine seen toSee =
    case toSee of
        [] -> error "you done fuked up"
        x : xs -> if isInfixOf "Proof" x 
            then (seen, xs) 
            else splitByProofLine (seen ++ [x]) xs

parseUserProof :: Logic -> [String] -> [Line]
parseUserProof _ [] = []
parseUserProof logic (fl : remFileLines)
    | (all isSpace fl) || "IGNORE" `isInfixOf` fl = parseUserProof logic remFileLines
    | otherwise = getLineFromUser logic fl : parseUserProof logic remFileLines

parseUserProofFile' :: Logic -> String -> (Sentence, ([Line] -> [Line]), [Line])
parseUserProofFile' logic fileContent =
    let (goalLine, pfLines') = splitByGoalLine (lines fileContent)
        goal = getProofGoal logic [] goalLine
        (preamble, pfLines) = splitByProofLine [] pfLines'
        deductionFunc = getDeductionsFunc logic goal preamble in
            (goal, deductionFunc, parseUserProof logic pfLines)


parseUserProofFile :: String -> String -> IO (Sentence, ([Line] -> [Line]), [Line])
parseUserProofFile logicName proofName = do
    fileContent <- readFile ("hand_proofs/" ++ logicName ++ "/" ++ proofName ++ ".txt")
    createDirectoryIfMissing False ("datalog/datalog_proofs/" ++ logicName ++ "/" ++ proofName)
    pure (parseUserProofFile' (getLogic logicName) fileContent)
