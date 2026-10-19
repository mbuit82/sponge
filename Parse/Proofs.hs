module Parse.Proofs where

import Core
import Parse.Sentences

import Defs.Specs

import Data.List
import Data.Char
import qualified Data.Map as Map
import System.Directory 



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

getDeductionArgs :: Sentence -> [String] -> [Sentence]
getDeductionArgs _ [] = []
getDeductionArgs goalModuloDeduction (fl : remPreamble)
    | "IGNORE" `isInfixOf` fl = getDeductionArgs goalModuloDeduction remPreamble
    | "deduction" `isInfixOf` fl =
        case goalModuloDeduction of 
            OpNode op [lArg, rArg] -> 
                if op == cond 
                then lArg : (getDeductionArgs rArg remPreamble)
                else error "ope should have conditional in goal to use deduction"
            _ -> error "ope should have conditional in goal to use deduction"
    | otherwise = getDeductionArgs goalModuloDeduction remPreamble

splitByGoalLine :: [String] -> (String, [String])
splitByGoalLine [] = error "file has no lines!"
splitByGoalLine (l:tl) = (l, tl)

splitByProofLine :: [String] -> [String] -> ([String], [String])
splitByProofLine seen toSee =
    case toSee of
        [] -> error "you done fuked up. Maybe you forgot the \"Proof\" header?"
        x : xs -> if isInfixOf "Proof" x 
            then (seen, xs) 
            else splitByProofLine (seen ++ [x]) xs

parseUserProof :: Logic -> [String] -> [Line]
parseUserProof _ [] = []
parseUserProof logic (fl : remFileLines)
    | (all isSpace fl) || "IGNORE" `isInfixOf` fl = parseUserProof logic remFileLines
    | otherwise = getLineFromUser logic fl : parseUserProof logic remFileLines

parseUserProofFile' :: Logic -> String -> (Sentence, [Sentence], [Line])
parseUserProofFile' logic fileContent =
    let (goalLine, pfLines') = splitByGoalLine (lines fileContent)
        goal = getProofGoal logic [] goalLine
        (preamble, pfLines) = splitByProofLine [] pfLines'
        deductionArgs = getDeductionArgs goal preamble in
            (goal, deductionArgs, parseUserProof logic pfLines)


parseUserProofFile :: String -> String -> IO (Sentence, [Sentence], [Line])
parseUserProofFile logicName proofName = do
    fileContent <- readFile ("hand_proofs/" ++ logicName ++ "/" ++ proofName ++ ".txt")
    createDirectoryIfMissing False ("datalog/datalog_proofs/" ++ logicName ++ "/" ++ proofName)
    pure (parseUserProofFile' (getLogic logicName) fileContent)
