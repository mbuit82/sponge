module Proofs where

import Core

import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map


-- This is all general, not specific to the deduction lemma. I think this can be kept. 

-- when we run a transformation on a _proof state_, we want to return the result ++ old transformata, and then take the next element and make that the next current. 
applyTransformation :: Transformation -> Transformant -> Transformant
applyTransformation transformation oldState =
    case curr oldState of
        Nothing -> error "can't apply transformation to when we have no current step!" -- we could just return oldState but that would be defective behavior so I'll leave it like this. not really sure what should happpen in this case
        Just currLine -> 
            case transformanda oldState of
                [] -> 
                    let applied = reverse (transformation oldState) in 
                        Transformant (applied ++ transformata oldState) Nothing [] ((length applied) - 1 + offset oldState)
                nxt : remLines -> 
                    let applied = reverse (transformation oldState) in
                        Transformant (applied ++ transformata oldState) (Just nxt) remLines ((length applied) - 1 + offset oldState)

-- the first arg is supposed to be a proof
intoTransformant :: [Line] -> Transformant
intoTransformant [] = error "can't transformation a proof with no steps!" -- not really sure what should happen here either
intoTransformant (fstLine:remLines) = Transformant [] (Just fstLine) remLines 0


applyOffsetInternal :: Int -> Line -> Line
applyOffsetInternal offset (Line n c justification rfs uNum) = 
    Line (n + offset) c justification (map (+ offset) rfs) uNum

applyOffsetInternalToLines :: Int -> [Line] -> [Line]
applyOffsetInternalToLines offset lns = map (applyOffsetInternal offset) lns

-- asdf = \x -> fromJust (findLineWithUserNum (transformata transformant) x)



-- EXAMPLE: Deduction lemma. 
-- I want this to be what a transformation looks like. 
axiomCaseTransformation :: Sentence -> Transformation
axiomCaseTransformation hyp transformant = 
    [   
        Line n (lineContent currLine) (justification currLine) [] Nothing,
        Line (n + 1) (OpNode cond [lineContent currLine, (OpNode cond [hyp, lineContent currLine])]) "Axiom2" [] Nothing,
        Line (n + 2) (OpNode cond [hyp, lineContent currLine]) "Modus Ponens" [n, n + 1] (userNumber currLine)
    ]
    where 
        currLine = fromJust (curr transformant)
        n = lineNumber (currLine) + (offset transformant)

hypCaseTransformation :: Transformation
hypCaseTransformation transformant = 
    [
        Line n (OpNode cond [OpNode cond [c, OpNode cond [c, c]], OpNode cond [OpNode cond [c, OpNode cond [OpNode cond [c, c], c]], OpNode cond [c, c]]]) "Axiom3" [] Nothing,
        Line (n + 1) (OpNode cond [c, OpNode cond [c, c]]) "Axiom2" [] Nothing,
        Line (n + 2) (OpNode cond [OpNode cond [c, OpNode cond [OpNode cond [c, c], c]], OpNode cond [c, c]]) "Modus Ponens" [n + 1, n] Nothing,
        Line (n + 3) (OpNode cond [c, OpNode cond [OpNode cond [c, c], c]]) "Axiom2" [] Nothing,
        Line (n + 4) (OpNode cond [c, c]) "Modus Ponens" [n + 3, n + 2] (userNumber currLine)
    ]
    where 
        currLine = fromJust (curr transformant)
        c = lineContent currLine
        n = lineNumber (currLine) + (offset transformant)

modusPonensCaseTransformation :: Sentence -> Transformation
modusPonensCaseTransformation hyp transformant = -- pLine and pqLine are already transformed
    let currLine = fromJust (curr transformant) in 
        let n = lineNumber (currLine) + (offset transformant) in 
            [
                Line n (OpNode cond [lineContent pLine, OpNode cond [lineContent pqLine, OpNode cond [hyp, lineContent currLine]]]) "Axiom3" [] Nothing,
                Line (n + 1) (OpNode cond [lineContent pqLine, OpNode cond [hyp, lineContent currLine]]) "Modus Ponens" [lineNumber pLine, n] Nothing,
                Line (n + 2) (OpNode cond [hyp, lineContent currLine]) "Modus Ponens" [lineNumber pqLine, n + 1] (userNumber currLine)
            ]
    where 
        [pLine, pqLine] = getCurrentRefLines transformant

-- deduction should be the last transformation that happens
useDeduction' :: Logic -> Sentence -> Transformant -> Transformant
useDeduction' logic hyp state =
    case (curr state) of
        Nothing -> state -- we've reached the end! 
        Just line -> case justification line of
            "Modus Ponens" -> useDeduction' logic hyp (applyTransformation (modusPonensCaseTransformation hyp) state)
            "Assumption" -> if lineContent line == hyp 
                                then useDeduction' logic hyp (applyTransformation hypCaseTransformation state) 
                                else useDeduction' logic hyp (applyTransformation (axiomCaseTransformation hyp) state)
            j -> if j `elem` (map axiomName (axioms logic))
                        then useDeduction' logic hyp (applyTransformation (axiomCaseTransformation hyp) state)
                        else error "unknown justification for deduction"

resetUserNumbers :: [Line] -> [Line]
resetUserNumbers lns = map (\(Line n c j r _) -> Line n c j r (Just n)) lns

useDeduction :: Logic -> Sentence -> [Line] -> [Line]
useDeduction logic hyp oldProof = 
    resetUserNumbers (reverse (transformata (useDeduction' logic hyp (intoTransformant oldProof))))

applyDerivedRules' :: Logic -> Transformant -> Transformant
applyDerivedRules' logic state =
    case (curr state) of
        Nothing -> state -- we've reached the end! 
        Just line -> case (derivedRules logic) Map.!? (justification line) of
            Nothing -> applyDerivedRules' logic (applyTransformation identityTransformation state)
            Just transformation -> applyDerivedRules' logic (applyTransformation transformation state)
    
applyDerivedRules :: Logic -> [Line] -> [Line]
applyDerivedRules logic oldProof = 
    resetUserNumbers (reverse (transformata (applyDerivedRules' logic (intoTransformant oldProof))))



-- stuff below is for getting proofs from user input
-- function to use after getting the goal
-- For now, use this one, but am thinking of having a general one where deduction is one of many last-transformations done
parseUserProofWithDeduction :: Logic -> Sentence -> [String] -> [Line]
parseUserProofWithDeduction _ _ [] = []
parseUserProofWithDeduction logic deductionRelativeGoal (fl : remFileLines)
    | "deduction" `isInfixOf` fl =
        case deductionRelativeGoal of
            OpNode op [lArg, rArg] -> 
                if op == cond 
                then useDeduction logic lArg (parseUserProofWithDeduction logic rArg remFileLines)
                else error "ope should have conditional in goal to use deduction"
            _ -> error "ope should have conditional in goal to use deduction"
    | (all isSpace fl) || fl == "Proof" = parseUserProofWithDeduction logic deductionRelativeGoal remFileLines -- ignore conditions
    | otherwise = getLineFromUser logic fl : parseUserProofWithDeduction logic deductionRelativeGoal remFileLines

parseUserProof :: Logic -> [String] -> [Line]
parseUserProof _ [] = []
parseUserProof logic (fl : remFileLines)
    | (all isSpace fl) || "IGNORE" `isInfixOf` fl = parseUserProof logic remFileLines
    | otherwise = getLineFromUser logic fl : parseUserProof logic remFileLines

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

parseUserProofFile :: Logic -> String -> (Sentence, [Line])
parseUserProofFile logic fileContent =
    let (goalLine, pfLines') = splitByGoalLine (lines fileContent)
        goal = getProofGoal logic [] goalLine
        (preamble, pfLines) = splitByProofLine [] pfLines'
        deductionFunc = getDeductionsFunc logic goal preamble in
            (goal, (deductionFunc . applyDerivedRules logic . parseUserProof logic) pfLines)