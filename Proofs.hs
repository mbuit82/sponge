module Proofs where

import Core

import Data.Maybe
import Data.List
import Data.Char


-- This is all general, not specific to the deduction lemma. I think this can be kept. 
data Transformant = Transformant { transformata :: [Line], curr :: Maybe Line, transformanda :: [Line], offset :: Int}

type Transformation = Int -> Line -> [Line]

-- when we run a transformation on a _proof state_, we want to return the result ++ old transformata, and then take the next element and make that the next current. 
applyTransformation :: Transformation -> Transformant -> Transformant
applyTransformation transformation oldState =
    case curr oldState of
        Nothing -> error "can't apply transformation to when we have no current step!" -- we could just return oldState but that would be defective behavior so I'll leave it like this. not really sure what should happpen in this case
        Just currLine -> 
            case transformanda oldState of
                [] -> 
                    let applied = reverse (transformation (offset oldState) currLine) in 
                        Transformant (applied ++ transformata oldState) Nothing [] ((length applied) - 1 + offset oldState)
                nxt : tail -> 
                    let applied = reverse (transformation (offset oldState) currLine) in
                        Transformant (applied ++ transformata oldState) (Just nxt) tail ((length applied) - 1 + offset oldState)

-- the first arg is supposed to be a proof
intoTransformant :: [Line] -> Transformant
intoTransformant [] = error "can't transformation a proof with no steps!" -- not really sure what should happen here either
intoTransformant (fstLine:tail) = Transformant [] (Just fstLine) tail 0

applyOffset :: Int -> Line -> Line
applyOffset offset (Line n c justification rfs uNum) = 
    case rfs of
        Nothing -> Line (n + offset) c justification rfs uNum
        Just (i, j) -> Line (n + offset) c justification (Just (i + offset, j + offset)) uNum

applyOffsetToLines :: Int -> [Line] -> [Line]
applyOffsetToLines offset lines = map (applyOffset offset) lines





-- EXAMPLE: Deduction lemma. 
-- I want this to be what a transformation looks like. 
axiomCaseDeduction :: Sentence -> Line -> [Line]
axiomCaseDeduction hyp (Line lNum c justification rfs uNum) = 
    [   
        Line lNum c justification rfs Nothing,
        Line (lNum + 1) (OpNode cond [c, (OpNode cond [hyp, c])]) "Axiom2" Nothing Nothing,
        Line (lNum + 2) (OpNode cond [hyp, c]) "Modus Ponens" (Just (lNum, lNum + 1)) uNum
    ]

hypCaseDeduction :: Line -> [Line]
hypCaseDeduction (Line n c justification rfs uNum) = 
    [
        Line n (OpNode cond [OpNode cond [c, OpNode cond [c, c]], OpNode cond [OpNode cond [c, OpNode cond [OpNode cond [c, c], c]], OpNode cond [c, c]]]) "Axiom3" Nothing Nothing,
        Line (n + 1) (OpNode cond [c, OpNode cond [c, c]]) "Axiom2" Nothing Nothing,
        Line (n + 2) (OpNode cond [OpNode cond [c, OpNode cond [OpNode cond [c, c], c]], OpNode cond [c, c]]) "Modus Ponens" (Just (n + 1, n)) Nothing,
        Line (n + 3) (OpNode cond [c, OpNode cond [OpNode cond [c, c], c]]) "Axiom2" Nothing Nothing,
        Line (n + 4) (OpNode cond [c, c]) "Modus Ponens" (Just (n + 3, n + 2)) uNum
    ]
    -- [Line lNum (OpNode cond [c, c]) "Axiom1" Nothing uNum]

findLineWithUserNum :: [Line] -> Int -> Maybe Line
findLineWithUserNum lines uNum =
    case lines of
        [] -> Nothing
        l : tail -> case userNumber l of
                        Just luNum -> if luNum == uNum then (Just l) else findLineWithUserNum tail uNum
                        _ -> findLineWithUserNum tail uNum

axiomCaseTransformation :: Sentence -> Transformation
axiomCaseTransformation hyp offset line = applyOffsetToLines offset (axiomCaseDeduction hyp line)

hypCaseTransformation :: Transformation
hypCaseTransformation offset line = applyOffsetToLines offset (hypCaseDeduction line)

modusPonensCaseTransformation :: Sentence -> Line -> Line -> Transformation
modusPonensCaseTransformation hyp pLine pqLine offset currLine = -- pLine and pqLine are already transformed
    let n = lineNumber currLine + offset in 
        [
            Line n (OpNode cond [lineContent pLine, OpNode cond [lineContent pqLine, OpNode cond [hyp, lineContent currLine]]]) "Axiom3" Nothing Nothing,
            Line (n + 1) (OpNode cond [lineContent pqLine, OpNode cond [hyp, lineContent currLine]]) "Modus Ponens" (Just (lineNumber pLine, n)) Nothing,
            Line (n + 2) (OpNode cond [hyp, lineContent currLine]) "Modus Ponens" (Just (lineNumber pqLine, n + 1)) (userNumber currLine)
        ]

-- deduction should be the last transformation that happens
useDeduction' :: Logic -> Sentence -> Transformant -> Transformant
useDeduction' logic hyp state =
    case (curr state) of
        Nothing -> state -- we've reached the end! 
        Just line -> case justification line of
                        "Modus Ponens" -> useDeduction' logic hyp (applyTransformation (modusPonensCaseTransformation hyp pLine pqLine) state)
                                            where 
                                                pLine = fromJust (findLineWithUserNum (transformata state) (fst (fromJust (refLines line))))
                                                pqLine = fromJust (findLineWithUserNum (transformata state) (snd (fromJust (refLines line))))
                        "Assumption" -> if lineContent line == hyp 
                                            then useDeduction' logic hyp (applyTransformation hypCaseTransformation state) 
                                            else useDeduction' logic hyp (applyTransformation (axiomCaseTransformation hyp) state)
                        just -> if just `elem` (map axiomName (axioms logic))
                                    then useDeduction' logic hyp (applyTransformation (axiomCaseTransformation hyp) state)
                                    else error "unknown justification for deduction"

resetUserNumbers :: [Line] -> [Line]
resetUserNumbers lines = map (\(Line n c j r _) -> Line n c j r (Just n)) lines

useDeduction :: Logic -> Sentence -> [Line] -> [Line]
useDeduction logic hyp oldProof = 
    resetUserNumbers (reverse (transformata (useDeduction' logic hyp (intoTransformant oldProof))))



-- stuff below is for getting proofs from user input
-- function to use after getting the goal
-- For now, use this one, but am thinking of having a general one where deduction is one of many last-transformations done
parseUserProofWithDeduction :: Logic -> Sentence -> [String] -> [Line]
parseUserProofWithDeduction logic deductionRelativeGoal [] = []
parseUserProofWithDeduction logic deductionRelativeGoal (fl : rem)
    | isInfixOf "deduction" fl =
        case deductionRelativeGoal of
            OpNode cond [lArg, rArg] -> useDeduction logic lArg (parseUserProofWithDeduction logic rArg rem)
            _ -> error "ope should have implication in goal to use deduction"
    | (all isSpace fl) || fl == "Proof" = parseUserProofWithDeduction logic deductionRelativeGoal rem -- ignore conditions
    | otherwise = getLineFromUser (operators logic) fl : parseUserProofWithDeduction logic deductionRelativeGoal rem

splitByProofLine :: [String] -> (String, [String])
splitByProofLine [] = error "file has no lines!"
splitByProofLine (l:tl) = (l, tl)

parseUserProofFile :: Logic -> String -> (Sentence, [Line])
parseUserProofFile logic fileContent =
    let (goalLine, pfLines) = splitByProofLine (lines fileContent) in
        let goal = getProofGoal (operators logic) [] goalLine in
            (goal, parseUserProofWithDeduction logic goal pfLines)