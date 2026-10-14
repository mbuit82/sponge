module Proofs where

import Core
import Defs.Rules
import Defs.Specs
import PruneProofTrees

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
    -- resetUserNumbers (reverse (transformata (useDeduction' hyp (intoTransformant logic oldProof))))

applyDerivedRules' :: Map.Map String Transformation -> Transformant -> Transformant
applyDerivedRules' derRulesDict state =
    case (curr state) of
        Nothing -> state -- we've reached the end! 
        Just line -> case derRulesDict Map.!? (justification line) of
            Nothing -> applyDerivedRules' derRulesDict (applyTransformation identityTransformation state)
            Just transformation -> applyDerivedRules' derRulesDict (applyTransformation transformation state)
    
applyDerivedRules :: Logic -> Map.Map String Transformation -> [Line] -> [Line]
applyDerivedRules logic derRulesDict = 
    resetUserNumbers . reverse . transformata . (applyDerivedRules' derRulesDict) . (intoTransformant logic)
    -- resetUserNumbers (reverse (transformata (applyDerivedRules' derRulesDict (intoTransformant logic oldProof))))





-- CITING PROOFS
-- this is going to be redundant. 
applyIOTransformation :: (Transformant -> IO [Line]) -> Transformant -> IO (Transformant)
applyIOTransformation ioTransformation oldState = do
    applied <- reverse <$> (ioTransformation oldState)
    pure (Transformant (applied ++ transformata oldState) newCurr newTransformanda ((length applied) - 1 + offset oldState) (transformantLogic oldState))
    where 
        (newCurr, newTransformanda) = case transformanda oldState of
            [] -> (Nothing, [])
            nxt:remLines -> (Just nxt, remLines)

applySubstToSent :: Map.Map String Sentence -> Sentence -> Sentence
applySubstToSent varMap (Atom a) = instantiateVar varMap a
applySubstToSent varMap (OpNode op args) = (OpNode op (map (applySubstToSent varMap) args))

-- this is meant for theorems that we have proved. To avoid two O(n) passes (do one instead), could also do substitutions as we go
applyOffsetToInsertedTheorem :: Int -> Maybe Int -> Map.Map String Sentence -> IO [Line] -> IO [Line]
applyOffsetToInsertedTheorem offset replacingUNum varMap ioLines = do 
    lines <- ioLines
    case lines of 
        [] -> pure []
        [Line lNum c j rfs _] -> 
            pure [Line (lNum + offset) (applySubstToSent varMap c) j (map (+ offset) rfs) replacingUNum]
        ((Line lNum c j rfs _) : ls) ->
            ((Line (lNum + offset) (applySubstToSent varMap c) j (map (+ offset) rfs) Nothing) :) <$> (applyOffsetToInsertedTheorem offset replacingUNum varMap (pure ls))

splitOn' :: Char -> String -> [String]
splitOn' c s = case break (== c) s of
    (a, []) -> [a]
    (a, _ : rest) -> a : splitOn' c rest

-- technically inefficient w the isInfixOf since every substPair is checked, but gives more flexibility
getSplitFunc :: Logic -> String -> (String, Sentence)
getSplitFunc logic substPair = 
    let parseFunc = parse (operators logic) (definedOperators logic) in
        if isInfixOf "/" substPair 
            then ((\[newSent, atomStr] -> (atomStr, parseFunc newSent)) . splitOn' '/') substPair 
            else ((\[atomStr, newSent] -> (atomStr, parseFunc newSent)) . splitOn' '\\') substPair

getVarMap :: Logic -> String -> Map.Map String Sentence
getVarMap logic = Map.fromList . map (getSplitFunc logic) . splitOn' ','

stripBrackets :: String -> String
stripBrackets ('[':rest)
    | not (null rest) && last rest == ']' = init rest
stripBrackets subsStr = error ("somthing wrong w the user-inputted substitution: " ++ subsStr)

getCitedTheoremInfo :: Logic -> String -> (String, String, Map.Map String Sentence)
getCitedTheoremInfo logic jus =
    let jus' = stripPrefix "citing" (dropWhile isSpace jus) in
        let ((proofName'), rest) = break (=='(') (dropWhile isSpace (fromJust jus')) in
            let (logicName, rest') = break (==')') (dropWhile isSpace (fromJust (stripPrefix "(from" rest))) in
                let subsStrWithBrackets = dropWhile isSpace (dropWhile (==')') rest') in
                    (logicName, dropWhileEnd isSpace proofName', getVarMap logic (stripBrackets subsStrWithBrackets))

citedTheoremIOTransformation :: Transformant -> IO [Line]
citedTheoremIOTransformation state = do
    let (logicName, proofName, varMap) = getCitedTheoremInfo (transformantLogic state) (justification (fromJust (curr state))) in
        applyOffsetToInsertedTheorem (offset state + lineNumber (fromJust (curr state)) - 1) (userNumber (fromJust (curr state))) varMap (snd <$> (getHaskellProof logicName proofName))

applyCitedTheorems' :: IO (Transformant) -> IO (Transformant)
applyCitedTheorems' pureState = 
    do
    state <- pureState
    case curr state of
        Nothing -> pureState
        Just line -> 
            if "citing" `isInfixOf` (justification line)
                then do 
                    applyCitedTheorems' (applyIOTransformation citedTheoremIOTransformation state)
                else do
                    applyCitedTheorems' (pure (applyTransformation identityTransformation state))

applyCitedTheorems :: Logic -> IO [Line] -> IO [Line]
applyCitedTheorems logic pureOldProof = do
    (resetUserNumbers . reverse. transformata) <$> (applyCitedTheorems' ((intoTransformant logic) <$> pureOldProof))



-- stuff below is for getting proofs from user input
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
    createDirectoryIfMissing False ("datalog_proofs/" ++ logicName ++ "/" ++ proofName)
    pure (parseUserProofFile' (getLogic logicName) fileContent)

getHaskellProof :: String -> String -> IO (Sentence, [Line])
getHaskellProof logicName proofName = do
    (goal, deductionFunc, userLines) <- parseUserProofFile logicName proofName
    afterCitingTheorems <- applyCitedTheorems logic (pure userLines)
    pure (goal, (pruneProofTree . deductionFunc . applyDerivedRules logic derivedRules) afterCitingTheorems)
    where logic = getLogic logicName

-- I have a feeling this isn't the best definition; I don't think it's the moral one
isSubLogicByAxioms :: Logic -> Logic -> Bool
isSubLogicByAxioms logic1 logic2 =
    and (map (\op -> elem op (operators logic2)) (operators logic1)) &&
    and (map (\rl -> elem rl (inferenceRules logic2)) (inferenceRules logic1)) &&
    and (map (\ax -> elem ax (axioms logic2)) (axioms logic1))

getSubLogicsByAxioms :: String -> [String]
getSubLogicsByAxioms logicName =
    let logic = getLogic logicName in
        filter (\lName -> isSubLogicByAxioms (getLogic lName) logic) logicNames
