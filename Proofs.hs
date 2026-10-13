module Proofs where

import Core
import Defs.Rules
import Defs.Specs

import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map
import System.Directory (createDirectoryIfMissing)
import qualified Data.Set as S


-- This is all general, not specific to the deduction lemma. I think this can be kept. 
-- when we run a transformation on a _proof state_, we want to return the result ++ old transformata, and then take the next element and make that the next current. 
applyTransformation :: Transformation -> Transformant -> Transformant
applyTransformation transformation oldState =
    Transformant (applied ++ transformata oldState) newCurr newTransformanda ((length applied) - 1 + offset oldState) (transformantLogic oldState)
    where 
        applied = reverse (transformation oldState)
        (newCurr, newTransformanda) = case transformanda oldState of
            [] -> (Nothing, [])
            nxt:remLines -> (Just nxt, remLines)

-- the first arg is supposed to be a proof
intoTransformant :: Logic -> [Line] -> Transformant
intoTransformant _ [] = error "can't transformation a proof with no steps!" -- not really sure what should happen here either
intoTransformant logic (fstLine:remLines) = Transformant [] (Just fstLine) remLines 0 logic 



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

resetUserNumbers :: [Line] -> [Line]
resetUserNumbers lns = map (\(Line n c j r _) -> Line n c j r (Just n)) lns

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
    pure (goal, (deductionFunc . applyDerivedRules logic derivedRules) afterCitingTheorems)
    where logic = getLogic logicName



-- OPTIMIZATION: PRUNING PROOF TREES

-- the implementation commented out is not great with memory while building (the recursive calls don't actually get called till the bottom, so lots of things are added to the stack), so am gonna use this Claude version instead
collectSentData :: (Map.Map Sentence a -> Line -> Map.Map Sentence a) -> [Line] -> Map.Map Sentence a
-- getSentCounts [] = Map.empty
-- getSentCounts (ln:lns) = Map.insertWith (+) (lineContent ln) 1 (getSentCounts lns)
collectSentData dataFunc = foldl' dataFunc Map.empty

collectRepeatedData :: (Map.Map Sentence a -> Line -> Map.Map Sentence a) -> (a -> Bool) -> [Line] -> Map.Map Sentence a
collectRepeatedData dataFunc filterFunc lns = Map.filter filterFunc (collectSentData dataFunc lns)

sentCountsFunc :: Map.Map Sentence Int -> Line -> Map.Map Sentence Int
sentCountsFunc m ln = Map.insertWith (+) (lineContent ln) 1 m

sentRefsFunc :: Map.Map Sentence [Int] -> Line -> Map.Map Sentence [Int]
sentRefsFunc m ln = Map.insertWith (++) (lineContent ln) [lineNumber ln] m

getRepeatedSents :: [Line] -> Map.Map Sentence Int
getRepeatedSents = collectRepeatedData sentCountsFunc (>1)

getRepeatedRefs :: [Line] -> Map.Map Sentence [Int]
getRepeatedRefs = collectRepeatedData sentRefsFunc (\xs -> length xs > 1)

verifyInOrder' :: Int -> [Line] -> Bool
verifyInOrder' _ [] = True
verifyInOrder' n (ln:lns) = if n == lineNumber ln then verifyInOrder' (n + 1) lns else False

verifyInOrder :: [Line] -> Bool
verifyInOrder = verifyInOrder' 1

getLineNumberDependencies' :: [Line] -> S.Set Int -> S.Set Int
getLineNumberDependencies' [] dependents = dependents
getLineNumberDependencies' (ln:lns) dependents = 
    if S.member (lineNumber ln) dependents
        then let newDependents = dependents `S.union` S.fromList (refLines ln) in
            getLineNumberDependencies' lns newDependents
        else getLineNumberDependencies' lns dependents

getLineNumberDependencies :: [Line] -> Int -> S.Set Int
getLineNumberDependencies lns rootRef = getLineNumberDependencies' (reverse lns) (S.singleton rootRef)

replaceRef :: (Int, S.Set Int) -> [Int] -> [Int]
replaceRef _ [] = []
replaceRef (newRef, toReplace) (rf:rfs) =
    (if rf `S.member` toReplace then newRef else rf) : replaceRef (newRef, toReplace) rfs

replaceInRefs' :: (Int, S.Set Int) -> [Line] -> [Line]
replaceInRefs' _ [] = []
replaceInRefs' repeatInfo (Line lNum c j rfs uNum : lns) =
    Line lNum c j (replaceRef repeatInfo rfs) uNum : replaceInRefs' repeatInfo lns

replaceInRefs :: S.Set Int -> [Line] -> [Line]
replaceInRefs repeateds = replaceInRefs' (S.deleteFindMin repeateds)

removeRepeatRefs :: [Line] -> [Line]
removeRepeatRefs lns =
    let repeatedsList = Map.elems (getRepeatedRefs lns) in
        let listOfFuncs = map (replaceInRefs. S.fromList) (repeatedsList) in
            foldl' (\acc f -> f acc) lns listOfFuncs

getUsedRefs :: [Line] -> S.Set Int
getUsedRefs lns = getLineNumberDependencies lns (lineNumber ((reverse lns) !! 0))
        
removeUnusedLines :: S.Set Int -> [Line] -> [Line]
removeUnusedLines usedRefs [] = []
removeUnusedLines usedRefs (ln : lns) =
    if not ((lineNumber ln) `S.member` usedRefs)
        then removeUnusedLines usedRefs lns
        else ln : (removeUnusedLines usedRefs lns)

-- ight now we gotta renumber the proofs. Transformations are overkill I think but have the machinery so
reNumberTransformation :: Transformation
reNumberTransformation transformant = 
    case curr transformant of
        Nothing -> []
        Just (Line lNum c j rfs uNum) -> 
            [Line (offset transformant + 1) c j (getUpdatedCurrentRefs transformant) uNum]

-- modified version of applyTransformation
reNumber'' :: Transformant -> Transformant
reNumber'' oldState =
    Transformant (applied ++ transformata oldState) newCurr newTransformanda (offset oldState + 1) (transformantLogic oldState)
    where 
        applied = reNumberTransformation oldState
        (newCurr, newTransformanda) = case transformanda oldState of
            [] -> (Nothing, [])
            nxt:remLines -> (Just nxt, remLines)

reNumber' :: Transformant -> Transformant
reNumber' state = 
    case curr state of
        Nothing -> state
        Just a -> reNumber' (reNumber'' state)

dummyLogic :: Logic
dummyLogic = Logic "" [] [] [] []

reNumber :: [Line] -> [Line]
reNumber = resetUserNumbers.reverse.transformata.reNumber'.(intoTransformant dummyLogic)

pruneProofTree :: [Line] -> [Line]
pruneProofTree lns =
    let noRepeatRefs = removeRepeatRefs lns in
        reNumber (removeUnusedLines (getUsedRefs noRepeatRefs) noRepeatRefs)
