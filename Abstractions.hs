module Abstractions where

import Core
import Parse.Sentences
import Parse.Proofs

import Defs.Operators
import Defs.Rules
import Defs.Specs

import PruneProofTrees

import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map

-- moving up top in case add more stuff at bottom
getHaskellProofWithoutDeduction :: String -> String -> IO (Sentence, [Sentence], [Line])
getHaskellProofWithoutDeduction logicName proofName = do
    (goal, deductionArgs, userLines) <- parseUserProofFile logicName proofName
    let logic = getLogic logicName
    let afterDerivedRules = applyDerivedRules logic derivedRules userLines -- this way, derived rules can use cited thms
    afterCitingTheorems <- useCitedTheorems logic afterDerivedRules
    pure (goal, deductionArgs, afterCitingTheorems) -- this is what we return for the FINAL pass, which is deduction (below)

getHaskellProof :: String -> String -> IO (Sentence, [Line])
getHaskellProof logicName proofName = do
    let logic = getLogic logicName
    (goal, deductionArgs, lns) <- getHaskellProofWithoutDeduction logicName proofName
    pure (goal, (pruneProofTree . (makeDeductionsFunc logic deductionArgs)) lns)

seeHaskellProof :: String -> String -> IO ()
seeHaskellProof logicName proofName = do
    (_, pf) <- getHaskellProof logicName proofName
    let relevantContents = map (\l -> (lineNumber l, lineContent l, justification l, refLines l)) pf in
        mapM_ print relevantContents



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
        applySubst = parseWithSubst [cond] []
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
        applySubst = parseWithSubst [cond] []
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
        applySubst = parseWithSubst [cond] []
        currLine = fromJust (curr transformant)
        n = lineNumber (currLine) + (offset transformant)
        [pLine, pqLine] = getCurrentRefLines transformant
        (hp, hpq, c) = (lineContent pLine, lineContent pqLine, lineContent currLine)

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
            j -> if j `elem` (map axiomName (axioms logic)) || j == "TEMP"
                        then useDeduction' logic hyp (applyTransformation (axiomCaseTransformation hyp) state)
                        else error ("unknown justification for deduction" ++ j)

useDeduction :: Logic -> Sentence -> [Line] -> [Line]
useDeduction logic hyp = 
    resetUserNumbers . reverse . transformata . (useDeduction' logic hyp) . intoTransformant

makeDeductionsFunc :: Logic -> [Sentence] -> [Line] -> [Line]
makeDeductionsFunc logic deductionAntecedents =
    foldl (.) id (map (useDeduction logic) deductionAntecedents)



-- machinery for applying derived rules
applyDerivedRules' :: Map.Map String Transformation -> Transformant -> Transformant
applyDerivedRules' derRulesDict state =
    case (curr state) of
        Nothing -> state -- we've reached the end! 
        Just line -> case derRulesDict Map.!? (justification line) of
            Nothing -> applyDerivedRules' derRulesDict (applyTransformation identityTransformation state)
            Just transformation -> applyDerivedRules' derRulesDict (applyTransformation transformation state)
    
applyDerivedRules :: Logic -> Map.Map String Transformation -> [Line] -> [Line]
applyDerivedRules logic derRulesDict = 
    resetUserNumbers . reverse . transformata . (applyDerivedRules' derRulesDict) . intoTransformant



-- APPLYING PROOFS
-- this is going to be redundant. 
applyIOTransformation :: (Transformant -> IO [Line]) -> Transformant -> IO (Transformant)
applyIOTransformation ioTransformation oldState = do
    applied <- reverse <$> (ioTransformation oldState)
    let addtlOff = length applied
    pure (Transformant (applied ++ transformata oldState) newCurr newTransformanda (addtlOff - 1 + offset oldState))
    where 
        (newCurr, newTransformanda) = case transformanda oldState of
            [] -> (Nothing, [])
            nxt:remLines -> (Just nxt, remLines)

applySubstToSent :: Map.Map String Sentence -> Sentence -> Sentence
applySubstToSent varMap (Atom a) = instantiateVar varMap a
applySubstToSent varMap (OpNode op args) = (OpNode op (map (applySubstToSent varMap) args))

-- this is meant for theorems that we have proved. To avoid two O(n) passes (do one instead), could also do substitutions as we go
-- replacingUNum is the uNum that we want the final line to have? Yes
-- this does two things: it instantiates vars and it applies an offset
applyOffsetAndSubstsToInsertedTheorem :: Int -> Map.Map String Sentence -> [Line] -> [Line]
applyOffsetAndSubstsToInsertedTheorem off varMap lines =
    case lines of 
        [] -> []
        ((Line lNum c j rfs uNum) : ls) ->
            (Line (lNum + off) (applySubstToSent varMap c) j (map (+ off) rfs) uNum) : (applyOffsetAndSubstsToInsertedTheorem off varMap ls)

-- this is the last thing that should happen
fixFinalUNum :: Maybe Int -> [Line] -> [Line]
fixFinalUNum _ [] = []
fixFinalUNum finalUNum [Line lNum c j rfs _] = [Line lNum c j rfs finalUNum]
fixFinalUNum finalUNum (Line lNum c j rfs _ : remLines) =
    Line lNum c j rfs Nothing : fixFinalUNum finalUNum remLines

makeCitedTheoremInstance :: Transformant -> Sentence
makeCitedTheoremInstance state = 
    makeChain cond refdContentList currContent
    where 
        currLine = fromJust (curr state)
        refdContentList = map lineContent (getCurrentRefLines state)
        currContent = lineContent currLine

getVarMapFromState :: Transformant -> Sentence -> Map.Map String Sentence
getVarMapFromState state schema =
    getVarMap (makeCitedTheoremInstance state) schema

stripBrackets :: String -> String
stripBrackets ('[':rest)
    | not (null rest) && last rest == ']' = init rest
stripBrackets subsStr = error ("somthing wrong w the user-inputted substitution: " ++ subsStr)

-- the string here is the justification
getTheoremInfo :: Logic -> String -> (String, String)
getTheoremInfo logic jus =
    let jus' = dropWhile (/= ' ') (dropWhile isSpace jus) in
        let ((proofName'), rest) = break (=='(') (dropWhile isSpace jus') in
            let (logicName, rest') = break (==')') (dropWhile isSpace (fromJust (stripPrefix "(from" rest))) in
                -- let subsStrWithBrackets = dropWhile isSpace (dropWhile (==')') rest') in
                    -- (logicName, dropWhileEnd isSpace proofName', getVarMapOLD logic (stripBrackets subsStrWithBrackets))
                    (logicName, dropWhileEnd isSpace proofName')

useCitedTheorems' :: Logic -> Transformant -> IO (Transformant)
useCitedTheorems' logic state = do
    case curr state of
        Nothing -> pure state
        Just line -> 
            if "applying" `isInfixOf` (justification line) || 
                "using" `isInfixOf` (justification line) || 
                "citing" `isInfixOf` (justification line)
                then do 
                    step <- applyIOTransformation (appliedTheoremIOTransformation logic) state -- CHANGED TO USE APPLYING
                    useCitedTheorems' logic step
                else 
                    useCitedTheorems' logic (applyTransformation identityTransformation state)

useCitedTheorems :: Logic -> [Line] -> IO [Line]
useCitedTheorems logic oldProof = do
    (resetUserNumbers . reverse. transformata) <$> (useCitedTheorems' logic (intoTransformant oldProof))

-- all the new stuff
-- helper for markTempLines
makeReplacementPairs :: (Map.Map Sentence Int) -> [Line] -> [(Int, Int)]
makeReplacementPairs pairs [] = []
makeReplacementPairs pairs (ln:lns) = 
    case Map.lookup (lineContent ln) pairs of
        Nothing -> makeReplacementPairs pairs lns
        Just a -> if justification ln == "Assumption" || justification ln == "TEMP"
                    then (lineNumber ln, a) : makeReplacementPairs pairs lns
                    else makeReplacementPairs pairs lns
                        -- error ("interesting case in a deduction to application thing: " ++ (show ln))

-- map keys are old refs, map values are new refs
-- this is a helper for intoAppStep
replaceNumsInList :: (Map.Map Int Int) -> [Int] -> [Int]
replaceNumsInList _ [] = []
replaceNumsInList replacementMap (x:xs) = 
        case Map.lookup x replacementMap of
            Just xNew -> xNew : replaceNumsInList replacementMap xs
            Nothing -> (x - Map.size replacementMap) : replaceNumsInList replacementMap xs

-- right now, this just marks the temp lines
markTempLinesRefs :: (Map.Map Int Int) -> Line -> Line
markTempLinesRefs replacementMap (Line lNum c j r uNum) =
    case Map.lookup lNum replacementMap of
        Nothing -> Line lNum c j r (Just lNum)
        Just a -> Line lNum c "TEMP" r (Just lNum)

markTempLines' :: (Map.Map Int Int) -> [Line] -> [Line]
markTempLines' replacementMap = map (markTempLinesRefs replacementMap)

markTempLines :: [(Sentence, Int)] -> [Line] -> [Line]
markTempLines pairs lines =
    markTempLines' (Map.fromList (makeReplacementPairs (Map.fromList pairs) lines)) lines

-- this will also renumber, since renumbering from pruneProofTrees depends on a transformant
removeTempLinesRefs :: (Map.Map Int Int) -> Int-> Line -> Maybe Line
removeTempLinesRefs replacementMap prevLineNumber (Line lNum c j r uNum) =
    case Map.lookup lNum replacementMap of
        Nothing -> Just (Line newNum c j (replaceNumsInList replacementMap r) (Just newNum))
        Just r -> Nothing
    where newNum = prevLineNumber + 1

removeTempLines' :: (Map.Map Int Int) -> Int -> [Line] -> [Line]
removeTempLines' replacementMap prevLineNumber [] = []
removeTempLines' replacementMap prevLineNumber (ln:lns) =
    case removeTempLinesRefs replacementMap prevLineNumber ln of
        Nothing -> removeTempLines' replacementMap prevLineNumber lns 
        Just a -> a : removeTempLines' replacementMap (lineNumber a) lns

-- also renumbers (since dependson removeTempLinesRefs)
removeTempLines :: [(Sentence, Int)] -> [Line] -> [Line]
removeTempLines pairs [] = error "why are you trying to remove temp lines from an empty proof"
removeTempLines pairs (ln:lns) =
    let lines = ln:lns in
        removeTempLines' 
            (Map.fromList (makeReplacementPairs (Map.fromList pairs) lines))
            (lineNumber ln - 1)
            lines

-- [Sentence] are the deductionArgs, [Int] are the references supplied in the line
getSentIntPairs :: [Sentence] -> [Int] -> ([(Sentence, Int)], Either [Sentence] [Int])
getSentIntPairs [] refs = ([], Right refs)
getSentIntPairs deductionArgs [] = ([], Left deductionArgs)
getSentIntPairs (dArg:remArgs) (newRef:remRefs) =
    let (remPairs, leftovers) = getSentIntPairs remArgs remRefs in
        ((dArg, newRef) : remPairs, leftovers)

applySubstToLine :: Map.Map String Sentence -> Line -> Line
applySubstToLine varMap (Line lNum c j r uNum) =
    Line lNum (applySubstToSent varMap c) j r uNum

makeModusPonensLine :: Int -> Line -> Line
makeModusPonensLine ref (Line lNum (OpNode binOp [ant, consq]) j r uNum)
    | binOp == cond = Line (lNum+1) consq "Modus Ponens" [ref, lNum] Nothing
    | otherwise = error "can't make modus ponens line from smth that's not conditional (makeModusPonensLine)"

makeModusPonensLines' :: [Int] -> Line -> [Line]
makeModusPonensLines' [] _ = []
makeModusPonensLines' (x:xs) ln =
    let mpLineMade = makeModusPonensLine x ln in
        mpLineMade : makeModusPonensLines' xs mpLineMade

makeModusPonensLines :: [Int] -> [Line] -> [Line]
makeModusPonensLines refs = (makeModusPonensLines' refs) . last

addAppStuff :: Logic -> (Either [Sentence] [Int]) -> [Line] -> [Line]
addAppStuff logic leftovers lns = 
    case leftovers of
        Left deductionArgs -> (makeDeductionsFunc logic deductionArgs) lns 
        Right refs -> lns ++ makeModusPonensLines refs lns

appliedTheoremIOTransformation :: Logic -> Transformant -> IO [Line]
appliedTheoremIOTransformation logic state = do
    let currLine = fromJust (curr state) -- get the current state
    let (logicName, proofName) = getTheoremInfo logic (justification currLine) -- parse the justification
    (thmGoal, deductionArgs, userLines) <- getHaskellProofWithoutDeduction logicName proofName -- unfold everything but deduction in the cited proof
    let varMap = getVarMapFromState state thmGoal -- make the varMap from the current and cited lines and cited thm goal

    let offsetToApply = (offset state + lineNumber currLine - 1) -- copied from citedTheoremIOTransformation (deprecated)
    let userLinesSubstd = applyOffsetAndSubstsToInsertedTheorem offsetToApply varMap userLines

    -- now we start the process of getting rid of the deduction stuff
    let deductionArgsSubstd = map (applySubstToSent varMap) deductionArgs
    let appRfs = getUpdatedCurrentRefs state
    let (pairs, leftovers) = getSentIntPairs deductionArgsSubstd appRfs

    let tempLinesMarked = markTempLines pairs userLinesSubstd

    let postApp = addAppStuff logic leftovers tempLinesMarked

    let noTempLines = removeTempLines pairs postApp -- also renumbers

    let afterEverything = fixFinalUNum (userNumber currLine) noTempLines

    pure afterEverything