module ToDatalog.PruneProofTrees where

import Core

import qualified Data.Map as Map
import qualified Data.Set as Set

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

-- idea is you go backwards through proof
getSubProofRefs' :: [Line] -> Set.Set Int -> Set.Set Int
getSubProofRefs' [] dependents = dependents
getSubProofRefs' (ln:lns) dependents = 
    if Set.member (lineNumber ln) dependents
        then let newDependents = dependents `Set.union` Set.fromList (refLines ln) in
            getSubProofRefs' lns newDependents
        else getSubProofRefs' lns dependents

getSubProofRefs :: [Line] -> Int -> Set.Set Int
getSubProofRefs lns rootRef = getSubProofRefs' (reverse lns) (Set.singleton rootRef)

replaceRef :: (Int, Set.Set Int) -> [Int] -> [Int]
replaceRef _ [] = []
replaceRef (newRef, toReplace) (rf:rfs) =
    (if rf `Set.member` toReplace then newRef else rf) : replaceRef (newRef, toReplace) rfs

replaceInRefs' :: (Int, Set.Set Int) -> [Line] -> [Line]
replaceInRefs' _ [] = []
replaceInRefs' repeatInfo (Line lNum c j rfs uNum : lns) =
    Line lNum c j (replaceRef repeatInfo rfs) uNum : replaceInRefs' repeatInfo lns

step :: (Int, Int) -> (Int, Int) -> (Int, Int)
step (0,0) kv = kv
step currSmallest kv
    | snd kv < snd currSmallest = kv
    | snd kv == snd currSmallest = if fst kv < fst currSmallest then kv else currSmallest
    | otherwise = currSmallest

pickLineFunc :: Set.Set Int -> [Line] -> (Int, Set.Set Int)
-- pickLineFunc sameContentRefs lns = Set.deleteFindMin sameContentRefs
-- below is the naive, keep-smallest-subproof approach
pickLineFunc sameContentRefs lns = 
    let asList = Set.toList sameContentRefs in
        let sizeProofTrees = map (\int -> (int, Set.size (getSubProofRefs lns int))) asList in
            let keepRef = fst (foldl' step (0,0) sizeProofTrees) in 
                (keepRef, Set.delete keepRef sameContentRefs)

replaceInRefs :: Set.Set Int -> [Line] -> [Line]
replaceInRefs repeateds lns = replaceInRefs' (pickLineFunc repeateds lns) lns

removeRepeatRefs :: [Line] -> [Line]
removeRepeatRefs lns =
    let repeatedsList = Map.elems (getRepeatedRefs lns) in
        let listOfFuncs = map (replaceInRefs. Set.fromList) (repeatedsList) in
            foldl' (\acc f -> f acc) lns listOfFuncs

getUsedRefs :: [Line] -> Set.Set Int
getUsedRefs lns = getSubProofRefs lns (lineNumber ((reverse lns) !! 0))
        
removeUnusedLines :: Set.Set Int -> [Line] -> [Line]
removeUnusedLines usedRefs [] = []
removeUnusedLines usedRefs (ln : lns) =
    if not ((lineNumber ln) `Set.member` usedRefs)
        then removeUnusedLines usedRefs lns
        else ln : (removeUnusedLines usedRefs lns)

data Zipper = Zipper {  seen :: [Line], 
                        curr :: Maybe Line, 
                        toSee :: [Line] 
                        } deriving Show

intoZipper :: [Line] -> Zipper
intoZipper [] = error "sadfadfdsfdsffdsafds"
intoZipper (ln:rem) = Zipper [] (Just ln) rem

-- finds the first occurrence. This is taken advantage of in the strengthening derived rule
findLineWithUserNum :: [Line] -> Int -> Maybe Line
findLineWithUserNum [] _ = Nothing
findLineWithUserNum (l : remLines) uNum =
    case userNumber l of
        Just luNum -> if luNum == uNum then (Just l) else findLineWithUserNum remLines uNum
        _ -> findLineWithUserNum remLines uNum

getCurrentRefLine :: Zipper -> Int -> Line
getCurrentRefLine zipper r =
    case findLineWithUserNum (seen zipper) r of
        Nothing -> error ("ope couldn't find refline " ++ show r ++ " in lines " ++ show (seen zipper))
        Just ln -> ln

getCurrentRefLines :: Zipper -> Line -> [Line]
getCurrentRefLines zipper currLine =
    map (getCurrentRefLine zipper) (refLines currLine)

getUpdatedCurrentRefs :: Zipper -> Line -> [Int]
getUpdatedCurrentRefs zipper currLine = map lineNumber (getCurrentRefLines zipper currLine)

renumberLine :: Zipper -> Int -> Line -> Line
renumberLine zipper n currLine =
    Line 
        n 
        (lineContent currLine) 
        (justification currLine) 
        (getUpdatedCurrentRefs zipper currLine) 
        (userNumber currLine)

stepZipper :: (Line -> Line) -> Zipper -> Zipper 
stepZipper _ (Zipper sn Nothing ts) = error "nothing to step"
stepZipper f (Zipper sn (Just ln) []) = Zipper ((f ln):sn) Nothing []
stepZipper f (Zipper sn (Just ln) (nxt:nxts)) = Zipper ((f ln):sn) (Just nxt) nxts

renumber' :: Int -> Zipper -> Zipper
renumber' n zipper =
    case curr zipper of
        Nothing -> zipper
        Just ln -> renumber' (n+1) (stepZipper (renumberLine zipper n) zipper)

renumber :: [Line] -> [Line]
renumber = reverse.seen.(renumber' 1).intoZipper

resetUserNumbers :: [Line] -> [Line]
resetUserNumbers lns = map (\(Line n c j r _) -> Line n c j r (Just n)) lns

pruneProofTree :: [Line] -> [Line]
pruneProofTree lns =
    let noRepeatRefs = removeRepeatRefs lns in
        renumber (resetUserNumbers (removeUnusedLines (getUsedRefs noRepeatRefs) noRepeatRefs))

-- for seeing how unbalanced a proof tree is
getSubProofRoots :: [Line] -> Int -> Maybe [Int]
getSubProofRoots [] rootRef = Nothing
getSubProofRoots (ln:lns) rootRef
    | lineNumber ln == rootRef = Just (refLines ln)
    | otherwise = getSubProofRoots lns rootRef

getSubProofSizes :: [Line] -> Int -> [Int]
getSubProofSizes lns rootRef = 
    case getSubProofRoots lns rootRef of
        Nothing -> error "line not in proof"
        Just roots -> map (Set.size . getSubProofRefs lns) roots

getSubProofsWithSizes :: [Line] -> Int -> Map.Map Int Int
getSubProofsWithSizes lns rootRef = 
    case getSubProofRoots lns rootRef of
        Nothing -> error "line not in proof"
        Just roots -> Map.fromList (zip roots (map (Set.size . getSubProofRefs lns) roots))

getSubProofHeight :: [Line] -> Int -> Int
getSubProofHeight lns rootRef =
    case getSubProofRoots lns rootRef of
        Nothing -> error "line not in proof"
        Just [] -> 1
        Just roots -> 1 + maximum (map (getSubProofHeight lns) roots)