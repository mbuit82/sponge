module Abstractions where

import Core
import Parse.Sentences
import Parse.Proofs

import Defs.Rules
import Defs.Specs

import PruneProofTrees

import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map


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

-- CITING PROOFS
-- this is going to be redundant. 
applyIOTransformation :: (Transformant -> IO [Line]) -> Transformant -> IO (Transformant)
applyIOTransformation ioTransformation oldState = do
    applied <- reverse <$> (ioTransformation oldState)
    pure (Transformant (applied ++ transformata oldState) newCurr newTransformanda ((length applied) - 1 + offset oldState))
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

citedTheoremIOTransformation :: Logic -> Transformant -> IO [Line]
citedTheoremIOTransformation logic state = do
    let (logicName, proofName, varMap) = getCitedTheoremInfo logic (justification (fromJust (curr state))) in
        applyOffsetToInsertedTheorem (offset state + lineNumber (fromJust (curr state)) - 1) (userNumber (fromJust (curr state))) varMap (snd <$> (getHaskellProof logicName proofName))

applyCitedTheorems' :: Logic -> IO (Transformant) -> IO (Transformant)
applyCitedTheorems' logic pureState = 
    do
    state <- pureState
    case curr state of
        Nothing -> pureState
        Just line -> 
            if "citing" `isInfixOf` (justification line)
                then do 
                    applyCitedTheorems' logic (applyIOTransformation (citedTheoremIOTransformation logic) state)
                else do
                    applyCitedTheorems' logic (pure (applyTransformation identityTransformation state))

applyCitedTheorems :: Logic -> IO [Line] -> IO [Line]
applyCitedTheorems logic pureOldProof = do
    (resetUserNumbers . reverse. transformata) <$> (applyCitedTheorems' logic (intoTransformant <$> pureOldProof))



getHaskellProof :: String -> String -> IO (Sentence, [Line])
getHaskellProof logicName proofName = do
    (goal, deductionFunc, userLines) <- parseUserProofFile logicName proofName
    afterCitingTheorems <- applyCitedTheorems logic (pure userLines)
    pure (goal, (pruneProofTree . deductionFunc . applyDerivedRules logic derivedRules) afterCitingTheorems)
    where logic = getLogic logicName