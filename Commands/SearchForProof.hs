module Commands.SearchForProof where

import Core
import Parse.Sentences
import Defs.Specs

import Control.Monad
-- import Abstractions
import DerivedRules.UseDerivedRules
import System.Environment (getArgs)
import System.Directory 

getSubLogicsByAxioms :: String -> [String]
getSubLogicsByAxioms logicName =
    let logic = getLogic logicName in
        filter (\lName -> isSubLogicByAxioms (getLogic lName) logic) logicNames

doesProofMatchSearchSent :: String -> Sentence -> String -> IO (Bool)
doesProofMatchSearchSent searchLogicName searchSent proofName = do
    (tgtGoal, _) <- getHaskellProof searchLogicName proofName
    pure (haveSameStructure searchSent tgtGoal)

-- return a list of matching proof names
searchForProofInLogic :: Sentence -> String -> IO ([String])
searchForProofInLogic searchSent searchLogicName = do
    proofFileNames <- listDirectory ("user_proofs/" ++ searchLogicName)
    let proofNames = map (reverse .drop 4 .reverse) proofFileNames in
        filterM (doesProofMatchSearchSent searchLogicName searchSent) proofNames

searchForProof :: String -> String -> IO [String]
searchForProof parsingLogicName searchStr = do
    let parsingLogic = getLogic parsingLogicName in 
        let searchSent = parse (operators parsingLogic) (definedOperators parsingLogic) searchStr in
            concat <$> sequence (map (searchForProofInLogic searchSent) (getSubLogicsByAxioms parsingLogicName))

main :: IO ()
main = do
    [parsingLogicName, searchStr] <- getArgs
    searchResults <- searchForProof parsingLogicName searchStr
    putStrLn (show searchResults)
