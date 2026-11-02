module Commands.SearchForTheorem where

import Core
import Parse.Sentences
import Defs.Specs

import Control.Monad
import DerivedRules.UseDerivedRules
import System.Environment (getArgs)
import System.Directory 

getSubLogicsByAxioms :: String -> [String]
getSubLogicsByAxioms logicName =
    let logic = getLogic logicName in
        filter (\lName -> isSubLogicByAxioms (getLogic lName) logic) logicNames

doesTheoremMatchSearchSent :: String -> Sentence -> String -> IO (Bool)
doesTheoremMatchSearchSent searchLogicName searchSent proofName = do
    (tgtGoal, _) <- getHaskellProof searchLogicName proofName
    pure (haveSameStructure searchSent tgtGoal)

-- return a list of matching proof names
searchForTheoremInLogic :: Sentence -> String -> IO ([String])
searchForTheoremInLogic searchSent searchLogicName = do
    proofFileNames <- listDirectory ("user_proofs/" ++ searchLogicName)
    let proofNames = map (reverse .drop 4 .reverse) proofFileNames in
        filterM (doesTheoremMatchSearchSent searchLogicName searchSent) proofNames

searchForTheorem :: String -> String -> IO [String]
searchForTheorem parsingLogicName searchStr = do
    let parsingLogic = getLogic parsingLogicName in 
        let searchSent = parse (operators parsingLogic) (definedOperators parsingLogic) searchStr in
            concat <$> sequence (map (searchForTheoremInLogic searchSent) (getSubLogicsByAxioms parsingLogicName))

main :: IO ()
main = do
    [parsingLogicName, searchStr] <- getArgs
    searchResults <- searchForTheorem parsingLogicName searchStr
    putStrLn (show searchResults)
