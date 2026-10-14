module SearchForProof where

import Core
import Defs.Specs

import Control.Monad
import Proofs
import System.Environment (getArgs)
import System.Directory 


doesProofMatchSearchSent :: String -> Sentence -> String -> IO (Bool)
doesProofMatchSearchSent searchLogicName searchSent proofName = do
    (tgtGoal, _) <- getHaskellProof searchLogicName proofName
    pure (haveSameStructure searchSent tgtGoal)

-- return a list of matching proof names
searchForProofInLogic :: Sentence -> String -> IO ([String])
searchForProofInLogic searchSent searchLogicName = do
    proofFileNames <- listDirectory ("hand_proofs/" ++ searchLogicName)
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
