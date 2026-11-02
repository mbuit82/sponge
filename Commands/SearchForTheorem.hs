{-# LANGUAGE Strict #-}

module Commands.SearchForTheorem where

import Core
import Parse.Sentences
import Defs.Specs
import ToDatalog.Utils 

import Control.Monad
import DerivedRules.UseDerivedRules
import System.Environment (getArgs)
import System.Directory 

getSubLogicsByAxioms :: Logic -> [String]
getSubLogicsByAxioms logic =
    filter (\lName -> isSubLogicByAxioms (getLogic lName) logic) logicNames

doesTheoremMatchSearchSent :: String -> Sentence -> String -> IO (Bool)
doesTheoremMatchSearchSent searchLogicName searchSent proofName = do
    (tgtGoal, _) <- getHaskellProof searchLogicName proofName
    pure (haveSameStructure searchSent tgtGoal)

-- return a list of matching proof names
searchForTheoremInLogic :: Sentence -> String -> IO ([(String, String)])
searchForTheoremInLogic searchSent searchLogicName = do
    proofFileNames' <- listDirectory ("user_proofs/" ++ searchLogicName)
    let proofFileNames = filter isTxtFileName proofFileNames'
    let proofNames = map (\str -> (removeTxt str, searchLogicName)) proofFileNames
    filterM (\p -> doesTheoremMatchSearchSent searchLogicName searchSent (fst p)) proofNames

searchForTheorem :: Logic -> String -> IO [(String, String)]
searchForTheorem parsingLogic searchStr = do
    let searchSent = parse (operators parsingLogic) (definedOperators parsingLogic) searchStr
    let subLogics = getSubLogicsByAxioms parsingLogic
    concat <$> mapM (searchForTheoremInLogic searchSent) subLogics

main :: IO ()
main = do
    putStrLn "Welcome to theorem search."
    putStrLn "Type quit-search and press enter to exit theorem search."
    putStrLn "What logic do you want to check theorems for?"
    parsingLogicName <- getLine
    let parsingLogic = getLogic parsingLogicName -- need strict evaluation for this! rn fix is making this module strict
    putStrLn "What theorem are you looking for? "
    searchStr <- getLine
    searchResults <- searchForTheorem parsingLogic searchStr
    putStrLn (show searchResults)
