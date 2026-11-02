module ToDatalog.Utils where

import Core
import Defs.Specs
import ToDatalog.PruneProofTrees
import DerivedRules.UseDerivedRules

import System.IO
import Data.List
import System.Environment (getArgs)
import System.Directory


formulaToDatalog :: Bool -> Sentence -> String
formulaToDatalog True (Atom name) = name
formulaToDatalog False (Atom name) = "$Atom(\"" ++ name ++ "\")"
formulaToDatalog schemaBool (OpNode op args) = 
    "$" ++ (operatorName op) ++ "(" ++ argsStr ++ ")"
        where argsStr = intercalate ", " (map (formulaToDatalog schemaBool) args)


isTxtFileName :: String -> Bool
isTxtFileName fileName =
    drop (length fileName - 4) fileName == ".txt"

removeTxt :: String -> String
removeTxt fileName =
    take (length fileName - 4) fileName

overLogic :: String -> (String -> String -> IO ()) -> IO ()
overLogic logicName func = do 
    files <- listDirectory ("user_proofs/" ++ logicName ++ "/")
    let proofFiles = filter isTxtFileName files
    let proofNames = map removeTxt proofFiles
    mapM_ (func logicName) proofNames

doFunc :: (String -> String -> IO ()) -> IO ()
doFunc func = do
    args <- getArgs
    case args of
        [] -> error "???"
        [logicName] -> overLogic logicName func
        [logicName, proofName] -> func logicName proofName