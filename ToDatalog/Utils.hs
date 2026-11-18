module ToDatalog.Utils where

import Core
-- import Defs.Specs
-- import ToDatalog.PruneProofTrees
-- import DerivedRules.UseDerivedRules

-- import System.IO
import Data.List
import System.Environment (getArgs)
import System.Directory
import Control.Monad (void)


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

overLogic :: String -> (String -> String -> IO (b)) -> IO ([b])
overLogic logicName func = do 
    files <- listDirectory ("user_proofs/" ++ logicName ++ "/")
    let proofFiles = filter isTxtFileName files
    let proofNames = map removeTxt proofFiles
    mapM (func logicName) proofNames

doFunc :: (String -> String -> IO (b)) -> IO ()
doFunc func = do
    args <- getArgs
    case args of
        [] -> error "???"
        [logicName] -> void (overLogic logicName func)
        [logicName, proofName] -> void (func logicName proofName)