module ToDatalog.Utils where

import Core
import Specs ( getLogic, logicsDict )

import Data.List
import qualified Data.Map as Map
import System.Environment (getArgs)


formulaToDatalog :: Bool -> Sentence -> String
formulaToDatalog True (Atom name) = name
formulaToDatalog False (Atom name) = "$Atom(\"" ++ name ++ "\")"
formulaToDatalog schemaBool (OpNode op args) = 
    "$" ++ (operatorName op) ++ "(" ++ argsStr ++ ")"
        where argsStr = intercalate ", " (map (formulaToDatalog schemaBool) args)