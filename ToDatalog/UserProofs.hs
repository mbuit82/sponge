module ToDatalog.UserProofs where

import Core
import Defs.Specs
import Defs.Rules
import ToDatalog.Utils
import Proofs

import System.IO
import Data.List
import System.Environment (getArgs)
import System.Directory (createDirectoryIfMissing)

sentenceToDatalog :: Sentence -> String
sentenceToDatalog = formulaToDatalog False

lineToDatalog :: Line -> String
lineToDatalog line =
    let rfs = if refLines line == [] then [0, 0] else refLines line in
        "Line(" ++ show (lineNumber line) ++ ", " ++
        sentenceToDatalog (lineContent line) ++ ", " ++ 
        "\"" ++ justification line ++ "\", " ++ 
        (intercalate ", " . map show) rfs ++ ").\n"

proofToDatalog :: Sentence -> [Line] -> String
proofToDatalog proofGoal proofLines =
    "Goal(" ++ 
    sentenceToDatalog proofGoal ++ 
    ").\n\n" ++
    concatMap lineToDatalog proofLines
    
compileDatalogProof :: String -> Sentence -> Logic -> [Line] -> IO ()
compileDatalogProof proofName proofGoal proofLogic proofLines =
    withFile ("datalog_proofs/" ++ logicName proofLogic ++ "/" ++ proofName ++ "/" ++ proofName ++ ".dl") WriteMode $ \h -> do
        hSetEncoding h utf8
        hPutStr h ("#include \"../../../datalog_engines/" ++ (logicName proofLogic) ++ ".dl\"\n\n")
        hPutStr h (proofToDatalog proofGoal proofLines)

-- complete function to compile user input to Datalog
userToDatalog' :: String -> String -> IO ()
userToDatalog' logicName proofName = do
    (goal, haskellProof) <- getHaskellProof logicName proofName
    compileDatalogProof proofName goal logic haskellProof
    where logic = getLogic logicName

main :: IO ()
main = do 
    [logicName, proofName] <- getArgs
    userToDatalog' logicName proofName