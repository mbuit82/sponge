module ToDatalog.UserProofs where

import Core
import Specs ( getLogic, logicsDict )
import ToDatalog.Utils
import Proofs

import System.IO
import qualified Data.Map as Map
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
    fileContent <- readFile ("hand_proofs/" ++ logicName ++ "/" ++ proofName ++ ".txt")
    createDirectoryIfMissing False ("datalog_proofs/" ++ logicName ++ "/" ++ proofName)
    let (goal, proofLines) = parseUserProofFile logicName fileContent in
        compileDatalogProof proofName goal (getLogic logicName) proofLines

main :: IO ()
main = do 
    [logicName, proofName] <- getArgs
    userToDatalog' logicName proofName