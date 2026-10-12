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

parseUserProofFile :: String -> String -> IO (Sentence, ([Line] -> [Line]), [Line])
parseUserProofFile logicName proofName = do
    fileContent <- readFile ("hand_proofs/" ++ logicName ++ "/" ++ proofName ++ ".txt")
    createDirectoryIfMissing False ("datalog_proofs/" ++ logicName ++ "/" ++ proofName)
    pure (parseUserProofFile' (getLogic logicName) fileContent)

-- complete function to compile user input to Datalog
userToDatalog' :: String -> String -> IO ()
userToDatalog' logicName proofName = do
    (goal, deductionFunc, userLines) <- parseUserProofFile logicName proofName
    -- HERE is where the going through cited proofs would go
    compileDatalogProof proofName goal logic ((deductionFunc . applyDerivedRules derivedRules logic) userLines)
    where logic = getLogic logicName

    -- fileContent <- readFile ("hand_proofs/" ++ logicName ++ "/" ++ proofName ++ ".txt")
    -- createDirectoryIfMissing False ("datalog_proofs/" ++ logicName ++ "/" ++ proofName)
    -- let (goal, proofLines) = parseUserProofFile (getLogic logicName) fileContent in
    --     compileDatalogProof proofName goal (getLogic logicName) proofLines

main :: IO ()
main = do 
    [logicName, proofName] <- getArgs
    userToDatalog' logicName proofName