module Commands.CheckDatalogOutput where

import ToDatalog.Utils

import Data.List
import System.Environment (getArgs)
import Data.Binary (encodeFile, decodeFile)

getCsvFileName :: String -> String -> String -> String
getCsvFileName logicName proofName csvName =
        intercalate "/" ["datalog/datalog_proofs", logicName, proofName, (csvName ++ ".csv")]

checkDatalogOutput' :: String -> String -> IO Bool
checkDatalogOutput' logicName proofName = do
    provenContent <- readFile (getCsvFileName logicName proofName "Proven")
    case provenContent of
        [] -> pure False
        _ -> pure True

checkDatalogOutputWithMsg :: String -> String -> IO ()
checkDatalogOutputWithMsg logicName proofName = do
        -- putStrLn ("CHECKING " ++ proofName ++ " (from " ++ logicName ++ ")")
        result <- checkDatalogOutput' logicName proofName
        if result
                then do putStrLn (proofName ++" has been proved!")
                else do 
                        putStrLn "Proof is not yet proven."
                        unjustifiedContent <- readFile (getCsvFileName logicName proofName "Unjustified")
                        putStrLn "The following lines of the datalog proof are not proven: "
                        putStrLn unjustifiedContent
        putStrLn ""

main :: IO ()
main = doFunc checkDatalogOutputWithMsg