import Data.List
import System.Environment (getArgs)

getCsvFileName :: String -> String -> String -> String
getCsvFileName logicName proofName csvName =
        intercalate "/" ["datalog_proofs", logicName, proofName, (csvName ++ ".csv")]

checkDatalogOutput' :: String -> String -> IO ()
checkDatalogOutput' logicName proofName = do
    provenContent <- readFile (getCsvFileName logicName proofName "Proven")
    case provenContent of
        [] -> do 
                putStrLn "Proof is not yet proven."
                unjustifiedContent <- readFile (getCsvFileName logicName proofName "Unjustified")
                putStrLn "The following lines of the datalog proof are not proven: "
                putStrLn unjustifiedContent
        _ -> putStrLn (proofName ++" has been proved!")

main :: IO ()
main = do
        [a, b] <- getArgs
        checkDatalogOutput' a b
