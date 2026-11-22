module Commands.CheckInHaskell where

import Core
import Defs.Specs
import DerivedRules.UseDerivedRules
import ToDatalog.Utils


-- NOTE: don't have command for this yet!

checkInHaskell' :: String -> String -> IO (String, Bool)
checkInHaskell' logicName proofName = do
    (goal, pft) <- getHaskellProof logicName proofName
    let result = checkProof (getLogic logicName) pft
    pure (proofName, result)

checkLogic' :: String -> IO (String, [String])
checkLogic' logicName = do 
    results <- overLogic logicName checkInHaskell'
    let notProved = map fst (filter (\p -> not (snd p)) results)
    pure (logicName, notProved)

reportOnProof :: String -> String -> Bool -> IO ()
reportOnProof logicName proofName result = do
    putStrLn ("checking " ++ proofName ++ " (from " ++ logicName ++ ") in Haskell ...")
    if result
        then putStrLn (proofName ++ " is proved!")
        else putStrLn (proofName ++ " has NOT been proved.")
    putStrLn ""

reportOnLogic :: String -> [String] -> IO ()
reportOnLogic logicName notProved =
    if null notProved 
        then putStrLn ("All theorems in " ++ logicName ++ " are proved!")
        else putStrLn ("The following " ++ logicName ++ " theorems are NOT yet proved:\n" ++ show notProved)

checkInHaskell :: String -> String -> IO ()
checkInHaskell logicName proofName = do
    (_, result) <- checkInHaskell' logicName proofName
    reportOnProof logicName proofName result

checkLogic :: String -> IO ()
checkLogic logicName = do 
    (logicName, notProved) <- checkLogic' logicName
    reportOnLogic logicName notProved

-- NOTE: I think something about this doesn't work because it was saying some proofs that were not right were right
checkAll :: IO ()
checkAll = do
    results <- mapM checkLogic' logicNames
    mapM_ (\(lName, notProved) -> reportOnLogic lName notProved) results