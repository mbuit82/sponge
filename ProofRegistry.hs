module ProofRegistry where

import Core
import Defs.Specs
import CheckDatalogOutput

import System.Environment (getArgs)
import qualified Data.Map as Map

-- basing this of CheckDatalogOutput, the way this would work is that all Souffle proofs are run, and then all csvs are checked.

-- the type is not a maybe just to avoid iteration again that would remove Nothings
-- and this should return the _full_ proof, ie only with axioms
checkDatalogOutputKeepingProof :: String -> String -> IO (Maybe (String, Sentence, [Line]))
checkDatalogOutputKeepingProof logicName proofName = do
    result <- checkDatalogOutput' logicName proofName
    case result of 
        False -> pure Nothing
        True -> do 
            userProofContent <- readFile ("hand_proofs/" ++ logicName ++ "/" ++ proofName ++ ".txt")
            let (goal, proofLines) = parseUserProofFile (getLogic logicName) userProofContent
            pure (Just (proofName, goal, proofLines))

-- -- goes through the list twice. I think this is the best I can do without external package
-- makeLogicProofs' :: String -> [String] -> IO (Map.Map String (Sentence, [Line]))
-- makeLogicProofs' logicName fileNames =
--     (Map.fromList . concat) <$> mapM (checkDatalogOutputKeepingProof logicName . (\str -> str)) fileNames

-- makeLogicProofs :: String -> IO ()
-- makeLogicProofs logicName = do
--     fileNames <- listDirectory ("datalog_proofs/" ++ logicName)
--     logicsDict <- makeLogicProofs' logicName fileNames
--     encodeFile (logicName ++ "_theorems.bin") logicsDict

-- No. You don't need to do all of this. On any given citation of a proof, you just need to access that proof's lines. 
-- I've already realized that I have to embed everything in IO, I'm already fucked there. 
-- So appending stuff that's IO isn't that bad. 

-- How do I originally get _out_ of IO? Since I do proof manipulations _not_ in IO. The way I do that is that I start in an IO, then I do a <- thing, then I do all the operations I want, and then I continue. 
-- So you only need to have the parsing proof function IO. It isn't an overhaul of everything, since everything else is still only declarative. 