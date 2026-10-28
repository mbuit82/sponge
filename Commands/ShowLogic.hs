module Commands.ShowLogic (main) where

import Core
import Defs.Specs

import Data.List
import System.Environment (getArgs)

prettyPrintPremises :: (Sentence, Maybe Sentence) -> String
prettyPrintPremises (prem1, Nothing) =
    "|- " ++ prettyPrintSentence prem1 
prettyPrintPremises (prem1, Just prem2) =
    "|- " ++ prettyPrintSentence prem1 ++ " and |- " ++ prettyPrintSentence prem2

prettyPrintRule :: InferenceRule -> String
prettyPrintRule rule =
    ruleName rule ++ ": " ++ 
    "from " ++ prettyPrintPremises (premises rule) ++
    " infer |- " ++ prettyPrintSentence (conclusion rule)

prettyPrintLogic :: Logic -> String
prettyPrintLogic logic =
    intercalate "\n\n"
    [
        "Logic name: " ++ logicName logic,
        "Operators:\n" ++ (intercalate "\n" (map prettyPrintOperator (operators logic))),
        "Defined Operators:\n" ++ (intercalate "\n" (map prettyPrintDefOp (definedOperators logic))),
        "Axioms:\n" ++ (intercalate "\n" (map prettyPrintAxiom (axioms logic))),
        "Inference Rules:\n" ++ (intercalate "\n" (map prettyPrintRule (inferenceRules logic)))
    ]

main :: IO ()
main = do
    [logicName] <- getArgs
    putStrLn (prettyPrintLogic (getLogic logicName))