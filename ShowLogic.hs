
module ShowLogic (main) where

import Core
import Specs

import Data.List
import System.Environment (getArgs)

prettyPrintOperator :: Operator -> String 
prettyPrintOperator op =
    (operatorSymbol op) ++ " (" ++ (operatorName op) ++ "), arity " ++ show (arity op)

prettyPrintAxiom :: Axiom -> String
prettyPrintAxiom axiom =
    axiomName axiom ++ ": |- " ++ show (axiomContent axiom)

prettyPrintPremises :: (Sentence, Maybe Sentence) -> String
prettyPrintPremises (prem1, Nothing) =
    "|- " ++ show prem1 
prettyPrintPremises (prem1, Just prem2) =
    "|- " ++ show prem1 ++ " and |- " ++ show prem2

prettyPrintRule :: InferenceRule -> String
prettyPrintRule rule =
    ruleName rule ++ ": " ++ 
    "from " ++ prettyPrintPremises (premises rule) ++
    " conclude |- " ++ show (conclusion rule)

prettyPrintLogic :: Logic -> String
prettyPrintLogic logic =
    intercalate "\n\n"
    [
        "Logic name: " ++ logicName logic,
        "Operators:\n" ++ (intercalate "\n" (map prettyPrintOperator (operators logic))),
        "Axioms:\n" ++ (intercalate "\n" (map prettyPrintAxiom (axioms logic))),
        "Inference Rules:\n" ++ (intercalate "\n" (map prettyPrintRule (inferenceRules logic)))
    ]

main :: IO ()
main = do
    [logicName] <- getArgs
    putStrLn (prettyPrintLogic (getLogic logicName))