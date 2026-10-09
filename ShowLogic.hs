
module ShowLogic (main) where

import Core
import Specs

import Data.List
import System.Environment (getArgs)

prettyPrintOperator :: Operator -> String 
prettyPrintOperator op =
    (operatorSymbol op) ++ " (" ++ (operatorName op) ++ "), arity " ++ show (arity op)

defOpDummyArgs :: Int -> [Sentence]
defOpDummyArgs n = map (\(p, i) -> Atom (p ++ show i)) (zip (replicate n "P") (take n [1..]))

dummyDefOp :: DefinedOperator -> String
dummyDefOp defOp =
    case (defOpArity defOp) of
        1 -> (defOpSymbol defOp) ++ " P1"
        2 -> intercalate (" " ++ (defOpSymbol defOp) ++ " ") (map show (defOpDummyArgs (defOpArity defOp)))
        3 -> error "haven't figured out n-ary operators yet (printing out an n-ary defined operator)"

prettyPrintDefOp :: DefinedOperator -> String
prettyPrintDefOp defOp = 
    (defOpSymbol defOp) ++ " (where " ++ (dummyDefOp defOp) ++ " := " ++ show ((definition defOp) (defOpDummyArgs (defOpArity defOp)))

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
        "Defined Operators:\n" ++ (intercalate "\n" (map prettyPrintDefOp (definedOperators logic))),
        "Axioms:\n" ++ (intercalate "\n" (map prettyPrintAxiom (axioms logic))),
        "Inference Rules:\n" ++ (intercalate "\n" (map prettyPrintRule (inferenceRules logic)))
    ]

main :: IO ()
main = do
    [logicName] <- getArgs
    putStrLn (prettyPrintLogic (getLogic logicName))