
module ShowLogic (main) where

import Core
import Defs.Specs

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
        2 -> intercalate (" " ++ (defOpSymbol defOp) ++ " ") (map prettyPrintSentence (defOpDummyArgs (defOpArity defOp)))
        3 -> error "haven't figured out n-ary operators yet (printing out an n-ary defined operator)"

prettyPrintDefOp :: DefinedOperator -> String
prettyPrintDefOp defOp = 
    (defOpSymbol defOp) ++ " (where " ++ (dummyDefOp defOp) ++ " := " ++ prettyPrintSentence ((definition defOp) (defOpDummyArgs (defOpArity defOp)))

prettyPrintSentence :: Sentence -> String
prettyPrintSentence (Atom str) = str
prettyPrintSentence (OpNode (Operator _ opS 0) []) = opS
prettyPrintSentence (OpNode (Operator _ opS 1) [arg]) = opS ++ "(" ++ prettyPrintSentence arg ++ ")"
prettyPrintSentence (OpNode (Operator _ opS 2) [arg1, arg2]) = "(" ++ prettyPrintSentence arg1 ++ " " ++ opS ++ " " ++ prettyPrintSentence arg2 ++ ")"
prettyPrintSentence (OpNode _ _) = error "either n-ary or something's gone wrong with an operator definition"

prettyPrintAxiom :: Axiom -> String
prettyPrintAxiom axiom =
    axiomName axiom ++ ": |- " ++ prettyPrintSentence (axiomContent axiom)

prettyPrintPremises :: (Sentence, Maybe Sentence) -> String
prettyPrintPremises (prem1, Nothing) =
    "|- " ++ prettyPrintSentence prem1 
prettyPrintPremises (prem1, Just prem2) =
    "|- " ++ prettyPrintSentence prem1 ++ " and |- " ++ prettyPrintSentence prem2

prettyPrintRule :: InferenceRule -> String
prettyPrintRule rule =
    ruleName rule ++ ": " ++ 
    "from " ++ prettyPrintPremises (premises rule) ++
    " conclude |- " ++ prettyPrintSentence (conclusion rule)

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