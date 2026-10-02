module Specs where

import Core

import Data.Tree
import Data.List
import System.IO

data Spec = Spec
  { specName :: String,
    baseSystem :: Maybe Spec,
    newOperators :: [Operator],
    newAxioms :: [Axiom],
    newInferenceRules :: [InferenceRule]
  }

getLogic :: Spec -> Logic
getLogic spec = 
    case (baseSystem spec) of
        Nothing ->  (Logic { 
                        logicName = specName spec, 
                        operators = newOperators spec, 
                        axioms = newAxioms spec, 
                        inferenceRules = newInferenceRules spec })
        Just base -> let baseLogic = getLogic base in
                    (Logic { 
                        logicName = specName spec, 
                        operators = operators baseLogic ++ newOperators spec, 
                        axioms = axioms baseLogic ++ newAxioms spec, 
                        inferenceRules = inferenceRules baseLogic ++ newInferenceRules spec })

sharedDatalog :: String
sharedDatalog = unlines [
    ".type Goal = ToProve {s: Sentence}\n",
    ".decl Line(line_num: unsigned, line_content: Sentence, line_just: symbol, i: unsigned, j: unsigned, goal: Goal)",
    ".decl Justified(n: unsigned, goal: Goal)",
    ".decl Unjustified(n: unsigned, goal: Goal)",
    ".decl UnjustifiedCount(c: number, goal: Goal)",
    ".decl Claim(goal: Goal)",
    ".decl Proven(f: Sentence)\n",
    "Unjustified(n, goal) :- Line(n, _, _, _, _, goal), !Justified(n, goal).",
    "UnjustifiedCount(c, goal) :- Claim(goal), c = count : { Unjustified(_, goal) }.",
    "Proven(f) :- Claim($ToProve(f)),\n\tLine(n, f, _, _, _, $ToProve(f)),\n\tJustified(n, $ToProve(f)),\n\tUnjustifiedCount(0, $ToProve(f)).\n",
    ".output Unjustified\n.output Justified\n.output Proven\n"
    ]

compileDatalogEngine :: Spec -> IO ()
compileDatalogEngine spec =
    withFile ("datalog_engines/" ++ specName spec ++ ".dl") WriteMode $ \h -> do
        hSetEncoding h utf8
        hPutStr h (syntaxToDatalog logic)
        hPutStr h sharedDatalog
        hPutStr h (axiomsToDatalog logic)
        hPutStr h (inferenceRulesToDataog logic)
    where 
        logic = getLogic spec


specIntuitionistic :: Spec
specIntuitionistic = Spec {
    specName = "intuitionistic",
    baseSystem = Nothing,
    newOperators = [Operator "Bot" 0, Operator "Implication" 2],
    newAxioms = [
        Axiom "Axiom1" (Node "Implication" [lf "P", lf "P"]),
        Axiom "Axiom2" (Node "Implication" [lf "P", Node "Implication" [lf "Q", lf "P"]]),
        Axiom "Axiom3" (Node "Implication" [Node "Implication" [lf "P", lf "Q"], Node "Implication" [Node "Implication" [lf "P", Node "Implication" [lf "Q", lf "R"]], Node "Implication" [lf "P", lf "R"]]]),
        Axiom "Axiom4" (Node "Implication" [Node "Implication" [lf "P", lf "Bot"], Node "Implication" [lf "P", lf "Q"]])],
    newInferenceRules = [InferenceRule "Modus Ponens" [lf "P", Node "Implication" [lf "P", lf "Q"]] (lf "Q")]
}

specClassical :: Spec
specClassical = Spec {
    specName = "classical",
    baseSystem = Just specIntuitionistic,
    newOperators = [],
    newAxioms = [Axiom "Axiom5" (Node "Implication" [Node "Implication" [Node "Implication" [lf "P", lf "Bot"], lf "Bot"], lf "P"])],
    newInferenceRules = []
}

specK :: Spec
specK = Spec {
    specName = "K",
    baseSystem = Just specClassical,
    newOperators = [Operator "Box" 1],
    newAxioms = [Axiom "K Axiom" (Node "Implication" [Node "Box" [Node "Implication" [lf "P", lf "Q"]], Node "Implication" [Node "Box" [lf "P"], Node "Box" [lf "Q"]]])],
    newInferenceRules = [InferenceRule "N" [lf "P"] (Node "Box" [lf "P"])]
}