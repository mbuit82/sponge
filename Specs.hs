module Specs where

import Core

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
    "",
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
    -- I want to check that all axioms and inference rules are well-formed. 
    -- use the all function and the isWff function.
    -- Also here check that all inference rules have max 2 premises
    -- I think this ideally happens not here, but like in a check function. 
    -- for now I can run that check function here
    -- well like I want it to happen _before_ I apply all the transformations on proofs. Like it should be the _first_ thing that happens. 
    withFile ("datalog_engines/" ++ specName spec ++ ".dl") WriteMode $ \h -> do
        hSetEncoding h utf8
        hPutStr h ".type Sentence = Atom {name: symbol}"
        hPutStr h (syntaxToDatalog logic)
        hPutStr h sharedDatalog
        hPutStr h (axiomsToDatalog logic)
        hPutStr h (inferenceRulesToDataog logic)
    where 
        logic = getLogic spec

bot :: Operator
bot = Operator "Bot" 0

specIntuitionistic :: Spec
specIntuitionistic = Spec {
    specName = "intuitionistic",
    baseSystem = Nothing,
    newOperators = [bot, impl],
    newAxioms = [
        Axiom "Axiom1" (OpNode impl [Atom "P", Atom "P"]),
        Axiom "Axiom2" (OpNode impl [Atom "P", OpNode impl [Atom "Q", Atom "P"]]),
        Axiom "Axiom3" (OpNode impl [OpNode impl [Atom "P", Atom "Q"], OpNode impl [OpNode impl [Atom "P", OpNode impl [Atom "Q", Atom "R"]], OpNode impl [Atom "P", Atom "R"]]]),
        Axiom "Axiom4" (OpNode impl [OpNode impl [Atom "P", OpNode bot []], OpNode impl [Atom "P", Atom "Q"]])],
    newInferenceRules = [InferenceRule "Modus Ponens" (Atom "P", Just (OpNode impl [Atom "P", Atom "Q"])) (Atom "Q")]
}

specClassical :: Spec
specClassical = Spec {
    specName = "classical",
    baseSystem = Just specIntuitionistic,
    newOperators = [],
    newAxioms = [Axiom "Axiom5" (OpNode impl [OpNode impl [OpNode impl [Atom "P", OpNode bot []], OpNode bot []], Atom "P"])],
    newInferenceRules = []
}

box :: Operator
box = Operator "Box" 1

specK :: Spec
specK = Spec {
    specName = "K",
    baseSystem = Just specClassical,
    newOperators = [box],
    newAxioms = [Axiom "K Axiom" (OpNode impl [OpNode box [OpNode impl [Atom "P", Atom "Q"]], OpNode impl [OpNode box [Atom "P"], OpNode box [Atom "Q"]]])],
    newInferenceRules = [InferenceRule "N" (Atom "P", Nothing) (OpNode box [Atom "P"])]
}