module Specs where

import Core

import Data.List
import System.IO


-- moved these functions here because these are exclusively for making engines
constructorToDatalog :: Operator -> String
constructorToDatalog op = 
    " | " ++ operatorName op ++ " {" ++ (intercalate ", " args) ++ "}"
    where 
        args = ["s" ++ show i ++ ": Sentence" | i <- [1 .. (arity op)]]
    
syntaxToDatalog :: Logic -> String
syntaxToDatalog logic = concatMap constructorToDatalog (operators logic)

makeDatalogLine :: Sentence -> String -> String -> String -> String -> String
makeDatalogLine sentence name n i j =
    "Line(" ++ 
        n ++ ", " ++
        schemaToDatalog sentence ++ ", " ++
        (if name == "_" then name else "\"" ++ name ++ "\"") ++ ", " ++ 
        i ++ ", " ++ 
        j ++ ")"

axiomToDatalog :: Axiom -> String
axiomToDatalog axiom = 
    "Justified(n) :- " ++ 
    makeDatalogLine (axiomContent axiom) (axiomName axiom) "n" "_" "_" ++ 
    ".\n"

axiomsToDatalog :: Logic -> String
axiomsToDatalog logic = concatMap axiomToDatalog (axioms logic)

conclusionToDatalog :: InferenceRule -> String 
conclusionToDatalog rule = 
    "Justified(n) :- " ++ 
    makeDatalogLine (conclusion rule) (ruleName rule) "n" "i" jv
    where jv = case snd (premises rule) of 
            Nothing -> "_"
            Just _ -> "j"

premisesToDatalog :: InferenceRule -> [String] 
premisesToDatalog rule =
    concat [ [  v ++ " < n", 
                "Justified(" ++ v ++ ")", 
                makeDatalogLine prem "_" v "_" "_"] 
            | (v, prem) <- zip ["i", "j"] premList]
    where premList = case snd (premises rule) of
                        Nothing -> [fst (premises rule)]
                        Just s -> [fst (premises rule), s]

inferenceRuleToDatalog :: InferenceRule -> String 
inferenceRuleToDatalog rule =
    intercalate ",\n\t" (concLine : premLines) ++ ".\n"
    where 
        concLine = conclusionToDatalog rule
        premLines = premisesToDatalog rule

inferenceRulesToDataog :: Logic -> String
inferenceRulesToDataog logic = concatMap inferenceRuleToDatalog (inferenceRules logic)

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
    "\n",
    ".decl Line(line_num: unsigned, line_content: Sentence, line_just: symbol, i: unsigned, j: unsigned)",
    ".decl Justified(n: unsigned)",
    ".decl Unjustified(n: unsigned)",
    ".decl UnjustifiedCount(c: number)",
    ".decl Goal(goal: Sentence)",
    ".decl Proven(f: Sentence)\n",
    "Unjustified(n) :- Line(n, _, _, _, _), !Justified(n).",
    "UnjustifiedCount(c) :- c = count : { Unjustified(_) }.",
    "Proven(f) :- Goal(f),\n\tLine(n, f, _, _, _),\n\tJustified(n),\n\tUnjustifiedCount(0).\n",
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