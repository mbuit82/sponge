module Core where

import Data.Tree
import Data.List

type Sentence = Tree String
-- helper for writing trees bc leaves are uglyyyy
-- once I get a front end I won't need this tho
lf :: String -> Sentence 
lf name = Node name []

data Operator = Operator {operatorName :: String, arity :: Int}

data Axiom = Axiom {axiomName :: String, axiomContent :: Sentence}

data InferenceRule = InferenceRule {
    ruleName :: String,
    premises :: [Sentence], 
    conclusion :: Sentence}

data Logic = Logic
  { logicName :: String,
    operators :: [Operator],
    axioms :: [Axiom],
    inferenceRules :: [InferenceRule]
  }

operatorToDatalog :: Operator -> String
operatorToDatalog op = 
    " | " ++ operatorName op ++ " {" ++ (intercalate ", " args) ++ "}"
    where 
        args = ["s" ++ show i ++ ": Sentence" | i <- [1 .. (arity op)]]
    
syntaxToDatalog :: Logic -> String
syntaxToDatalog logic =
    ".type Sentence = Atom {name: symbol}" ++ 
    concatMap operatorToDatalog (operators logic) ++ 
    "\n"

formulaToDatalog :: Bool -> Logic -> Sentence -> String
formulaToDatalog varBool logic sentence =
    if not (elem (rootLabel sentence) (map operatorName (operators logic)))
    then if varBool
            then rootLabel sentence
            else "$Atom(\"" ++ (rootLabel sentence) ++ "\")"
    else "$" ++ (rootLabel sentence) ++ "(" ++ argsStr ++ ")"
    where argsStr = intercalate ", " 
            (map (formulaToDatalog varBool logic) (subForest sentence))

schemaToDatalog :: Logic -> Sentence -> String
schemaToDatalog = formulaToDatalog True

sentenceToDatalog :: Logic -> Sentence -> String
sentenceToDatalog = formulaToDatalog False

makeDatalogLine :: Logic -> Sentence -> String -> String -> String -> String -> String
makeDatalogLine logic sentence name n i j =
    "Line(" ++ 
        n ++ ", " ++
        schemaToDatalog logic sentence ++ ", " ++
        (if name == "_" then name else "\"" ++ name ++ "\"") ++ ", " ++ 
        i ++ ", " ++ 
        j ++ ", " ++ 
        "goal)"

axiomToDatalog :: Logic -> Axiom -> String
axiomToDatalog logic axiom = 
    "Justified(n, goal) :- " ++ 
    makeDatalogLine logic (axiomContent axiom) (axiomName axiom) "n" "_" "_" ++ 
    ".\n"

axiomsToDatalog :: Logic -> String
axiomsToDatalog logic = concatMap (axiomToDatalog logic) (axioms logic)

conclusionToDatalog :: Logic -> InferenceRule -> String 
conclusionToDatalog logic rule = 
    "Justified(n, goal) :- " ++ 
    makeDatalogLine logic (conclusion rule) (ruleName rule) "n" "i" jv
    where jv = case premises rule of 
            [_] -> "_"
            [_, _] -> "j"
            _ -> error "should be one or two premises for an inference rule for now"

premisesToDatalog :: Logic -> InferenceRule -> [String] 
premisesToDatalog logic rule =
    concat [ [  v ++ " < n", 
                "Justified(" ++ v ++ ", goal)", 
                makeDatalogLine logic prem "_" v "_" "_"] 
            | (v, prem) <- zip ["i", "j"] (premises rule)]

inferenceRuleToDatalog :: Logic -> InferenceRule -> String 
inferenceRuleToDatalog logic rule =
    intercalate ",\n\t" (concLine : premLines) ++ ".\n"
    where 
        concLine = conclusionToDatalog logic rule
        premLines = premisesToDatalog logic rule

inferenceRulesToDataog :: Logic -> String
inferenceRulesToDataog logic = concatMap (inferenceRuleToDatalog logic) (inferenceRules logic)