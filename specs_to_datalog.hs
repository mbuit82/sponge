import qualified Data.Map as Map
import Data.Tree
import Data.List
import System.IO

type Sentence = Tree String
lf :: String -> Sentence -- helper for writing trees bc leaves are uglyyyy
lf name = Node name []
data Operator = Operator {
    operatorName :: String, 
    arity :: Int}
data Axiom = Axiom {
    axiomName :: String, 
    axiomContent :: Sentence}
data InferenceRule = InferenceRule {
    ruleName :: String,
    premises :: [Sentence], 
    conclusion :: Sentence}

operatorToDatalog :: Operator -> String
operatorToDatalog op = 
    operatorName op ++ " {" ++ (intercalate ", " args) ++ "}"
    where 
        args = ["s" ++ show i ++ ": Sentence" | i <- [1 .. (arity op)]]
    
syntaxToDatalog :: [Operator] -> String
syntaxToDatalog ops =
    ".type Sentence = Atom {name: symbol}" ++ 
    concatMap (\op -> " | " ++ operatorToDatalog op) ops ++ 
    "\n"

sentenceToDatalog :: [Operator] -> Sentence -> String
sentenceToDatalog ops sentence =
    let opNames = map (\op -> operatorName op) ops in
        if null (subForest sentence) && not (elem (rootLabel sentence) opNames)
        then rootLabel sentence
        else "$" ++ (rootLabel sentence) ++ "(" ++ argsStr ++ ")"
    where argsStr = intercalate ", " (map (\sentence -> sentenceToDatalog ops sentence) (subForest sentence))

makeDatalogLine :: [Operator] -> Sentence -> String -> String -> String -> String -> String
makeDatalogLine ops sentence name n i j =
    "Line(" ++ 
        n ++ ", " ++
        sentenceToDatalog ops sentence ++ ", " ++
        editedName ++ ", " ++ 
        i ++ ", " ++ 
        j ++ ", " ++ 
        "goal)"
    where editedName = if name == "_" then name else "\"" ++ name ++ "\""

axiomToDatalog :: [Operator] -> Axiom -> String
axiomToDatalog ops axiom = 
    "Justified(n, goal) :- " ++ 
    makeDatalogLine ops (axiomContent axiom) (axiomName axiom) "n" "_" "_" ++ 
    ".\n"

axiomsToDatalog :: [Operator] -> [Axiom] -> String
axiomsToDatalog ops axioms = concatMap (axiomToDatalog ops) axioms

conclusionToDatalog :: [Operator] -> InferenceRule -> String 
conclusionToDatalog ops rule = 
    "Justified(n, goal) :- " ++ 
    makeDatalogLine ops (conclusion rule) (ruleName rule) "n" "i" jv
    where jv = case premises rule of 
            [_] -> "_"
            [_, _] -> "j"
            _ -> error "should be one or two premises for an inference rule for now" 

premisesToDatalog :: [Operator] -> InferenceRule -> [String] 
premisesToDatalog ops rule =
    concat [ [v ++ " < n", "Justified(" ++ v ++ ", goal)", makeDatalogLine ops prem "_" v "_" "_"] | (v, prem) <- zip ["i", "j"] prems]
    where prems = premises rule

inferenceRuleToDatalog :: [Operator] -> InferenceRule -> String 
inferenceRuleToDatalog ops rule =
    intercalate ",\n\t" (concLine : premLines) ++ ".\n"
    where 
        concLine = conclusionToDatalog ops rule
        premLines = premisesToDatalog ops rule

inferenceRulesToDataog :: [Operator] -> [InferenceRule] -> String
inferenceRulesToDataog ops rules = concatMap (inferenceRuleToDatalog ops) rules

data RawSpec = RawSpec
  { systemName :: String,
    baseSystem :: Maybe RawSpec,
    operators :: [Operator],
    axioms :: [Axiom],
    inferenceRules :: [InferenceRule]
  }

getSystemSpecs :: RawSpec -> ([Operator], [Axiom], [InferenceRule])
getSystemSpecs spec = 
    case (baseSystem spec) of
        Nothing -> (operators spec, axioms spec, inferenceRules spec)
        Just b -> let (bops, baxs, brules) = getSystemSpecs b in
                        (bops ++ operators spec, 
                            baxs ++ axioms spec, 
                            brules ++ inferenceRules spec)

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

compileDatalogEngine :: RawSpec -> IO ()
compileDatalogEngine spec =
    withFile ("datalog_engines/" ++ systemName spec ++ ".dl") WriteMode $ \h -> do
        hSetEncoding h utf8
        hPutStr h (syntaxToDatalog operators)
        hPutStr h sharedDatalog
        hPutStr h (axiomsToDatalog operators axioms)
        hPutStr h (inferenceRulesToDataog operators inferenceRules)
    where 
        (operators, axioms, inferenceRules) = getSystemSpecs spec

specIntuitionistic :: RawSpec
specIntuitionistic = RawSpec {
    systemName = "intuitionistic",
    baseSystem = Nothing,
    operators = [Operator "Bot" 0, Operator "Implication" 2],
    axioms = [
        Axiom "Axiom1" (Node "Implication" [lf "P", lf "P"]),
        Axiom "Axiom2" (Node "Implication" [lf "P", Node "Implication" [lf "Q", lf "P"]]),
        Axiom "Axiom3" (Node "Implication" [Node "Implication" [lf "P", lf "Q"], Node "Implication" [Node "Implication" [lf "P", Node "Implication" [lf "Q", lf "R"]], Node "Implication" [lf "P", lf "R"]]]),
        Axiom "Axiom4" (Node "Implication" [Node "Implication" [lf "P", lf "Bot"], Node "Implication" [lf "P", lf "Q"]])],
    inferenceRules = [InferenceRule "Modus Ponens" [lf "P", Node "Implication" [lf "P", lf "Q"]] (lf "Q")]
}

specClassical :: RawSpec
specClassical = RawSpec {
    systemName = "classical",
    baseSystem = Just specIntuitionistic,
    operators = [],
    axioms = [Axiom "Axiom5" (Node "Implication" [Node "Implication" [Node "Implication" [lf "P", lf "Bot"], lf "Bot"], lf "P"])],
    inferenceRules = []
}

specK :: RawSpec
specK = RawSpec {
    systemName = "K",
    baseSystem = Just specClassical,
    operators = [Operator "Box" 1],
    axioms = [Axiom "K Axiom" (Node "Implication" [Node "Box" [Node "Implication" [lf "P", lf "Q"]], Node "Implication" [Node "Box" [lf "P"], Node "Box" [lf "Q"]]])],
    inferenceRules = [InferenceRule "N" [lf "P"] (Node "Box" [lf "P"])]
}