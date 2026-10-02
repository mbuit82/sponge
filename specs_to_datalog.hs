import qualified Data.Map as Map
import Data.Tree
import Data.List
import System.IO

type Sentence = Tree String
lf :: String -> Sentence -- helper for writing trees bc leaves are uglyyyy
lf name = Node name []
data Operator = Operator {
    operator_name :: String, 
    arity :: Int}
data Axiom = Axiom {
    axiom_name :: String, 
    axiom_content :: Sentence}
data InferenceRule = InferenceRule {
    rule_name :: String,
    premises :: [Sentence], 
    conclusion :: Sentence}

operator_to_datalog :: Operator -> String

syntax_to_datalog :: [Operator] -> String

sentence_to_datalog :: [Operator] -> Sentence -> String

make_datalog_Line :: [Operator] -> Sentence -> String -> String -> String -> String -> String

axiom_to_datalog :: [Operator] -> Axiom -> String

axioms_to_datalog :: [Operator] -> [Axiom] -> String

conclusion_to_datalog :: [Operator] -> InferenceRule -> String 

premises_to_datalog :: [Operator] -> InferenceRule -> [String] 

inference_rule_to_datalog :: [Operator] -> InferenceRule -> String 

inference_rules_to_datalog :: [Operator] -> [InferenceRule] -> String

operator_to_datalog op = 
    operator_name op ++ " {" ++ (intercalate ", " args) ++ "}"
    where 
        args = ["s" ++ show i ++ ": Sentence" | i <- [1 .. (arity op)]]
    
syntax_to_datalog ops =
    ".type Sentence = Atom {name: symbol}" ++ 
    concatMap (\op -> " | " ++ operator_to_datalog op) ops ++ 
    "\n"

sentence_to_datalog ops sentence =
    let op_names = map (\op -> operator_name op) ops in
        if null (subForest sentence) && not (elem (rootLabel sentence) op_names)
        then rootLabel sentence
        else "$" ++ (rootLabel sentence) ++ "(" ++ args_str ++ ")"
    where args_str = intercalate ", " (map (\sentence -> sentence_to_datalog ops sentence) (subForest sentence))

make_datalog_Line ops sentence name n i j =
    "Line(" ++ 
        n ++ ", " ++
        sentence_to_datalog ops sentence ++ ", " ++
        edited_name ++ ", " ++ 
        i ++ ", " ++ 
        j ++ ", " ++ 
        "goal)"
    where edited_name = if name == "_" then name else "\"" ++ name ++ "\""

axiom_to_datalog ops axiom = 
    "Justified(n, goal) :- " ++ 
    make_datalog_Line ops (axiom_content axiom) (axiom_name axiom) "n" "_" "_" ++ 
    ".\n"

axioms_to_datalog ops axioms = concatMap (axiom_to_datalog ops) axioms

conclusion_to_datalog ops rule = 
    "Justified(n, goal) :- " ++ 
    make_datalog_Line ops (conclusion rule) (rule_name rule) "n" "i" jv
    where jv = case premises rule of 
            [_] -> "_"
            [_, _] -> "j"
            _ -> error "should be one or two premises for an inference rule for now" 

premises_to_datalog ops rule =
    concat [ [v ++ " < n", "Justified(" ++ v ++ ", goal)", make_datalog_Line ops prem "_" v "_" "_"] | (v, prem) <- zip ["i", "j"] prems]
    where prems = premises rule

inference_rule_to_datalog ops rule =
    intercalate ",\n\t" (concLine : premLines) ++ ".\n"
    where 
        concLine = conclusion_to_datalog ops rule
        premLines = premises_to_datalog ops rule

inference_rules_to_datalog ops rules = concatMap (inference_rule_to_datalog ops) rules

data RawSpec = RawSpec
  { system_name :: String,
    base_system :: Maybe RawSpec,
    operators :: [Operator],
    axioms :: [Axiom],
    inference_rules :: [InferenceRule]
  }

get_system_specs :: RawSpec -> ([Operator], [Axiom], [InferenceRule])
get_system_specs spec = 
    case (base_system spec) of
        Nothing -> (operators spec, axioms spec, inference_rules spec)
        Just b -> let (bops, baxs, brules) = get_system_specs b in
                        (bops ++ operators spec, 
                            baxs ++ axioms spec, 
                            brules ++ inference_rules spec)

shared_datalog :: String
shared_datalog = unlines [
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

compile_datalog_engine :: RawSpec -> IO ()
compile_datalog_engine spec =
    withFile ("datalog_engines/" ++ system_name spec ++ ".dl") WriteMode $ \h -> do
        hSetEncoding h utf8
        hPutStr h (syntax_to_datalog operators)
        hPutStr h shared_datalog
        hPutStr h (axioms_to_datalog operators axioms)
        hPutStr h (inference_rules_to_datalog operators inference_rules)
    where 
        (operators, axioms, inference_rules) = get_system_specs spec

spec_intuitionistic :: RawSpec
spec_intuitionistic = RawSpec {
    system_name = "intuitionistic",
    base_system = Nothing,
    operators = [Operator "Bot" 0, Operator "Implication" 2],
    axioms = [
        Axiom "Axiom1" (Node "Implication" [lf "P", lf "P"]),
        Axiom "Axiom2" (Node "Implication" [lf "P", Node "Implication" [lf "Q", lf "P"]]),
        Axiom "Axiom3" (Node "Implication" [Node "Implication" [lf "P", lf "Q"], Node "Implication" [Node "Implication" [lf "P", Node "Implication" [lf "Q", lf "R"]], Node "Implication" [lf "P", lf "R"]]]),
        Axiom "Axiom4" (Node "Implication" [Node "Implication" [lf "P", lf "Bot"], Node "Implication" [lf "P", lf "Q"]])],
    inference_rules = [InferenceRule "Modus Ponens" [lf "P", Node "Implication" [lf "P", lf "Q"]] (lf "Q")]
}

spec_classical :: RawSpec
spec_classical = RawSpec {
    system_name = "classical",
    base_system = Just spec_intuitionistic,
    operators = [],
    axioms = [Axiom "Axiom5" (Node "Implication" [Node "Implication" [Node "Implication" [lf "P", lf "Bot"], lf "Bot"], lf "P"])],
    inference_rules = []
}

spec_K :: RawSpec
spec_K = RawSpec {
    system_name = "K",
    base_system = Just spec_classical,
    operators = [Operator "Box" 1],
    axioms = [Axiom "K Axiom" (Node "Implication" [Node "Box" [Node "Implication" [lf "P", lf "Q"]], Node "Implication" [Node "Box" [lf "P"], Node "Box" [lf "Q"]]])],
    inference_rules = [InferenceRule "N" [lf "P"] (Node "Box" [lf "P"])]
}