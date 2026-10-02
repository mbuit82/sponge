import qualified Data.Map as Map
import Data.Tree
import Data.List
import GHC.Generics (Generic)
import System.IO


type Sentence = Tree String
data Operator = Operator {
    op_name :: String, 
    arity :: Int}
data Axiom = Axiom {
    axiom_name :: String, 
    axiom_content :: Sentence}
data InferenceRule = InferenceRule {
    rule_name :: String,
    premises :: List Sentence, 
    conclusion :: Sentence}

operator_to_datalog :: Operator -> String

syntax_to_datalog :: [Operator] -> String

sentence_to_datalog :: [Operator] -> Sentence -> String

make_datalog_Line :: [Operator] -> Sentence -> String -> String -> String -> String -> String

axioms_to_datalog :: [Operator] -> [Axiom] -> String

conclusion_to_datalog :: [Operator] -> InferenceRule -> String 

premises_to_datalog :: [Operator] -> InferenceRule -> [String] 

inference_rule_to_datalog :: [Operator] -> InferenceRule -> String 

inference_rules_to_datalog :: [Operator] -> [InferenceRule] -> String

-- tested
operator_to_datalog operator = 
    op_name operator ++ " {" ++ (intercalate ", " args) ++ "}"
    where 
        args = ["s" ++ show i ++ ": Sentence" | i <- [1 .. (arity operator)]]
    
-- tested
syntax_to_datalog operators =
    ".type Sentence = Atom {name: symbol}" ++ 
    concatMap (\op -> " | " ++ operator_to_datalog op) operators ++ 
    "\n"

-- NOT TESTED!!
sentence_to_datalog operators sentence =
    let op_names = map (\op -> op_name op) operators in
        if null (subForest sentence) && elem (rootLabel sentence) op_names
        then rootLabel sentence
        else "$" ++ (rootLabel sentence) ++ "(" ++ args_str ++ ")"
    where args_str = intercalate ", " (map (\sentence -> sentence_to_datalog operators sentence) (subForest sentence))

make_datalog_Line operators sentence name n i j =
    "Line(" ++ 
        n ++ ", " ++
        sentence_to_datalog operators sentence ++ ", " ++
        edited_name ++ ", " ++ 
        i ++ ", " ++ 
        j ++ ", " ++ 
        "goal)"
    where edited_name = if name == "_" then name else "\"" ++ name ++ "\""

axioms_to_datalog operators axioms =
    let func = (\axiom -> "Justified(n, goal) :- " ++ make_datalog_Line operators (axiom_content axiom) (axiom_name axiom) "n" "_" "_" ++ ".\n") in 
        concat (map func axioms)

conclusion_to_datalog operators inference_rule = 
    "Justified(n, goal) :- " ++ 
    make_datalog_Line operators (conclusion inference_rule) (rule_name inference_rule) "n" "i" jv
    where jv = case premises inference_rule of 
            [_] -> "_"
            [_, _] -> "j"
            _ -> error "should be one or two premises for an inference rule for now" 

premises_to_datalog operators inference_rule =
    concat [ [v ++ " < n", "Justified(" ++ v ++ ", goal)", make_datalog_Line operators prem "_" v "_" "_"] | (v, prem) <- zip ["i", "j"] prems]
    where prems = premises inference_rule

inference_rule_to_datalog operators inference_rule =
    intercalate ",\n\t" (concLine : premLines) ++ "."
    where 
        concLine = conclusion_to_datalog operators inference_rule
        premLines = premises_to_datalog operators inference_rule

inference_rules_to_datalog operators inference_rules =
    concat [ inference_rule_to_datalog operators rule ++ "\n" | rule <- inference_rules]

data RawSpec = RawSpec
  { name :: String,
    base :: Maybe String,
    ops :: [Operator],
    axs :: [Axiom],
    rules :: [InferenceRule]
  } deriving (Generic)

json_to_haskell :: String -> RawSpec
json_to_haskell = undefined



get_system_specs :: String -> ([Operator], [Axiom], [InferenceRule])
get_system_specs system_name = 
    case (base spec) of
        Nothing -> (ops spec, axs spec, rules spec)
        Just b -> let (bops, baxs, brules) = get_system_specs b in
                        (bops ++ ops spec, 
                            baxs ++ axs spec, 
                            brules ++ rules spec)
    where spec = json_to_haskell system_name

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

compile_datalog_engine :: String -> IO ()
compile_datalog_engine system_name =
    withFile ("datalog_engines/" ++ system_name ++ ".dl") WriteMode $ \h -> do
        hSetEncoding h utf8
        hPutStr h (syntax_to_datalog operators)
        hPutStr h shared_datalog
        hPutStr h (axioms_to_datalog operators axioms)
        hPutStr h (inference_rules_to_datalog operators inference_rules)
    where 
        (operators, axioms, inference_rules) = get_system_specs system_name