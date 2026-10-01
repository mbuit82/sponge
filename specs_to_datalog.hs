import qualified Data.Map as Map
import Data.Tree
import Data.List


type Sentence = Tree String
data Operator = Operator {
    op_name :: String, 
    arity :: Int}
type Operators = List Operator
data Axiom = Axiom {
    axiom_name :: String, 
    axiom_content :: Sentence}
data Inference_Rule = InferenceRule {
    rule_name :: String,
    premises :: List Sentence, 
    conclusion :: Sentence}
data NIJ_Coords = NIJ_Coords {
    n :: String, 
    i :: String,  
    j :: String}

operator_to_datalog :: Operator -> String

syntax_to_datalog :: Operators -> String

sentence_to_datalog :: Operators -> Sentence -> String

-- make_datalog_Line :: Operators -> Sentence -> String -> NIJ_Coords -> String

-- axioms_to_datalog :: Operators -> List Axiom -> String

-- inference_rule_to_datalog :: Operators -> InferenceRule -> String 

-- inference_rules_to_datalog :: Operators -> List InferenceRule -> String

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
        else 
            "$" ++ (rootLabel sentence) ++ "(" ++ args_str ++ ")"
    where args_str = intercalate ", " (map (\sentence -> sentence_to_datalog operators sentence) (subForest sentence))


