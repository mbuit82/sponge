module Core where

import Data.List
import Data.Maybe
import Data.Tree

data Operator = Operator {
    operatorName :: String,  -- what datalog will call the operator. what we actually care about form here on out. ideally user optionally picks this name out
    operatorSymbol :: String, -- what the user will write. relevant at tokenizer level. 
    arity :: Int
}
instance Show Operator where
    show op = operatorName op
instance Eq Operator where -- TODO: think about. I think it ultimately doesn't matter lol but still, think about. 
    op1 == op2 = operatorName op1 == operatorName op2 -- datalog will throw an error if there is more than one constructor with the same name for the Sentence predicate so all good there

impl :: Operator
impl = Operator "Implication" "->" 2

data Sentence = Atom {atomName :: String}
              | OpNode {topOp :: Operator, args :: [Sentence]} deriving Eq
instance Show Sentence where 
    show (Atom str) = str
    show (OpNode (Operator opN opS 0) []) = opS
    show (OpNode (Operator opN opS 1) [arg]) = opS ++ "(" ++ show arg ++ ")"
    show (OpNode (Operator opN opS 2) [arg1, arg2]) = "(" ++ show arg1 ++ " " ++ opS ++ " " ++ show arg2 ++ ")"
    show (OpNode (Operator opN opS _) args) = error "either ternary or something's gone wrong with an operator definition"
        -- (show opN) ++ "(" ++ intercalate ", " (map show args) ++ ")" -- ternary+, but for would be indicative that something's gone wrong

data Axiom = Axiom {axiomName :: String, axiomContent :: Sentence} -- low key not necessary

data InferenceRule = InferenceRule {
    ruleName :: String,
    premises :: (Sentence, Maybe Sentence), -- strictly enforce having two
    conclusion :: Sentence}

-- well, by design, the operators in the axioms and inference rules need to be in the operators. 
-- how can I enforce that with the type system? not sure I can
data Logic = Logic
  { logicName :: String,
    operators :: [Operator],
    axioms :: [Axiom],
    inferenceRules :: [InferenceRule]
  }

formulaToDatalog :: Bool -> Sentence -> String
formulaToDatalog varBool sentence =
    case sentence of 
        Atom name -> if varBool
                        then name
                        else "$Atom(\"" ++ name ++ "\")"
        OpNode op args -> "$" ++ (operatorName op) ++ "(" ++ argsStr ++ ")"
            where argsStr = intercalate ", " 
                    (map (formulaToDatalog varBool) args)

schemaToDatalog :: Sentence -> String
schemaToDatalog = formulaToDatalog True

sentenceToDatalog :: Sentence -> String
sentenceToDatalog = formulaToDatalog False


-- RUNTIME CHECKS FOR LATER
aritiesCheck :: Sentence -> Bool
aritiesCheck sentence =
    case sentence of
        Atom _ -> True
        OpNode op args -> if arity op == length args 
            then all aritiesCheck args
            else False

isWff :: Logic -> Sentence -> Bool
isWff logic sentence =
    case sentence of
        Atom _ -> True
        OpNode op args -> if elem op (operators logic)
            then all (isWff logic) args
            else False

axiomsWf :: Logic -> Bool
axiomsWf logic = all (isWff logic) (map axiomContent (axioms logic))

inferenceRuleWf :: Logic -> InferenceRule -> Bool
inferenceRuleWf logic rule = 
    isWff logic (conclusion rule) && case premises rule of
        (p1, Nothing) -> isWff logic p1
        (p1, Just p2) -> isWff logic p1 && isWff logic p2

inferenceRulesWf :: Logic -> Bool
inferenceRulesWf logic = all (inferenceRuleWf logic) (inferenceRules logic)
-- END RUNTIME CHECKS


isInstance :: Sentence -> Sentence -> Bool
-- the first Sentence is a sentence, second is a schema
-- need to think about naming for sentences/formulae
-- for now, assume everything is well-formed. 
isInstance sentence schema =
    case schema of
        Atom _ -> True
        OpNode schemaOp schemaArgs ->
            case sentence of
                Atom _ -> False
                OpNode sentOp sentArgs -> 
                    schemaOp == sentOp && all (\p -> isInstance (fst p) (snd p)) (zip sentArgs schemaArgs)

haveSameStructure :: Sentence -> Sentence -> Bool
haveSameStructure s1 s2 = isInstance s1 s2 && isInstance s2 s1



-- user input to Haskell
data Token = LPToken | RPToken | OpToken Operator | AtomToken String
instance Show Token where
    show LPToken = "("
    show RPToken = ")"
    show (OpToken operator) = operatorSymbol operator
    show (AtomToken str) = str

exportCurrToken :: Maybe String -> [Token]
exportCurrToken Nothing = [] -- :: [[Char]]
exportCurrToken (Just a) = [AtomToken a] -- :: [[Char]]

getOpWithSymbol :: [Operator] -> String -> Maybe Operator
getOpWithSymbol [] name = Nothing
getOpWithSymbol (op : rem) name =
    if operatorSymbol op == name then (Just op) else getOpWithSymbol rem name

tokenize' :: [Operator] -> String -> Maybe String -> [Token]
tokenize' ops [] beingBuilt = exportCurrToken beingBuilt -- we're never going to have an operator at the end is what this is saying... 
tokenize' ops (char : remChars) beingBuilt =
    if fromMaybe [] beingBuilt `elem` (map operatorSymbol ops)
        then  [OpToken (fromJust (getOpWithSymbol ops (fromJust beingBuilt)))] ++ tokenize' ops (char : remChars) Nothing -- now we can do no spaces after operators!
        else case char of -- we know that the currently being built is _not_ an operator, so we can treat it as not one (or something that's not one yet)
            '(' -> exportCurrToken beingBuilt ++ [LPToken] ++ tokenize' ops remChars Nothing
            ')' -> exportCurrToken beingBuilt ++ [RPToken] ++ tokenize' ops remChars Nothing
            ' ' -> exportCurrToken beingBuilt              ++ tokenize' ops remChars Nothing
            ',' -> exportCurrToken beingBuilt              ++ tokenize' ops remChars Nothing -- for stuff after "by" and in general why not
            char -> tokenize' ops remChars (Just (fromMaybe [] beingBuilt ++ [char]))

tokenize :: [Operator] -> String -> [Token]
tokenize ops str = tokenize' ops str Nothing

parse' :: [String] -> Maybe [String] -> Tree String
parse' tokens currArg = undefined

parse :: [Token] -> Sentence
parse = undefined