module Core where

import Data.List
import Data.Maybe
import Data.Tree

data Operator = Operator {
    operatorName :: String,  -- what datalog will call the operator. what we actually care about form here on out. ideally user optionally picks this name out
    operatorSymbol :: String, -- what the user will write. relevant at tokenizer level. 
    arity :: Int
} deriving (Eq, Show) -- you've seriously fucked up if the three don't match, but I think only operatorName really needs to
-- instance Show Operator where
--     show op = operatorName op
-- instance Eq Operator where -- TODO: think about. I think it ultimately doesn't matter lol but still, think about. 
--     op1 == op2 = operatorName op1 == operatorName op2 -- datalog will throw an error if there is more than one constructor with the same name for the Sentence predicate so all good there

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
tokenize' ops [] beingBuilt = 
    if fromMaybe [] beingBuilt `elem` (map operatorSymbol ops)
        then [OpToken (fromJust (getOpWithSymbol ops (fromJust beingBuilt)))]
        else exportCurrToken beingBuilt
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

push :: a -> [a] -> [a]
push x stack = x : stack

pop :: [a] -> [a]
pop [] = error "Stack underflow from pop"
pop (x:xs) = xs

fetch :: [a] -> a
fetch [] = error "Stack underflow from fetch"
fetch (x:xs) = x

getNextSentence :: [Token] -> [Sentence] -> [Token] -> (Sentence, [Token])
getNextSentence [] [sent] toSee = (sent, toSee)
getNextSentence opStack sentStack toSee =
    case toSee of
        [] -> case sentStack of 
                [sent] -> (sent, [])
                sent : remS -> error "have lots of sentences here"
                _ -> error "shid"
        LPToken : rem -> getNextSentence (LPToken : opStack) sentStack rem
        RPToken : rem -> case fetch opStack of
                            OpToken op -> case sentStack of
                                            rArg : lArg : remSents -> getNextSentence (pop (pop opStack)) (OpNode op [lArg, rArg] : remSents) rem -- this should really be pop until you see a LPToken
                                            _ -> error "not enough args"
                            LPToken -> getNextSentence (pop opStack) sentStack rem -- sandwiched something lol (unary or nullary operator that over-parenthesized)
                            _ -> error "should have been an operator on the stack but there wasn't"
        AtomToken a : rem -> getNextSentence opStack (Atom a : sentStack) rem
        OpToken op : rem -> case arity op of
                                0 -> getNextSentence opStack (OpNode op [] : sentStack) rem
                                1 -> let (nextSent, newRem) = getNextSentence [] [] rem in
                                        getNextSentence opStack (OpNode op [nextSent] : sentStack) newRem
                                2 -> getNextSentence (OpToken op : opStack) sentStack rem
                                _ -> error "not doing n-ary predicates yet"



-- parse' :: [Token] -> [Sentence] -> [Token] -> Sentence
-- -- associativity and precedence are dealt with at the RPToken case
-- -- for no top-level parentheses, edit the [] case
-- parse' opStack sentStack toSee =
--     case toSee of
--         [] -> undefined -- we're done?
--         LPToken : rem -> parse' (LPToken : opStack) sentStack rem
--         RPToken : rem -> case fetch opStack of -- I think we can do it so that we only put binary operators on the opStack
--                             OpToken op -> undefined
--                             _ -> error "should have been an operator here"
--         AtomToken a : rem -> parse' opStack (Atom a : sentStack) rem
--         OpToken op : rem -> case arity op of
--                                 0 -> parse' opStack (OpNode op [] : sentStack) rem
--                                 1 -> undefined -- get the next sentence in toSee, and make that the argument, and push that to the sentence stack
--                                 2 -> parse' (OpToken op : opStack) sentStack rem

parse :: [Operator] -> String -> Sentence
parse ops input = fst (getNextSentence [] [] (tokenize ops input))

