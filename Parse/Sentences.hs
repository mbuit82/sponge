module Parse.Sentences (parse, instantiateVar, parseWithSubst) where

import Core

import Data.Maybe
import qualified Data.Map as Map

-- user input to Haskell
data Token = LPToken | RPToken | OpToken Operator | DefOpToken DefinedOperator | AtomToken String
instance Show Token where
    show LPToken = "("
    show RPToken = ")"
    show (OpToken operator) = "OpToken " ++ operatorSymbol operator
    show (DefOpToken defOp) = "DefOpToken " ++ defOpSymbol defOp
    show (AtomToken str) = "AtomToken " ++ str

toAtomToken :: String -> [Token]
toAtomToken [] = []
toAtomToken a = [AtomToken a]

getWithStr :: (a -> String) -> [a] -> String -> Maybe a
getWithStr _ [] _ = Nothing
getWithStr strFunc (x:xs) str =
    if strFunc x == str then (Just x) else getWithStr strFunc xs str

getOpWithSymbol :: [Operator] -> String -> Maybe Operator
getOpWithSymbol = getWithStr operatorSymbol

getDefOpWithSymbol :: [DefinedOperator] -> String -> Maybe DefinedOperator
getDefOpWithSymbol = getWithStr defOpSymbol

tokenize' :: [Operator] -> [DefinedOperator] -> String -> String -> [Token]
tokenize' ops defOps toSee beingBuilt
    | beingBuilt `elem` (map operatorSymbol ops) = 
        [OpToken (fromJust (getOpWithSymbol ops beingBuilt))] ++ tokenize' ops defOps toSee []
    | beingBuilt `elem` (map defOpSymbol defOps) =
        [DefOpToken (fromJust (getDefOpWithSymbol defOps beingBuilt))] ++ tokenize' ops defOps toSee []
    | otherwise = case toSee of
        [] -> toAtomToken beingBuilt
        '(' : remChars -> toAtomToken beingBuilt ++ [LPToken] ++ tokenize' ops defOps remChars [] -- should never happen? 
        ')' : remChars -> toAtomToken beingBuilt ++ [RPToken] ++ tokenize' ops defOps remChars []
        ' ' : remChars -> toAtomToken beingBuilt              ++ tokenize' ops defOps remChars []
        x : remChars -> tokenize' ops defOps remChars (beingBuilt ++ [x])

tokenize :: [Operator] -> [DefinedOperator] -> String -> [Token]
tokenize ops defOps str = tokenize' ops defOps str []

pop :: [a] -> [a]
pop [] = error "Stack underflow from pop"
pop (_:xs) = xs

fetch :: [a] -> a
fetch [] = error "Stack underflow from fetch"
fetch (x:_) = x

getNextSentence' :: (String -> Sentence) -> [Token] -> [Sentence] -> [Token] -> (Sentence, [Token])
getNextSentence' _ [] [sent] toSee = (sent, toSee) -- yes: we've gotten the next sentence, and there's no operators (so we're not currently building something). perfect.
getNextSentence' _ opStack [] [] = error ("shid we reached the end and we have no sentences lel. current opStack (rest are empty): " ++ show opStack)
getNextSentence' _ opStack [sent] [] = error ("this case doesn't make sense really. opStack and sentStack: " ++ show opStack ++ ", " ++ show sent)
getNextSentence' _ opStack sentStack [] = error ("error in parsing. check for a missing set of parentheses? opStack and sentStack: " ++ show opStack ++ ", " ++ show sentStack)
getNextSentence' atomFunc opStack sentStack toSee =
    case toSee of
        LPToken : toks -> getNextSentence' atomFunc (LPToken : opStack) sentStack toks
        RPToken : toks -> case fetch opStack of
                            -- we only put binary operaotrs/defops on the opstack. unary and nullary are just immediately put on the sentStack
                            OpToken op -> case sentStack of
                                            rArg : lArg : remSents -> getNextSentence' atomFunc (pop (pop opStack)) (OpNode op [lArg, rArg] : remSents) toks -- this should really be pop until you see a LPToken
                                            _ -> error "not enough args"
                            DefOpToken defOp -> case sentStack of
                                            rArg : lArg : remSents -> getNextSentence' atomFunc (pop (pop opStack)) (((definition defOp) [lArg, rArg]) : remSents ) toks -- this should really be pop until you see a LPToken
                                            _ -> error "not enough args"
                            LPToken -> getNextSentence' atomFunc (pop opStack) sentStack toks -- sandwiched something lol (unary or nullary operator that over-parenthesized)
                            _ -> error "should have been an operator on the stack but there wasn't"
        AtomToken a : toks -> getNextSentence' atomFunc opStack (atomFunc a : sentStack) toks
        OpToken op : toks -> case arity op of
                                0 -> getNextSentence' atomFunc opStack (OpNode op [] : sentStack) toks
                                1 -> let (nextSent, newRem) = getNextSentence' atomFunc [] [] toks in
                                        getNextSentence' atomFunc opStack (OpNode op [nextSent] : sentStack) newRem
                                2 -> getNextSentence' atomFunc (OpToken op : opStack) sentStack toks
                                _ -> error "not doing n-ary predicates yet (got n-ary operator)"
        DefOpToken defOp : toks -> case defOpArity defOp of
                                0 -> getNextSentence' atomFunc opStack (((definition defOp) []) : sentStack) toks
                                1 -> let (nextSent, newRem) = getNextSentence' atomFunc [] [] toks in
                                        getNextSentence' atomFunc opStack (((definition defOp) [nextSent]) : sentStack) newRem
                                2 -> getNextSentence' atomFunc (DefOpToken defOp : opStack) sentStack toks
                                _ -> error "not doing n-ary predicates yet (got n-ary defined operator)"

-- lmao so we just add an extra set of parentheses onto everything lol
-- to avoid O(n) iteration through toks, could move this to base case of tokenize' function
-- or think of smarter way to do top level parens lol
getTopLevelSentence :: (String -> Sentence) -> [Token] -> Sentence
getTopLevelSentence atomFunc toks = fst (getNextSentence' atomFunc [] [] (LPToken : toks ++ [RPToken]))



-- these below are really the only functions that should be exported
parse :: [Operator] -> [DefinedOperator] -> String -> Sentence
parse ops defOps input = getTopLevelSentence Atom (tokenize ops defOps input)

instantiateVar :: Map.Map String Sentence -> String -> Sentence
instantiateVar varMap str = case varMap Map.!? str of
    Nothing -> error ("variable " ++ str ++ " is not in the substitution " ++ show varMap)
    Just sent -> sent

parseWithSubst :: [Operator] -> [DefinedOperator] -> String -> Substitution -> Sentence
parseWithSubst ops defOps input varTuples = 
    let varMap = Map.fromList varTuples in
        getTopLevelSentence (instantiateVar varMap) (tokenize ops defOps input)

-- -- used in substitutions in derived rules
-- getApplySubstFromTransformant :: Transformant -> String -> Substitution -> Sentence
-- getApplySubstFromTransformant transformant =
--     let logic = transformantLogic transformant in
--         parseWithSubst (operators logic) (definedOperators logic)
