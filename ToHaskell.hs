module ToHaskell where

import Core

import Data.List
import Data.Maybe
import Proofs
import Data.Char

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

pop :: [a] -> [a]
pop [] = error "Stack underflow from pop"
pop (x:xs) = xs

fetch :: [a] -> a
fetch [] = error "Stack underflow from fetch"
fetch (x:xs) = x

getNextSentence :: [Token] -> [Sentence] -> [Token] -> (Sentence, [Token])
-- getNextSentence [OpToken binOp] [rArg, lArg] [] = (OpNode binOp [lArg, rArg], []) -- my attempt at no top level parentheses. The problem is tha we never get there
getNextSentence [] [sent] toSee = (sent, toSee) -- yes: we've gotten the next sentence, and there's no operators (so we're not currently building something). perfect.
getNextSentence opStack [] [] = error "shid we reached the end and we have no sentences lel"
getNextSentence opStack [sent] [] = error "this case doesn't make sense really"
getNextSentence opStack (sent:remS) [] = error "check for a missing set of parentheses?"
getNextSentence opStack sentStack toSee =
    case toSee of
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

-- lmao so we just add an extra set of parentheses onto everything lol. 
getTopLevelSentence :: [Token] -> Sentence
-- getTopLevelSentence (LPToken : rem) = fst (getNextSentence [] [] (LPToken:rem)) -- we have a first paren, so guessing we have a last. If we don't or if unbalanced we'll throw an error somewhre prolly
getTopLevelSentence toks = fst (getNextSentence [] [] (LPToken : toks ++ [RPToken]))

parseSentence :: [Operator] -> String -> Sentence
parseSentence ops input = getTopLevelSentence (tokenize ops input)

getLineNumFromLine :: String -> String -> (Int, String)
getLineNumFromLine seen toSee = 
    case toSee of
        '.' : ' ' : '|' : '-' : ' ' : rem -> (read seen, rem)
        [] -> error "couldn't find line number split!"
        c : rem -> getLineNumFromLine (seen ++ [c]) rem

getContentFromLine :: [Operator] -> String -> String -> (Sentence, String)
getContentFromLine ops seen toSee =
    case toSee of
        'b' : 'y' : ' ' : rem -> (parseSentence ops seen, rem)
        [] -> error "line wasn't justified!"
        c : rem -> getContentFromLine ops (seen ++ [c]) rem

-- meant to be applied after getting the content
getJustificationFromLine :: String -> String -> (String, Maybe (Int, Int))
getJustificationFromLine seen toSee =
    case toSee of
        ',' : rem -> case rem of
                        [] -> (seen, Nothing)
                        s -> case words s of
                                [i, j] -> (seen, Just (read i, read j))
                                _ -> error "theres stuff after justification but it's not two ints"
        [] -> (seen, Nothing) -- axiom case (with no trailing comma)
        c : rem -> getJustificationFromLine (seen ++ [c]) rem

getLineFromUser :: [Operator] -> String -> Line
getLineFromUser ops userLine =
    let (lNum, rem1) = getLineNumFromLine "" userLine in
        let (content, rem2) = getContentFromLine ops "" rem1 in
            let (j, rfs) = getJustificationFromLine "" rem2 in
                Line lNum content j rfs (Just lNum)

getProofGoal :: [Operator] -> String -> String -> Sentence
getProofGoal ops seen [] = error "proof has no goal!"
getProofGoal ops seen ('|' : '-' : rem) = parseSentence ops rem
getProofGoal ops seen (c:tail) = getProofGoal ops (seen ++ [c]) tail

-- function to use after getting the goal
-- For now, use this one, but am thinking of having a general one where deduction is one of many last-transformations done
parseUserProofWithDeduction :: Logic -> Sentence -> [String] -> [Line]
parseUserProofWithDeduction logic deductionRelativeGoal [] = []
parseUserProofWithDeduction logic deductionRelativeGoal (fl : rem)
    | isInfixOf "deduction" fl =
        case deductionRelativeGoal of
            OpNode impl [lArg, rArg] -> useDeduction logic lArg (parseUserProofWithDeduction logic rArg rem)
            _ -> error "ope should have implication in goal to use deduction"
    | (all isSpace fl) || fl == "Proof" = parseUserProofWithDeduction logic deductionRelativeGoal rem -- ignore conditions
    | otherwise = getLineFromUser (operators logic) fl : parseUserProofWithDeduction logic deductionRelativeGoal rem

splitByProofLine :: [String] -> (String, [String])
splitByProofLine [] = error "file has no lines!"
splitByProofLine (l:tl) = (l, tl)

parseUserProofFile :: Logic -> String -> (Sentence, [Line])
parseUserProofFile logic fileContent =
    let (goalLine, pfLines) = splitByProofLine (lines fileContent) in
        let goal = getProofGoal (operators logic) [] goalLine in
            (goal, parseUserProofWithDeduction logic goal pfLines)