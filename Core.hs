module Core where

import Data.Maybe

data Operator = Operator {
    operatorName :: String,  -- what datalog will call the operator. what we actually care about form here on out. ideally user optionally picks this name out
    operatorSymbol :: String, -- what the user will write. relevant at tokenizer level. 
    arity :: Int
} deriving (Eq, Show)

data DefinedOperator = DefinedOperator {
    defOpName :: String,
    defOpSymbol :: String, 
    defOpArity :: Int,
    definition :: [Sentence] -> Sentence
} 

cond :: Operator
cond = Operator "Conditional" "->" 2

data Sentence = Atom {atomName :: String}
              | OpNode {topOp :: Operator, args :: [Sentence]} deriving Eq
instance Show Sentence where 
    show (Atom str) = str
    show (OpNode (Operator _ opS 0) []) = opS
    show (OpNode (Operator _ opS 1) [arg]) = opS ++ "(" ++ show arg ++ ")"
    show (OpNode (Operator _ opS 2) [arg1, arg2]) = "(" ++ show arg1 ++ " " ++ opS ++ " " ++ show arg2 ++ ")"
    show (OpNode _ _) = error "either n-ary or something's gone wrong with an operator definition"
        -- (show opN) ++ "(" ++ intercalate ", " (map show args) ++ ")" -- n-ary, but for would be indicative that something's gone wrong

data Axiom = Axiom {axiomName :: String, axiomContent :: Sentence} deriving Show
-- low key not necessary

data InferenceRule = InferenceRule {
    ruleName :: String,
    premises :: (Sentence, Maybe Sentence), -- strictly enforce having two
    conclusion :: Sentence} deriving Show

-- well, by design, the operators in the axioms and inference rules need to be in the operators. 
-- how can I enforce that with the type system? not sure I can
-- you basically enforce it by design...? actually no that depends on the user lol
-- I think you'd have to create a syntax object and then a logic object. Kinda gross. I trust users on this
data Logic = Logic
  { logicName :: String,
    operators :: [Operator],
    definedOperators :: [DefinedOperator],
    axioms :: [Axiom],
    inferenceRules :: [InferenceRule]
  } 

-- for proofs
data Line = Line {
    lineNumber :: Int,
    lineContent :: Sentence,
    justification :: String,
    refLines :: [Int],
    userNumber :: Maybe Int -- the original line number the user used (NOTE: actually this is not that lol it's like an old pointer type thing lol)
} deriving Eq
-- a proof, inside haskell, is just a list of lines. That's all Haskell knows about proofs. (I used to have a proof type)
instance Show Line where
    show line = show (lineNumber line) ++ " " ++
                userNumberHuh (userNumber line) ++ ". " ++ 
                show (lineContent line) ++ "\t" ++ 
                "by " ++ justification line ++ show (refLines line)

userNumberHuh :: Maybe Int -> String
userNumberHuh Nothing = "-"
userNumberHuh (Just n) = "(" ++ show n ++ ")"



-- RUNTIME CHECKS FOR LATER
aritiesCheck :: Sentence -> Bool
aritiesCheck (Atom _) = True
aritiesCheck (OpNode op args)
    | arity op == length args = all aritiesCheck args
    | otherwise = False

isWff :: Logic -> Sentence -> Bool
isWff _ (Atom _) = True
isWff logic (OpNode op args)
    | elem op (operators logic) = all (isWff logic) args
    | otherwise = False

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
isInstance _ (Atom _) = True
isInstance sentence (OpNode schemaOp schemaArgs) =
    case sentence of 
        Atom _ -> False
        OpNode sentOp sentArgs -> 
            schemaOp == sentOp && all (\p -> isInstance (fst p) (snd p)) (zip sentArgs schemaArgs)

haveSameStructure :: Sentence -> Sentence -> Bool
haveSameStructure s1 s2 = isInstance s1 s2 && isInstance s2 s1



-- for avoiding that stupid souffle warning
getAtoms :: Sentence -> [String]
getAtoms (Atom a) = [a]
getAtoms (OpNode _ args) = concatMap getAtoms args

getNumVarOccurences :: String -> Sentence -> Int
getNumVarOccurences tgtVar (Atom a) =
    if a == tgtVar then 1 else 0
getNumVarOccurences tgtVar (OpNode _ args) =
    sum (map (getNumVarOccurences tgtVar) args)

getSingletonVars :: Sentence -> [String]
getSingletonVars sentence =
    let pairList = map (\str -> (str, getNumVarOccurences str sentence)) (getAtoms sentence) in
        map fst (filter (\(_, numOcc) -> numOcc == 1) pairList)

dashVarsOut :: [String] -> Sentence -> Sentence
dashVarsOut toDash (Atom a) = if a `elem` toDash then Atom "_" else Atom a
dashVarsOut toDash (OpNode op args) = OpNode op (map (dashVarsOut toDash) args)

dashSingletonVars :: Sentence -> Sentence
dashSingletonVars sentence =
    let toDash = getSingletonVars sentence in
        dashVarsOut toDash sentence



-- user input to Haskell
data Token = LPToken | RPToken | OpToken Operator | DefOpToken DefinedOperator | AtomToken String
instance Show Token where
    show LPToken = "("
    show RPToken = ")"
    show (OpToken operator) = "OpToken " ++ operatorSymbol operator
    show (DefOpToken defOp) = "DefOpToken " ++ defOpSymbol defOp
    show (AtomToken str) = "AtomToken " ++ str

exportCurrToken :: String -> [Token]
exportCurrToken [] = []
exportCurrToken a = [AtomToken a]

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
        [] -> exportCurrToken beingBuilt
        '(' : remChars -> exportCurrToken beingBuilt ++ [LPToken] ++ tokenize' ops defOps remChars []
        ')' : remChars -> exportCurrToken beingBuilt ++ [RPToken] ++ tokenize' ops defOps remChars []
        ' ' : remChars -> exportCurrToken beingBuilt              ++ tokenize' ops defOps remChars []
        ',' : remChars -> exportCurrToken beingBuilt              ++ tokenize' ops defOps remChars [] -- for stuff after "by" and in general why not
        x : remChars -> tokenize' ops defOps remChars (beingBuilt ++ [x])

tokenize :: [Operator] -> [DefinedOperator] -> String -> [Token]
tokenize ops defOps str = tokenize' ops defOps str []

pop :: [a] -> [a]
pop [] = error "Stack underflow from pop"
pop (_:xs) = xs

fetch :: [a] -> a
fetch [] = error "Stack underflow from fetch"
fetch (x:_) = x

getNextSentence :: [Token] -> [Sentence] -> [Token] -> (Sentence, [Token])
-- getNextSentence [OpToken binOp] [rArg, lArg] [] = (OpNode binOp [lArg, rArg], []) -- my attempt at no top level parentheses. The problem is tha we never get there
getNextSentence [] [sent] toSee = (sent, toSee) -- yes: we've gotten the next sentence, and there's no operators (so we're not currently building something). perfect.
getNextSentence opStack [] [] = error ("shid we reached the end and we have no sentences lel. current opStack (rest are empty): " ++ show opStack)
getNextSentence opStack [sent] [] = error ("this case doesn't make sense really. opStack and sentStack: " ++ show opStack ++ ", " ++ show sent)
getNextSentence opStack sentStack [] = error ("error in parsing. check for a missing set of parentheses? opStack and sentStack: " ++ show opStack ++ ", " ++ show sentStack)
getNextSentence opStack sentStack toSee =
    case toSee of
        LPToken : toks -> getNextSentence (LPToken : opStack) sentStack toks
        RPToken : toks -> case fetch opStack of
                            -- we only put binary operaotrs/defops on the opstack. unary and nullary are just immediately put on the sentStack
                            OpToken op -> case sentStack of
                                            rArg : lArg : remSents -> getNextSentence (pop (pop opStack)) (OpNode op [lArg, rArg] : remSents) toks -- this should really be pop until you see a LPToken
                                            _ -> error "not enough args"
                            DefOpToken defOp -> case sentStack of
                                            rArg : lArg : remSents -> getNextSentence (pop (pop opStack)) (((definition defOp) [lArg, rArg]) : remSents ) toks -- this should really be pop until you see a LPToken
                                            _ -> error "not enough args"
                            LPToken -> getNextSentence (pop opStack) sentStack toks -- sandwiched something lol (unary or nullary operator that over-parenthesized)
                            _ -> error "should have been an operator on the stack but there wasn't"
        AtomToken a : toks -> getNextSentence opStack (Atom a : sentStack) toks
        OpToken op : toks -> case arity op of
                                0 -> getNextSentence opStack (OpNode op [] : sentStack) toks
                                1 -> let (nextSent, newRem) = getNextSentence [] [] toks in
                                        getNextSentence opStack (OpNode op [nextSent] : sentStack) newRem
                                2 -> getNextSentence (OpToken op : opStack) sentStack toks
                                _ -> error "not doing n-ary predicates yet (got n-ary operator)"
        DefOpToken defOp : toks -> case defOpArity defOp of
                                0 -> getNextSentence opStack (((definition defOp) []) : sentStack) toks
                                1 -> let (nextSent, newRem) = getNextSentence [] [] toks in
                                        getNextSentence opStack (((definition defOp) [nextSent]) : sentStack) newRem
                                2 -> getNextSentence (DefOpToken defOp : opStack) sentStack toks
                                _ -> error "not doing n-ary predicates yet (got n-ary defined operator)"

-- lmao so we just add an extra set of parentheses onto everything lol. 
getTopLevelSentence :: [Token] -> Sentence
-- getTopLevelSentence (LPToken : rem) = fst (getNextSentence [] [] (LPToken:rem)) -- we have a first paren, so guessing we have a last. If we don't or if unbalanced we'll throw an error somewhre prolly
getTopLevelSentence toks = fst (getNextSentence [] [] (LPToken : toks ++ [RPToken]))

parse :: [Operator] -> [DefinedOperator] -> String -> Sentence
parse ops defOps input = getTopLevelSentence (tokenize ops defOps input)

getLineNumFromLine :: String -> String -> (Int, String)
getLineNumFromLine seen toSee = 
    case toSee of
        '.' : ' ' : '|' : '-' : ' ' : remChars -> (read seen, remChars)
        [] -> error "couldn't find line number split! Maybe you forgot to include \"|-\" in a line?"
        c : remChars -> getLineNumFromLine (seen ++ [c]) remChars

-- here is where automatic use of defined operators happens
getContentFromLine :: Logic -> String -> String -> (Sentence, String)
getContentFromLine logic seen toSee =
    case toSee of
        'b' : 'y' : ' ' : remChars -> (parse (operators logic) (definedOperators logic) seen, remChars)
        [] -> error "line wasn't justified!"
        c : remChars -> getContentFromLine logic (seen ++ [c]) remChars

-- meant to be applied after getting the content
getJustificationFromLine :: String -> String -> (String, [Int])
getJustificationFromLine seen toSee =
    case toSee of
        ',' : remChars -> case remChars of
                            [] -> (seen, [])
                            s -> (seen, map read (words s))
                                    -- [i, j] -> (seen, Just (read i, read j))
                                    -- _ -> error "theres stuff after justification but it's not just ints"
        [] -> (seen, []) -- axiom case (with no trailing comma)
        c : remChars -> getJustificationFromLine (seen ++ [c]) remChars

getLineFromUser :: Logic -> String -> Line
getLineFromUser logic userLine =
    let (lNum, rem1) = getLineNumFromLine "" userLine in
        let (content, rem2) = getContentFromLine logic "" rem1 in
            let (j, rfs) = getJustificationFromLine "" rem2 in
                Line lNum content j rfs (Just lNum)

getProofGoal :: Logic -> String -> String -> Sentence
getProofGoal _ _ [] = error "proof has no goal!"
getProofGoal logic _ ('|' : '-' : remChars) = parse (operators logic) (definedOperators logic) remChars
getProofGoal logic seen (c:remChars) = getProofGoal logic (seen ++ [c]) remChars