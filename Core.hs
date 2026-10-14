module Core where

import Data.Maybe
import Data.List
import qualified Data.Map as Map

data Operator = Operator {
    operatorName :: String,  -- what datalog will call the operator. what we actually care about form here on out. ideally user optionally picks this name out
    operatorSymbol :: String, -- what the user will write. relevant at tokenizer level. 
    arity :: Int
} deriving (Eq, Show, Read, Ord)
prettyPrintOperator :: Operator -> String 
prettyPrintOperator op =
    (operatorSymbol op) ++ " (" ++ (operatorName op) ++ "), arity " ++ show (arity op)

data DefinedOperator = DefinedOperator {
    defOpName :: String,
    defOpSymbol :: String, 
    defOpArity :: Int,
    definition :: [Sentence] -> Sentence
} 
defOpDummyArgs :: Int -> [Sentence]
defOpDummyArgs n = map (\(p, i) -> Atom (p ++ show i)) (zip (replicate n "P") (take n [1..]))

dummyDefOp :: DefinedOperator -> String
dummyDefOp defOp =
    case (defOpArity defOp) of
        1 -> (defOpSymbol defOp) ++ " P1"
        2 -> intercalate (" " ++ (defOpSymbol defOp) ++ " ") (map prettyPrintSentence (defOpDummyArgs (defOpArity defOp)))
        3 -> error "haven't figured out n-ary operators yet (printing out an n-ary defined operator)"

prettyPrintDefOp :: DefinedOperator -> String
prettyPrintDefOp defOp = 
    (defOpSymbol defOp) ++ " (where " ++ (dummyDefOp defOp) ++ " := " ++ prettyPrintSentence ((definition defOp) (defOpDummyArgs (defOpArity defOp)))

cond :: Operator
cond = Operator "Conditional" "->" 2

data Sentence = Atom {atomName :: String}
              | OpNode {topOp :: Operator, args :: [Sentence]} deriving (Eq, Read, Ord)
prettyPrintSentence :: Sentence -> String
prettyPrintSentence (Atom str) = str
prettyPrintSentence (OpNode (Operator _ opS 0) []) = opS
prettyPrintSentence (OpNode (Operator _ opS 1) [arg]) = opS ++ "(" ++ prettyPrintSentence arg ++ ")"
prettyPrintSentence (OpNode (Operator _ opS 2) [arg1, arg2]) = "(" ++ prettyPrintSentence arg1 ++ " " ++ opS ++ " " ++ prettyPrintSentence arg2 ++ ")"
prettyPrintSentence (OpNode _ _) = error "either n-ary or something's gone wrong with an operator definition"
instance Show Sentence where
    show = prettyPrintSentence

data Axiom = Axiom {axiomName :: String, axiomContent :: Sentence} deriving (Eq, Show, Read) -- low key not necessary
prettyPrintAxiom :: Axiom -> String
prettyPrintAxiom axiom =
    axiomName axiom ++ ": |- " ++ prettyPrintSentence (axiomContent axiom)

data InferenceRule = InferenceRule {
    ruleName :: String,
    premises :: (Sentence, Maybe Sentence), -- can have max two (bc of how Datalog is set up)
    conclusion :: Sentence} deriving (Eq, Show, Read)

type DerivedRule = (String, Transformation)

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
} deriving (Eq, Show, Read) -- a proof, inside haskell, is just a list of lines. That's all Haskell knows about proofs. (I used to have a proof type)
-- keeping this here in case it's ever relevant
-- prettyPrintLine :: Line -> String
-- prettyPrintLine (Line lNum c j rfs uNum) = 
--     show lNum ++ " " ++
--     userNumberHuh uNum ++ ". " ++ 
--     prettyPrintSentence c ++ "\t" ++ 
--     "by " ++ j ++ show rfs

userNumberHuh :: Maybe Int -> String
userNumberHuh Nothing = "-"
userNumberHuh (Just n) = "(" ++ show n ++ ")"



-- RUNTIME CHECKS FOR LATER
-- thought these would be good to do. I think they're basically enforced though. Would be good to do tho? 
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

parse :: [Operator] -> [DefinedOperator] -> String -> Sentence
parse ops defOps input = getTopLevelSentence Atom (tokenize ops defOps input)

type Substitution = [(String, Sentence)]

instantiateVar :: Map.Map String Sentence -> String -> Sentence
instantiateVar varMap str = case varMap Map.!? str of
    Nothing -> error ("variable " ++ str ++ " is not in the substitution " ++ show varMap)
    Just sent -> sent

parseWithSubst :: [Operator] -> [DefinedOperator] -> String -> Substitution -> Sentence
parseWithSubst ops defOps input varTuples = 
    let varMap = Map.fromList varTuples in
        getTopLevelSentence (instantiateVar varMap) (tokenize ops defOps input)

-- used in substitutions in derived rules
getApplySubstFromTransformant :: Transformant -> String -> Substitution -> Sentence
getApplySubstFromTransformant transformant =
    let logic = transformantLogic transformant in
        parseWithSubst (operators logic) (definedOperators logic)

getLineNumFromLine :: String -> String -> (Int, String)
getLineNumFromLine seen toSee = 
    case toSee of
        '.' : ' ' : '|' : '-' : ' ' : remChars -> (read seen, remChars)
        [] -> error "couldn't find line number split. Maybe you forgot to include \"|-\" in a line?"
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
        ':' : remChars -> case remChars of
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



-- need to move now that derived rules are transformations and are in logics :/
-- Wait. And now that they're not, I can move it back... 
data Transformant = Transformant {  transformata :: [Line], 
                                    curr :: Maybe Line, 
                                    transformanda :: [Line], 
                                    offset :: Int,
                                    transformantLogic :: Logic}

type Transformation = Transformant -> [Line]

-- when we run a transformation on a _proof state_, we want to return the result ++ old transformata, and then take the next element and make that the next current. 
applyTransformation :: Transformation -> Transformant -> Transformant
applyTransformation transformation oldState =
    Transformant (applied ++ transformata oldState) newCurr newTransformanda ((length applied) - 1 + offset oldState) (transformantLogic oldState)
    where 
        applied = reverse (transformation oldState)
        (newCurr, newTransformanda) = case transformanda oldState of
            [] -> (Nothing, [])
            nxt:remLines -> (Just nxt, remLines)

identityTransformation :: Transformation
identityTransformation transformant = 
    case curr transformant of
        Nothing -> []
        Just (Line lNum c j rfs uNum) -> 
            [Line (lNum + offset transformant) c j (getUpdatedCurrentRefs transformant) uNum]

-- the second arg is supposed to be a proof
intoTransformant :: Logic -> [Line] -> Transformant
intoTransformant _ [] = error "can't transformation a proof with no steps!" -- not really sure what should happen here either
intoTransformant logic (fstLine:remLines) = Transformant [] (Just fstLine) remLines 0 logic 

findLineWithUserNum' :: [Line] -> Int -> Maybe Line
findLineWithUserNum' [] _ = Nothing
findLineWithUserNum' (l : remLines) uNum =
    case userNumber l of
        Just luNum -> if luNum == uNum then (Just l) else findLineWithUserNum' remLines uNum
        _ -> findLineWithUserNum' remLines uNum
    
findLineWithUserNum :: Transformant -> Int -> Maybe Line
findLineWithUserNum transformant uNum = findLineWithUserNum' (transformata transformant) uNum

getCurrentRefLines :: Transformant -> [Line] -- NOT A TRANSFORMATION!!!
getCurrentRefLines transformant =
    let currLine = fromJust (curr transformant) in 
        map (fromJust . findLineWithUserNum transformant) (refLines currLine)

getUpdatedCurrentRefs :: Transformant -> [Int]
getUpdatedCurrentRefs = (map lineNumber) . getCurrentRefLines

resetUserNumbers :: [Line] -> [Line]
resetUserNumbers lns = map (\(Line n c j r _) -> Line n c j r (Just n)) lns