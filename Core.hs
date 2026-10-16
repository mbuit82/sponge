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

cond :: Operator
cond = Operator "Conditional" "->" 2

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

type Substitution = [(String, Sentence)] -- largely just a shortcut

data Axiom = Axiom {axiomName :: String, axiomContent :: Sentence} deriving (Eq, Show, Read) -- low key not necessary
prettyPrintAxiom :: Axiom -> String
prettyPrintAxiom axiom =
    axiomName axiom ++ ": |- " ++ prettyPrintSentence (axiomContent axiom)

data InferenceRule = InferenceRule {
    ruleName :: String,
    premises :: (Sentence, Maybe Sentence), -- can have max two (bc of how Datalog is set up)
    conclusion :: Sentence} deriving (Eq, Show, Read)

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

-- I have a feeling this isn't the best definition; I don't think it's the moral one
isSubLogicByAxioms :: Logic -> Logic -> Bool
isSubLogicByAxioms logic1 logic2 =
    and (map (\op -> elem op (operators logic2)) (operators logic1)) &&
    and (map (\rl -> elem rl (inferenceRules logic2)) (inferenceRules logic1)) &&
    and (map (\ax -> elem ax (axioms logic2)) (axioms logic1))






data Transformant = Transformant {  transformata :: [Line], 
                                    curr :: Maybe Line, 
                                    transformanda :: [Line], 
                                    offset :: Int,
                                    transformantLogic :: Logic}

type Transformation = Transformant -> [Line]

type DerivedRule = (String, Transformation)

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

-- finds the first occurrence. This is taken advantage of in the strengthening derived rule
findLineWithUserNum' :: [Line] -> Int -> Maybe Line
findLineWithUserNum' [] _ = Nothing
findLineWithUserNum' (l : remLines) uNum =
    case userNumber l of
        Just luNum -> if luNum == uNum then (Just l) else findLineWithUserNum' remLines uNum
        _ -> findLineWithUserNum' remLines uNum
    
findLineWithUserNum :: Transformant -> Int -> Maybe Line
findLineWithUserNum transformant = findLineWithUserNum' (transformata transformant)

findLineWithContent' :: [Line] -> Sentence -> Maybe Line
findLineWithContent' [] _ = Nothing
findLineWithContent' (l : remLines) sent =
    if lineContent l == sent 
        then Just l
        else findLineWithContent' remLines sent

findLineWithContent :: Transformant -> Sentence -> Maybe Line
findLineWithContent transformant = findLineWithContent' (transformata transformant)


getCurrentRefLines :: Transformant -> [Line] -- NOT A TRANSFORMATION!!!
getCurrentRefLines transformant =
    let currLine = fromJust (curr transformant) in 
        map (fromJust . findLineWithUserNum transformant) (refLines currLine)

getUpdatedCurrentRefs :: Transformant -> [Int]
getUpdatedCurrentRefs = (map lineNumber) . getCurrentRefLines

resetUserNumbers :: [Line] -> [Line]
resetUserNumbers lns = map (\(Line n c j r _) -> Line n c j r (Just n)) lns

getNEmbeddedAntecedents :: Int -> Sentence -> [Sentence]
getNEmbeddedAntecedents 0 _ = []
getNEmbeddedAntecedents n (OpNode op [arg1, arg2])
    | op == cond = arg1 : getNEmbeddedAntecedents (n-1) arg2
    | otherwise = error "can only get N antecedents on a conditional"

getNthConsequent :: Int -> Sentence -> Sentence
getNthConsequent 0 sent = sent
getNthConsequent n (OpNode op [arg1, arg2])
    | op == cond = getNthConsequent (n-1) arg2
    | otherwise = error "can only get Nth consequent on a conditional"
getNthConsequent n sent = 
    error ("dunno what went wrong. debugging info: getNthConsequent, " ++ show n ++ ", " ++ show sent)

getEmbeddedAntecedentsUpTo :: Sentence -> Sentence -> [Sentence]
getEmbeddedAntecedentsUpTo stopSent sent
    | sent == stopSent = []
    | otherwise = case sent of
        Atom a -> error ("supposed to have reached stopSent " ++ show stopSent ++ " but never did?")
        (OpNode op [arg1, arg2]) -> 
            if op == cond
                then arg1 : getEmbeddedAntecedentsUpTo stopSent arg2
                else error "can only get all antecedents on a chain of conditionals"

makeChain :: [Sentence] -> Sentence -> Sentence
makeChain [] consq = consq
makeChain (p:rem) consq = OpNode cond [p, makeChain rem consq]