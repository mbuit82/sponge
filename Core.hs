module Core where

import Data.Maybe
import Data.List
import qualified Data.Map as Map
import Data.Functor.Identity

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
        _ -> error "haven't done how to do n-ary operators yet (printing out an n-ary defined operator)"

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
} deriving Eq -- a proof, inside haskell, is just a list of lines. That's all Haskell knows about proofs. (I used to have a proof type)
-- keeping this here in case it's ever relevant
prettyPrintLine :: Line -> String
prettyPrintLine (Line lNum c j rfs uNum) = 
    show lNum ++ " " ++
    userNumberHuh uNum ++ ". " ++ 
    prettyPrintSentence c ++ "\t" ++ 
    "by " ++ j ++ show rfs
instance Show Line where
    show = prettyPrintLine

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

-- presupposes isInstance (ie will crash otherwise)
getVarMap' :: Sentence -> Sentence -> [(String, Sentence)]
-- the first Sentence is a sentence, second is a schema
-- need to think about naming for sentences/formulae
getVarMap' sentence (Atom a) = [(a, sentence)]
getVarMap' sentence (OpNode schemaOp schemaArgs) =
    case sentence of 
        Atom _ -> error msg
        OpNode sentOp sentArgs -> 
            if schemaOp == sentOp 
                then concatMap (\p -> getVarMap' (fst p) (snd p)) (zip sentArgs schemaArgs)
                else error msg
    where 
        msg = ("looks like sentence " ++ show sentence ++ " isn't an instance of " ++ show (OpNode schemaOp schemaArgs))

getVarMap :: Sentence -> Sentence -> Map.Map String Sentence
getVarMap sent schema = Map.fromList (getVarMap' sent schema)

instantiateVar :: Map.Map String Sentence -> String -> Sentence
instantiateVar varMap str = case varMap Map.!? str of
    Nothing -> error ("variable " ++ str ++ " is not in the substitution " ++ show varMap)
    Just sent -> sent


-- I have a feeling this isn't the best definition; I don't think it's the moral one
isSubLogicByAxioms :: Logic -> Logic -> Bool
isSubLogicByAxioms logic1 logic2 =
    and (map (\op -> elem op (operators logic2)) (operators logic1)) &&
    and (map (\rl -> elem rl (inferenceRules logic2)) (inferenceRules logic1)) &&
    and (map (\ax -> elem ax (axioms logic2)) (axioms logic1))



-- are used for conditionals in strengthening and K derived rules, but are more general processes so leaving here
getNEmbeddedAntecedents :: Operator -> Int -> Sentence -> [Sentence]
getNEmbeddedAntecedents op 0 _ = []
getNEmbeddedAntecedents op n (OpNode op' [arg1, arg2])
    | op' == op = arg1 : getNEmbeddedAntecedents op (n-1) arg2
    | otherwise = error "can only get N antecedents on a conditional"

getNthConsequent :: Operator -> Int -> Sentence -> Sentence
getNthConsequent op 0 sent = sent
getNthConsequent op n (OpNode op' [arg1, arg2])
    | op' == op = getNthConsequent op (n-1) arg2
    | otherwise = error "can only get Nth consequent on a conditional"
getNthConsequent op n sent = 
    error ("dunno what went wrong. debugging info: getNthConsequent, " ++ show n ++ ", " ++ show sent)

getEmbeddedAntecedentsUpTo :: Operator -> Sentence -> Sentence -> [Sentence]
getEmbeddedAntecedentsUpTo op stopSent sent
    | sent == stopSent = []
    | otherwise = case sent of
        Atom a -> error ("supposed to have reached stopSent " ++ show stopSent ++ " but never did?")
        (OpNode op' [arg1, arg2]) -> 
            if op' == op
                then arg1 : getEmbeddedAntecedentsUpTo op stopSent arg2
                else error "can only get all antecedents on a chain of conditionals"
        _ -> error ("supposed to have reached stopSent " ++ show stopSent ++ " but never did?")

makeChain :: Operator -> [Sentence] -> Sentence -> Sentence
makeChain op [] consq = consq
makeChain op (p:rem) consq = OpNode op [p, makeChain op rem consq]



-- PROOFTREES BASICS
data ProofTree = ProofTree {
    pfContent :: Sentence,
    pfJustification :: String,
    subProofs :: [ProofTree]
} deriving (Show, Eq)

applyOverTreeM :: Monad m => (ProofTree -> m ProofTree) -> ProofTree -> m ProofTree
applyOverTreeM func (ProofTree pfc pfj spfs) = do
    spfsUpdated <- mapM (applyOverTreeM func) spfs
    func (ProofTree pfc pfj spfsUpdated)

applyOverTree :: (ProofTree -> ProofTree) -> ProofTree -> ProofTree
applyOverTree func = runIdentity . applyOverTreeM (Identity . func)

findLineWithLNum :: [Line] -> Int -> Line
findLineWithLNum [] _ = error "no line with that number"
findLineWithLNum (ln:lns) lNum
    | lineNumber ln == lNum = ln
    | otherwise = findLineWithLNum lns lNum

linesToProofTree' :: [Line] -> Line -> ProofTree
linesToProofTree' [] _ = error "empty proof"
linesToProofTree' lns currLine = 
    ProofTree 
        (lineContent currLine) 
        (justification currLine) 
        (map ((linesToProofTree' lns) . (findLineWithLNum lns)) (refLines currLine))

linesToProofTree :: [Line] -> ProofTree
linesToProofTree lns = 
    case (reverse lns) of
        [] -> error "empty proof"
        (lastLn:remLns) ->
            linesToProofTree' (lastLn:remLns) lastLn

proofTreeToLines' :: Int -> ProofTree -> [Line]
-- don't believe this commented out is necessary because of Haskell lazy evaluation
-- proofTreeToLines' nextUseableRef (ProofTree pfc pfj []) =
--     [Line nextUseableRef pfc pfj [] (Just nextUseableRef)]
proofTreeToLines' nextUseableRef (ProofTree pfc pfj spfs) =
    let recs = referencesCase (nextUseableRef + 1) spfs in
        Line nextUseableRef pfc pfj (map (\lns -> lineNumber (lns !! 0)) recs) (Just nextUseableRef) : concat recs
        -- reversal at the end conserves user line order I think

referencesCase :: Int -> [ProofTree] -> [[Line]]
referencesCase baseInt [] = []
referencesCase baseInt (ref1:remRefs) =
    let firstRefRes = proofTreeToLines' baseInt ref1 in
    firstRefRes : referencesCase (baseInt + length firstRefRes) remRefs

invertNum :: Int -> Int -> Int
invertNum lenPf n = lenPf + 1 - n

invertLineNumbers :: Int -> Line -> Line
invertLineNumbers lenPf (Line lNum c j rfs _) = 
    Line (invertNum lenPf lNum) c j (map (invertNum lenPf) rfs) (Just (invertNum lenPf lNum))

proofTreeToLines :: ProofTree -> [Line]
proofTreeToLines pftree = 
    let revLines' = proofTreeToLines' 1 pftree in
        reverse (map (invertLineNumbers (length (revLines'))) revLines')