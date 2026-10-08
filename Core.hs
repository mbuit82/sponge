module Core where

data Operator = Operator {
    operatorName :: String,  -- what datalog will call the operator. what we actually care about form here on out. ideally user optionally picks this name out
    operatorSymbol :: String, -- what the user will write. relevant at tokenizer level. 
    arity :: Int
} deriving (Eq, Show) -- you've seriously fucked up if the three don't match, but I think only operatorName really needs to
-- instance Show Operator where
--     show op = operatorName op
-- instance Eq Operator where -- TODO: think about. I think it ultimately doesn't matter lol but still, think about. 
--     op1 == op2 = operatorName op1 == operatorName op2 -- datalog will throw an error if there is more than one constructor with the same name for the Sentence predicate so all good there

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

-- for proofs
data Line = Line {
    lineNumber :: Int,
    lineContent :: Sentence,
    justification :: String,
    refLines :: Maybe (Int, Int),
    userNumber :: Maybe Int -- the original line number the user used
} deriving Eq
-- a proof, inside haskell, is just a list of lines. That's all Haskell knows about proofs. (I used to have a proof type)
instance Show Line where
    show line = show (lineNumber line) ++ " " ++
                userNumberHuh (userNumber line) ++ ". " ++ 
                show (lineContent line) ++ "\t" ++ 
                "by " ++ justification line ++ refLinesHuh (refLines line)

refLinesHuh :: Maybe (Int, Int) -> String
refLinesHuh Nothing = []
refLinesHuh (Just (a, b)) = "(" ++ show a ++ ", " ++ show b ++ ")"

userNumberHuh :: Maybe Int -> String
userNumberHuh Nothing = "-"
userNumberHuh (Just n) = "(" ++ show n ++ ")"


-- RUNTIME CHECKS FOR LATER
aritiesCheck :: Sentence -> Bool
aritiesCheck (Atom a) = True
aritiesCheck (OpNode op args)
    | arity op == length args = all aritiesCheck args
    | otherwise = False

isWff :: Logic -> Sentence -> Bool
isWff logic (Atom _) = True
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
isInstance sentence (Atom _) = True
isInstance sentence (OpNode schemaOp schemaArgs) =
    case sentence of 
        Atom _ -> False
        OpNode sentOp sentArgs -> 
            schemaOp == sentOp && all (\p -> isInstance (fst p) (snd p)) (zip sentArgs schemaArgs)

haveSameStructure :: Sentence -> Sentence -> Bool
haveSameStructure s1 s2 = isInstance s1 s2 && isInstance s2 s1