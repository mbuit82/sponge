module Core where

import Data.List

data Operator = Operator {
    operatorName :: String, 
    arity :: Int
} deriving Eq

impl :: Operator
impl = Operator "Implication" 2

data Sentence = Atom {atomName :: String}
              | OpNode {topOp :: Operator, args :: [Sentence]}

data Axiom = Axiom {axiomName :: String, axiomContent :: Sentence}

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