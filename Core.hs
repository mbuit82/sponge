module Core where

import Data.List

data Operator = Operator {operatorName :: String, arity :: Int}

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

constructorToDatalog :: Operator -> String
constructorToDatalog op = 
    " | " ++ operatorName op ++ " {" ++ (intercalate ", " args) ++ "}"
    where 
        args = ["s" ++ show i ++ ": Sentence" | i <- [1 .. (arity op)]]
    
syntaxToDatalog :: Logic -> String
syntaxToDatalog logic = concatMap constructorToDatalog (operators logic)

-- headedByOperator :: Logic -> Sentence -> Bool
-- headedByOperator l s = (elem (rootLabel s) (map operatorName (operators l)))

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

makeDatalogLine :: Sentence -> String -> String -> String -> String -> String
makeDatalogLine sentence name n i j =
    "Line(" ++ 
        n ++ ", " ++
        schemaToDatalog sentence ++ ", " ++
        (if name == "_" then name else "\"" ++ name ++ "\"") ++ ", " ++ 
        i ++ ", " ++ 
        j ++ ", " ++ 
        "goal)"

axiomToDatalog :: Axiom -> String
axiomToDatalog axiom = 
    "Justified(n, goal) :- " ++ 
    makeDatalogLine (axiomContent axiom) (axiomName axiom) "n" "_" "_" ++ 
    ".\n"

axiomsToDatalog :: Logic -> String
axiomsToDatalog logic = concatMap axiomToDatalog (axioms logic)

conclusionToDatalog :: InferenceRule -> String 
conclusionToDatalog rule = 
    "Justified(n, goal) :- " ++ 
    makeDatalogLine (conclusion rule) (ruleName rule) "n" "i" jv
    where jv = case snd (premises rule) of 
            Nothing -> "_"
            Just _ -> "j"

premisesToDatalog :: InferenceRule -> [String] 
premisesToDatalog rule =
    concat [ [  v ++ " < n", 
                "Justified(" ++ v ++ ", goal)", 
                makeDatalogLine prem "_" v "_" "_"] 
            | (v, prem) <- zip ["i", "j"] premList]
    where premList = case snd (premises rule) of
                        Nothing -> [fst (premises rule)]
                        Just s -> [fst (premises rule), s]

inferenceRuleToDatalog :: InferenceRule -> String 
inferenceRuleToDatalog rule =
    intercalate ",\n\t" (concLine : premLines) ++ ".\n"
    where 
        concLine = conclusionToDatalog rule
        premLines = premisesToDatalog rule

inferenceRulesToDataog :: Logic -> String
inferenceRulesToDataog logic = concatMap inferenceRuleToDatalog (inferenceRules logic)

-- getOperatorWithName :: [Operator] -> String -> Maybe Operator
-- getOperatorWithName ops name = find ((== name) . operatorName) ops

isWff :: Sentence -> Bool
-- ideally, we don't have a need for this sentence. That's the magic of the type system!
isWff sentence =
    case sentence of
        Atom _ -> True
        OpNode op args -> if arity op == length args 
            then all isWff args
            else False

-- isAtom :: Logic -> Sentence -> Bool
-- isAtom l s = not headedByOperator l s

-- isInstance :: Logic -> Sentence -> Sentence -> Bool
-- -- the first Sentence is a sentence, second is a schema
-- -- need to think about naming for sentences/formulae
-- -- for now, assume everything is well-formed. 
-- isInstance logic sentence schema =
--     if isAtom logic schema
--     then True
--     else -- we know the schema is an operator
--         if rootLabel schema == 



--         cases schema of
--             Node nodeName children -> 

--     if (sentence rootLabel) == (schema rootLabel)
--     case schema of 
--         Node nodeName [] ->
--         Node nodeName [subTree] ->
        