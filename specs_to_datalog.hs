import qualified Data.Map as Map
import Data.Tree
import Data.List
import System.IO

type Sentence = Tree String
-- helper for writing trees bc leaves are uglyyyy
-- once I get a front end I won't need this tho
lf :: String -> Sentence 
lf name = Node name []

data Operator = Operator {operatorName :: String, arity :: Int}

data Axiom = Axiom {axiomName :: String, axiomContent :: Sentence}

data InferenceRule = InferenceRule {
    ruleName :: String,
    premises :: [Sentence], 
    conclusion :: Sentence}

data Logic = Logic
  { logicName :: String,
    operators :: [Operator],
    axioms :: [Axiom],
    inferenceRules :: [InferenceRule]
  }

operatorToDatalog :: Operator -> String
operatorToDatalog op = 
    " | " ++ operatorName op ++ " {" ++ (intercalate ", " args) ++ "}"
    where 
        args = ["s" ++ show i ++ ": Sentence" | i <- [1 .. (arity op)]]
    
syntaxToDatalog :: Logic -> String
syntaxToDatalog logic =
    ".type Sentence = Atom {name: symbol}" ++ 
    concatMap operatorToDatalog (operators logic) ++ 
    "\n"

formulaToDatalog :: Bool -> Logic -> Sentence -> String
formulaToDatalog varBool logic sentence =
    if not (elem (rootLabel sentence) (map operatorName (operators logic)))
    then if varBool
            then rootLabel sentence
            else "$Atom(\"" ++ (rootLabel sentence) ++ "\")"
    else "$" ++ (rootLabel sentence) ++ "(" ++ argsStr ++ ")"
    where argsStr = intercalate ", " 
            (map (formulaToDatalog varBool logic) (subForest sentence))

schemaToDatalog :: Logic -> Sentence -> String
schemaToDatalog = formulaToDatalog True

makeDatalogLine :: Logic -> Sentence -> String -> String -> String -> String -> String
makeDatalogLine logic sentence name n i j =
    "Line(" ++ 
        n ++ ", " ++
        schemaToDatalog logic sentence ++ ", " ++
        (if name == "_" then name else "\"" ++ name ++ "\"") ++ ", " ++ 
        i ++ ", " ++ 
        j ++ ", " ++ 
        "goal)"

axiomToDatalog :: Logic -> Axiom -> String
axiomToDatalog logic axiom = 
    "Justified(n, goal) :- " ++ 
    makeDatalogLine logic (axiomContent axiom) (axiomName axiom) "n" "_" "_" ++ 
    ".\n"

axiomsToDatalog :: Logic -> String
axiomsToDatalog logic = concatMap (axiomToDatalog logic) (axioms logic)

conclusionToDatalog :: Logic -> InferenceRule -> String 
conclusionToDatalog logic rule = 
    "Justified(n, goal) :- " ++ 
    makeDatalogLine logic (conclusion rule) (ruleName rule) "n" "i" jv
    where jv = case premises rule of 
            [_] -> "_"
            [_, _] -> "j"
            _ -> error "should be one or two premises for an inference rule for now"

premisesToDatalog :: Logic -> InferenceRule -> [String] 
premisesToDatalog logic rule =
    concat [ [  v ++ " < n", 
                "Justified(" ++ v ++ ", goal)", 
                makeDatalogLine logic prem "_" v "_" "_"] 
            | (v, prem) <- zip ["i", "j"] (premises rule)]

inferenceRuleToDatalog :: Logic -> InferenceRule -> String 
inferenceRuleToDatalog logic rule =
    intercalate ",\n\t" (concLine : premLines) ++ ".\n"
    where 
        concLine = conclusionToDatalog logic rule
        premLines = premisesToDatalog logic rule

inferenceRulesToDataog :: Logic -> String
inferenceRulesToDataog logic = concatMap (inferenceRuleToDatalog logic) (inferenceRules logic)


-- FROM HERE BELOW, SPEC STUFF

data Spec = Spec
  { specName :: String,
    baseSystem :: Maybe Spec,
    newOperators :: [Operator],
    newAxioms :: [Axiom],
    newInferenceRules :: [InferenceRule]
  }

getLogic :: Spec -> Logic
getLogic spec = 
    case (baseSystem spec) of
        Nothing ->  (Logic { 
                        logicName = specName spec, 
                        operators = newOperators spec, 
                        axioms = newAxioms spec, 
                        inferenceRules = newInferenceRules spec })
        Just base -> let baseLogic = getLogic base in
                    (Logic { 
                        logicName = specName spec, 
                        operators = operators baseLogic ++ newOperators spec, 
                        axioms = axioms baseLogic ++ newAxioms spec, 
                        inferenceRules = inferenceRules baseLogic ++ newInferenceRules spec })

sharedDatalog :: String
sharedDatalog = unlines [
    ".type Goal = ToProve {s: Sentence}\n",
    ".decl Line(line_num: unsigned, line_content: Sentence, line_just: symbol, i: unsigned, j: unsigned, goal: Goal)",
    ".decl Justified(n: unsigned, goal: Goal)",
    ".decl Unjustified(n: unsigned, goal: Goal)",
    ".decl UnjustifiedCount(c: number, goal: Goal)",
    ".decl Claim(goal: Goal)",
    ".decl Proven(f: Sentence)\n",
    "Unjustified(n, goal) :- Line(n, _, _, _, _, goal), !Justified(n, goal).",
    "UnjustifiedCount(c, goal) :- Claim(goal), c = count : { Unjustified(_, goal) }.",
    "Proven(f) :- Claim($ToProve(f)),\n\tLine(n, f, _, _, _, $ToProve(f)),\n\tJustified(n, $ToProve(f)),\n\tUnjustifiedCount(0, $ToProve(f)).\n",
    ".output Unjustified\n.output Justified\n.output Proven\n"
    ]

compileDatalogEngine :: Spec -> IO ()
compileDatalogEngine spec =
    withFile ("datalog_engines/" ++ specName spec ++ ".dl") WriteMode $ \h -> do
        hSetEncoding h utf8
        hPutStr h (syntaxToDatalog logic)
        hPutStr h sharedDatalog
        hPutStr h (axiomsToDatalog logic)
        hPutStr h (inferenceRulesToDataog logic)
    where 
        logic = getLogic spec

specIntuitionistic :: Spec
specIntuitionistic = Spec {
    specName = "intuitionistic",
    baseSystem = Nothing,
    newOperators = [Operator "Bot" 0, Operator "Implication" 2],
    newAxioms = [
        Axiom "Axiom1" (Node "Implication" [lf "P", lf "P"]),
        Axiom "Axiom2" (Node "Implication" [lf "P", Node "Implication" [lf "Q", lf "P"]]),
        Axiom "Axiom3" (Node "Implication" [Node "Implication" [lf "P", lf "Q"], Node "Implication" [Node "Implication" [lf "P", Node "Implication" [lf "Q", lf "R"]], Node "Implication" [lf "P", lf "R"]]]),
        Axiom "Axiom4" (Node "Implication" [Node "Implication" [lf "P", lf "Bot"], Node "Implication" [lf "P", lf "Q"]])],
    newInferenceRules = [InferenceRule "Modus Ponens" [lf "P", Node "Implication" [lf "P", lf "Q"]] (lf "Q")]
}

specClassical :: Spec
specClassical = Spec {
    specName = "classical",
    baseSystem = Just specIntuitionistic,
    newOperators = [],
    newAxioms = [Axiom "Axiom5" (Node "Implication" [Node "Implication" [Node "Implication" [lf "P", lf "Bot"], lf "Bot"], lf "P"])],
    newInferenceRules = []
}

specK :: Spec
specK = Spec {
    specName = "K",
    baseSystem = Just specClassical,
    newOperators = [Operator "Box" 1],
    newAxioms = [Axiom "K Axiom" (Node "Implication" [Node "Box" [Node "Implication" [lf "P", lf "Q"]], Node "Implication" [Node "Box" [lf "P"], Node "Box" [lf "Q"]]])],
    newInferenceRules = [InferenceRule "N" [lf "P"] (Node "Box" [lf "P"])]
}


-- FROM HERE BELOW, PROOFS

data Line = Line {
    lineNumber :: Int,
    lineContent :: Sentence,
    justification :: (String, Int, Int)
}

data Proof = Proof {
    proofName :: String, -- I don't NEED to add this (yet) technically. 
    proofGoal :: Sentence,
    proofLogic :: Logic,
    proofContent :: [Line]
}

sentenceToDatalog :: Logic -> Sentence -> String
sentenceToDatalog = formulaToDatalog False

lineToDatalog :: Proof -> Line -> String
lineToDatalog proof line = 
    let (justificationText, i, j) = justification line in
        "Line(" ++ show (lineNumber line) ++ ", " ++
        sentenceToDatalog (proofLogic proof) (lineContent line) ++ ", " ++ 
        "\"" ++ justificationText ++ "\", " ++
        show i ++ ", " ++ 
        show j ++ ", " ++
        "$ToProve(" ++ sentenceToDatalog (proofLogic proof) (proofGoal proof) ++ 
        -- (proofName proof) ++ -- would need more than just turning this on
        ")).\n"

proofToDatalog :: Proof -> String
proofToDatalog proof =
    "Claim($ToProve(" ++ 
    sentenceToDatalog (proofLogic proof) (proofGoal proof) ++ 
    ")).\n\n" ++
    concatMap (lineToDatalog proof) (proofContent proof)
    
compileDatalogProof :: Proof -> IO ()
compileDatalogProof proof =
    withFile ("autogenerated_proofs/" ++ proofName proof ++ ".dl") WriteMode $ \h -> do
        hSetEncoding h utf8
        hPutStr h ("#include \"../datalog_engines/" ++ (logicName (proofLogic proof)) ++ ".dl\"\n\n")
        hPutStr h (proofToDatalog proof)

l1 = Line 1 (Node "Implication" [Node "Implication" [lf "A", Node "Implication" [lf "A", lf "A"]], Node "Implication" [Node "Implication" [lf "A", Node "Implication" [Node "Implication" [lf "A", lf "A"], lf "A"]], Node "Implication" [lf "A", lf "A"]]]) ("Axiom3", 0, 0)
l2 = Line 2 (Node "Implication" [lf "A", Node "Implication" [lf "A", lf "A"]]) ("Axiom2", 0, 0)
l3 = Line 3 (Node "Implication" [Node "Implication" [lf "A", Node "Implication" [Node "Implication" [lf "A", lf "A"], lf "A"]], Node "Implication" [lf "A", lf "A"]]) ("Modus Ponens", 2, 1)
l4 = Line 4 (Node "Implication" [lf "A", Node "Implication" [Node "Implication" [lf "A", lf "A"], lf "A"]]) ("Axiom2", 0, 0)
l5 = Line 5 (Node "Implication" [lf "A", lf "A"]) ("Modus Ponens", 4, 3)

axiom1Proof = Proof "axiom1" (Node "Implication" [lf "A", lf "A"]) (getLogic specIntuitionistic) [l1, l2, l3, l4, l5]