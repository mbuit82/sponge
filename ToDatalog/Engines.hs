module ToDatalog.Engines where

import Core
import Specs ( getLogic, logicsDict )
import ToDatalog.Utils

import Data.List
import System.IO
import qualified Data.Map as Map
import System.Environment (getArgs)
import System.Directory (createDirectoryIfMissing)

ruleSchemaToDatalog :: Sentence -> String
ruleSchemaToDatalog = formulaToDatalog True

axiomSchemaToDatalog :: Sentence -> String
axiomSchemaToDatalog = formulaToDatalog True . dashSingletonVars

constructorToDatalog :: Operator -> String
constructorToDatalog op = 
    " | " ++ operatorName op ++ " {" ++ (intercalate ", " args) ++ "}"
    where 
        args = ["s" ++ show i ++ ": Sentence" | i <- [1 .. (arity op)]]
    
syntaxToDatalog :: Logic -> String
syntaxToDatalog logic = concatMap constructorToDatalog (operators logic)

makeDatalogLine :: (Sentence -> String) -> Sentence -> String -> String -> String -> String -> String
makeDatalogLine contentFunc sentence name n i j =
    "Line(" ++ 
        n ++ ", " ++
        contentFunc sentence ++ ", " ++
        (if name == "_" then name else "\"" ++ name ++ "\"") ++ ", " ++ 
        i ++ ", " ++ 
        j ++ ")"

axiomToDatalog :: Axiom -> String
axiomToDatalog axiom = 
    "Justified(n) :- " ++ 
    makeDatalogLine axiomSchemaToDatalog (axiomContent axiom) (axiomName axiom) "n" "_" "_" ++ 
    ".\n"

axiomsToDatalog :: Logic -> String
axiomsToDatalog logic = concatMap axiomToDatalog (axioms logic)

conclusionToDatalog :: InferenceRule -> String 
conclusionToDatalog rule = 
    "Justified(n) :- " ++ 
    makeDatalogLine ruleSchemaToDatalog (conclusion rule) (ruleName rule) "n" "i" jv
    where jv = case snd (premises rule) of 
            Nothing -> "_"
            Just _ -> "j"

premisesToDatalog :: InferenceRule -> [String] 
premisesToDatalog rule =
    concat [ [  v ++ " < n", 
                "Justified(" ++ v ++ ")", 
                makeDatalogLine ruleSchemaToDatalog prem "_" v "_" "_"] 
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

inferenceRulesToDatalog :: Logic -> String
inferenceRulesToDatalog logic = concatMap inferenceRuleToDatalog (inferenceRules logic)

sharedDatalog :: String
sharedDatalog = unlines [
    "\n",
    ".decl Line(line_num: unsigned, line_content: Sentence, line_just: symbol, i: unsigned, j: unsigned)",
    ".decl Justified(n: unsigned)",
    ".decl Unjustified(n: unsigned)",
    ".decl UnjustifiedCount(c: number)",
    ".decl Goal(goal: Sentence)",
    ".decl Proven(f: Sentence)\n",
    "Unjustified(n) :- Line(n, _, _, _, _), !Justified(n).",
    "UnjustifiedCount(c) :- c = count : { Unjustified(_) }.",
    "Proven(f) :- Goal(f),\n\tLine(n, f, _, _, _),\n\tJustified(n),\n\tUnjustifiedCount(0).\n",
    ".output Unjustified\n.output Justified\n.output Proven\n"
    ]

compileDatalogEngine :: String -> IO ()
compileDatalogEngine logicName =
    -- I want to check that all axioms and inference rules are well-formed. 
    -- use the all function and the isWff function.
    -- Also here check that all inference rules have max 2 premises
    -- I think this ideally happens not here, but like in a check function. 
    -- for now I can run that check function here
    -- well like I want it to happen _before_ I apply all the transformations on proofs. Like it should be the _first_ thing that happens. 
    withFile ("datalog_engines/" ++ logicName ++ ".dl") WriteMode $ \h -> do
        hSetEncoding h utf8
        hPutStr h ".type Sentence = Atom {name: symbol}"
        hPutStr h (syntaxToDatalog logic)
        hPutStr h sharedDatalog
        hPutStr h (axiomsToDatalog logic)
        hPutStr h (inferenceRulesToDatalog logic)
    where 
        logic = getLogic logicName

makeLogicDirectories :: String -> IO ()
makeLogicDirectories logicName = do
    createDirectoryIfMissing False ("datalog_proofs/" ++ logicName)
    createDirectoryIfMissing False ("hand_proofs/" ++ logicName)

main :: IO ()
main = let logics = (Map.keys logicsDict) in
        do 
            mapM_ compileDatalogEngine logics
            mapM_ makeLogicDirectories logics