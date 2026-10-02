-- NOTE: this is from when I thought of using Haskell instead of C. You can literally see where and why I stopped lol

-- This is what every file is going to need
import qualified Data.Map as Map
import Data.List
base :: Maybe String
axioms :: Map.Map String Sentence
inference_rules :: Map.Map String (List Sentence)


base = Nothing

data Sentence = SchemeVar Char | Bot | Implication Sentence Sentence -- We want Sentence to be extensible. Hm. Have some ideas in that Claude thing but tbh don't worry about that now

axioms = Map.fromList [
    ("Axiom1", (Implication (SchemeVar 'p') (SchemeVar 'p'))),
    ("Axiom2", (Implication (SchemeVar 'p') (Implication (SchemeVar 'q') (SchemeVar 'p')))),
    ("Axiom3", (Implication (Implication (SchemeVar 'p') (SchemeVar 'q')) (Implication (Implication (SchemeVar 'p') (Implication (SchemeVar 'q') (SchemeVar 'r'))) (Implication (SchemeVar 'p') (SchemeVar 'r'))))),
    ("Axiom4", (Implication (Implication (SchemeVar 'p') Bot) (Implication (SchemeVar 'p') (SchemeVar 'q'))))]

inference_rules = Map.singleton "Modus Ponens" [(SchemeVar 'p'), (Implication (SchemeVar 'p') (SchemeVar 'q')), (SchemeVar 'q')]

-- THIS is why we're using Haskell. This function. That's it. 
axiom_to_datalog :: Sentence -> String
axiom_to_datalog (SchemeVar char) = [char]
axiom_to_datalog Bot = "$Bot()"
axiom_to_datalog (Implication s1 s2) = concat ["$Implication(", axiom_to_datalog s1, ", ", axiom_to_datalog s2, ")"]
-- wait. No. This makes it not generic re num args. This is not good. We just want trees. We don't want specific data types. 

main = putStrLn (axiom_to_datalog (Map.findWithDefault Bot "Axiom1" axioms))
main2 = putStrLn (axiom_to_datalog (Map.findWithDefault Bot "Axiom2" axioms))
main3 = putStrLn (axiom_to_datalog (Map.findWithDefault Bot "Axiom3" axioms))