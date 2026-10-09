module Specs where

import Core

import qualified Data.Map as Map

data Spec = Spec
  { specName :: String,
    baseSystem :: Maybe Spec,
    newOperators :: [Operator],
    newDefinedOperators :: [DefinedOperator],
    newAxioms :: [Axiom],
    newInferenceRules :: [InferenceRule]
  }

getLogicFromSpec :: Spec -> Logic
getLogicFromSpec spec = 
    case (baseSystem spec) of
        Nothing ->  (Logic { 
                        logicName = specName spec, 
                        operators = newOperators spec, 
                        definedOperators = newDefinedOperators spec,
                        axioms = newAxioms spec, 
                        inferenceRules = newInferenceRules spec })
        Just base -> let baseLogic = getLogicFromSpec base in
                    (Logic { 
                        logicName = specName spec, 
                        operators = operators baseLogic ++ newOperators spec, 
                        definedOperators = definedOperators baseLogic ++ newDefinedOperators spec,
                        axioms = axioms baseLogic ++ newAxioms spec, 
                        inferenceRules = inferenceRules baseLogic ++ newInferenceRules spec })

makeLogicsDict :: [Spec] -> Map.Map String Logic
makeLogicsDict specs = Map.fromList (map (\s -> (specName s, getLogicFromSpec s)) specs)

logicsDict :: Map.Map String Logic
logicsDict = makeLogicsDict specsList -- specsList is at the bottom. Add any specs to it if you want to use them!

getLogic :: String -> Logic
getLogic logicName = logicsDict Map.! logicName



-- specs
specMinimalSmall :: Spec
specMinimalSmall = Spec {
    specName = "minimal_small",
    baseSystem = Nothing,
    newOperators = [cond], -- from core, since it plays role in deduction lemma thing
    newDefinedOperators = [],
    newAxioms = [   
        Axiom "Axiom2" (parse [cond] [] "P -> (Q -> P)"),
        Axiom "Axiom3" (parse [cond] [] "(P -> Q) -> ((P -> (Q -> R)) -> (P -> R))")],
    newInferenceRules = [InferenceRule "Modus Ponens" (parse [] [] "P", Just (parse [cond] [] "P -> Q")) (parse [] [] "Q")]
}

bot :: Operator
bot = Operator { operatorName = "Bot", operatorSymbol = "Bot", arity = 0}

specIntuitionisticSmall :: Spec
specIntuitionisticSmall = Spec {
    specName = "intuitionistic_small",
    baseSystem = Just specMinimalSmall,
    newOperators = [bot],
    newDefinedOperators = [neg],
    newAxioms = [Axiom "Axiom4" (parse [cond, bot] [] "(P -> Bot) -> (P -> Q)")],
    newInferenceRules = []
}

specClassicalSmall :: Spec
specClassicalSmall = Spec {
    specName = "classical_small",
    baseSystem = Just specIntuitionisticSmall,
    newOperators = [],
    newDefinedOperators = [], -- in theory you could add all the definitions here... ugh i don't wanna
    newAxioms = [Axiom "Axiom5" (parse [cond, bot] [neg] "((P -> Bot) -> Bot) -> P")],
    newInferenceRules = []
}

andOp :: Operator
andOp = Operator {operatorName = "And", operatorSymbol = "&", arity = 2}

orOp :: Operator
orOp = Operator "Or" "v" 2 -- can also just make operators like this (order follows order in above e.g. in andOp)

specMinimal :: Spec
specMinimal = Spec {
    specName = "minimal",
    baseSystem = Nothing,
    newOperators = [cond, andOp, orOp],
    newDefinedOperators = [],
    newAxioms = [   
        Axiom "Axiom2" (parse [cond] [] "P -> (Q -> P)"),
        Axiom "Axiom3" (parse [cond] [] "(P -> Q) -> ((P -> (Q -> R)) -> (P -> R))"),
        Axiom "And-EL" (parse [cond, andOp] [] "(P & Q) -> P"),
        Axiom "And-ER" (parse [cond, andOp] [] "(P & Q) -> Q"),
        Axiom "And-I" (parse [cond, andOp] [] "P -> (Q -> (P & Q))"),
        Axiom "Or-IL" (parse [cond, orOp] [] "P -> (P v Q)"),
        Axiom "Or-IR" (parse [cond, orOp] [] "Q -> (P v Q)"),
        Axiom "Or-E" (parse [cond, orOp] [] "(P -> R) -> ((Q -> R) -> ((P v Q) -> R))")],
    newInferenceRules = [InferenceRule "Modus Ponens" (parse [] [] "P", Just (parse [cond] [] "P -> Q")) (parse [] [] "Q")]
}

specIntuitionistic :: Spec
specIntuitionistic = Spec {
    specName = "intuitionistic",
    baseSystem = Just specMinimal,
    newOperators = [bot],
    newDefinedOperators = [neg],
    newAxioms = [Axiom "Explosion" (parse [cond, bot] [] "(P -> Bot) -> (P -> Q)")],
    newInferenceRules = []
}

specClassical :: Spec
specClassical = Spec {
    specName = "classical",
    baseSystem = Just specIntuitionistic,
    newOperators = [],
    newDefinedOperators = [],
    newAxioms = [Axiom "Excluded Middle" (parse [cond] [neg] "~ ~ P -> P")],
    newInferenceRules = []
}

box :: Operator
box = Operator "Box" "L" 1

specK :: Spec
specK = Spec {
    specName = "K",
    baseSystem = Just specClassical,
    newOperators = [box],
    newDefinedOperators = [diamond],
    newAxioms = [Axiom "K Axiom" (parse [cond, box] [] "L (P -> Q) -> (L P -> L Q)")],
    newInferenceRules = [InferenceRule "N" (parse [] [] "P", Nothing) (parse [box] [] "L P")]
}

-- the following axiomatization of linear logic comes from Hesselink 1990
linNull :: Operator
linNull = Operator "Null" "0" 0

linOr :: Operator
linOr = Operator "LinearDisjunction" "+" 2

linNeg :: Operator
linNeg = Operator "LinearNegation" "~" 1

specLinearIntensionalKernelHesselink :: Spec
specLinearIntensionalKernelHesselink = Spec {
    specName = "linear_intensional_kernel_Hesselink",
    baseSystem = Nothing,
    newOperators = [linNull, linOr, linNeg],
    newDefinedOperators = [lolli],
    newAxioms = [   
        Axiom "(2)" (parse [linNull, linOr, linNeg] [] "~A + A"),
        Axiom "(3)" (parse [linNull, linOr, linNeg] [] "~(A + B) + (B + A)"),
        Axiom "(4)" (parse [linNeg, linOr] [] "~((A + B) + C) + (A + (B + C))")],
    newInferenceRules = [
        InferenceRule "(0)Forward" (parse [] [] "A", Nothing) (parse [linNull, linOr] [] "0 + A"),
        InferenceRule "(0)Backward" (parse [linNull, linOr] [] "0 + A", Nothing) (parse [] [] "A"),
        InferenceRule "cut-rule" (parse [linOr] [] "A + B", Just (parse [linNeg, linOr] [] "~B + C")) (parse [linOr] [] "A + C")]
}

quest :: Operator
quest = Operator "Quest" "?" 1

linOps = [linNull, linOr, linNeg, quest] -- not as familiar with these so to be safe and avoid bugs am just gonna use this list lol

specLinearHesselink :: Spec
specLinearHesselink = Spec {
    specName = "linear_Hesselink",
    baseSystem = Just specLinearIntensionalKernelHesselink,
    newOperators = [quest],
    newDefinedOperators = [],
    newAxioms = [
        Axiom "(26)" (parse linOps [] "~0 + ?A"),
        Axiom "(27)" (parse linOps [] "~(?A + ?A) + ?A"),
        Axiom "(28)" (parse linOps [] "~?0"),
        Axiom "(29)" (parse linOps [] "~?(?A + ?B) + (?A + ?B)")],
    newInferenceRules = [
        InferenceRule "(25)Forward" (parse linOps [] "~A + ?B", Nothing) (parse linOps [] "~?A + ?B"),
        InferenceRule "(25)Backward" (parse linOps [] "~?A + ?B", Nothing) (parse linOps [] "~A + ?B")
    ]
}

specsList :: [Spec]
specsList = [   specMinimalSmall, specIntuitionisticSmall, specClassicalSmall, 
                specMinimal, specIntuitionistic, specClassical,
                specK,
                specLinearIntensionalKernelHesselink, specLinearHesselink
            ]









-- DEFINED OPERATORS PLAYGROUND
-- neg :: Operator
-- neg = Operator "Not" "~" 1

-- propagateFunc :: (Sentence -> Sentence) -> Sentence -> Sentence
-- propagateFunc func (OpNode op args) = (OpNode op (map func args))
-- propagateFunc func (Atom a) = Atom a

-- removeNot :: Sentence -> Sentence
-- removeNot (OpNode op [a])
--     | op == neg = (OpNode cond [removeNot a, OpNode bot []])
--     | otherwise = (OpNode op [removeNot a])
-- removeNot sent = propagateFunc removeNot sent -- not sure if this works? 

-- lolli :: Operator
-- lolli = Operator "Lollipop" "-o" 2

-- removeLollipop :: Sentence -> Sentence
-- removeLollipop (OpNode op [a, b])
--     | op == lolli = (OpNode linOr [OpNode linNeg [removeLollipop a], removeLollipop b])
--     | otherwise = (OpNode op (map removeLollipop [a, b]))
-- removeLollipop sent = propagateFunc removeLollipop sent

-- diamond :: Operator
-- diamond = Operator "Diamond" "M" 1

-- removeDiamond :: Sentence -> Sentence
-- removeDiamond (OpNode op [a])
--     | op == diamond = (OpNode neg [OpNode box [OpNode neg [a]]])
--     | otherwise = (OpNode op [removeDiamond a])
-- removeDiamond sent = propagateFunc removeDiamond sent



-- approach 2: just never make the defined operators into operators
-- what this encapsulates is that defined operators aren't really objects. They're more instructions. They're completely at the meta-level, so they should stay there. 
lolliDef :: [Sentence] -> Sentence
lolliDef = \[a, b] -> (OpNode linOr [OpNode linNeg [a], b]) -- partial, I think?

negDef :: [Sentence] -> Sentence
negDef = \[a] -> (OpNode cond [a, OpNode bot []])

diamondDef :: [Sentence] -> Sentence
diamondDef = \singleA -> negDef [OpNode box [negDef singleA]]

neg :: DefinedOperator
neg = DefinedOperator "Not" "~" 1 negDef

lolli :: DefinedOperator
lolli = DefinedOperator "Lollipop" "-o" 2 lolliDef

diamond :: DefinedOperator
diamond = DefinedOperator "Diamond" "M" 1 diamondDef

-- the current to-do is to change the tokenizing and parsing functions, and then change the tests. 
-- tokenize should now take a list of defined operators, and parse should too. 