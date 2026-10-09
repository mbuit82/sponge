module Specs where

import Core

import qualified Data.Map as Map

data Spec = Spec
  { specName :: String,
    baseSystem :: Maybe Spec,
    newOperators :: [Operator],
    newAxioms :: [Axiom],
    newInferenceRules :: [InferenceRule]
  }

getLogicFromSpec :: Spec -> Logic
getLogicFromSpec spec = 
    case (baseSystem spec) of
        Nothing ->  (Logic { 
                        logicName = specName spec, 
                        operators = newOperators spec, 
                        axioms = newAxioms spec, 
                        inferenceRules = newInferenceRules spec })
        Just base -> let baseLogic = getLogicFromSpec base in
                    (Logic { 
                        logicName = specName spec, 
                        operators = operators baseLogic ++ newOperators spec, 
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
    newAxioms = [   Axiom "Axiom2" (parse [cond] "P -> (Q -> P)"),
                    Axiom "Axiom3" (parse [cond] "(P -> Q) -> ((P -> (Q -> R)) -> (P -> R))")],
    newInferenceRules = [InferenceRule "Modus Ponens" (parse [] "P", Just (parse [cond] "P -> Q")) (parse [] "Q")]
}

bot :: Operator
bot = Operator "Bot" "Bot" 0

specIntuitionisticSmall :: Spec
specIntuitionisticSmall = Spec {
    specName = "intuitionistic_small",
    baseSystem = Just specMinimalSmall,
    newOperators = [bot],
    newAxioms = [Axiom "Axiom4" (parse [cond, bot] "(P -> Bot) -> (P -> Q)")],
    newInferenceRules = []
}

specClassicalSmall :: Spec
specClassicalSmall = Spec {
    specName = "classical_small",
    baseSystem = Just specIntuitionisticSmall,
    newOperators = [],
    newAxioms = [Axiom "Axiom5" (parse [cond, bot] "((P -> Bot) -> Bot) -> P")],
    newInferenceRules = []
}

andOp :: Operator
andOp = Operator "And" "&" 2

orOp :: Operator
orOp = Operator "Or" "v" 2

specMinimal :: Spec
specMinimal = Spec {
    specName = "minimal",
    baseSystem = Nothing,
    newOperators = [cond, andOp, orOp],
    newAxioms = [   Axiom "Axiom2" (parse [cond] "P -> (Q -> P)"),
                    Axiom "Axiom3" (parse [cond] "(P -> Q) -> ((P -> (Q -> R)) -> (P -> R))"),
                    Axiom "And-EL" (parse [cond, andOp] "(P & Q) -> P"),
                    Axiom "And-ER" (parse [cond, andOp] "(P & Q) -> Q"),
                    Axiom "And-I" (parse [cond, andOp] "P -> (Q -> (P & Q))"),
                    Axiom "Or-IL" (parse [cond, orOp] "P -> (P v Q)"),
                    Axiom "Or-IR" (parse [cond, orOp] "Q -> (P v Q)"),
                    Axiom "Or-E" (parse [cond, orOp] "(P -> R) -> ((Q -> R) -> ((P v Q) -> R))")],
    newInferenceRules = [InferenceRule "Modus Ponens" (parse [] "P", Just (parse [cond] "P -> Q")) (parse [] "Q")]
}

specIntuitionistic :: Spec
specIntuitionistic = Spec {
    specName = "intuitionistic",
    baseSystem = Just specMinimal,
    newOperators = [bot],
    newAxioms = [Axiom "Explosion" (parse [cond, bot] "(P -> Bot) -> (P -> Q)")],
    newInferenceRules = []
}

specClassical :: Spec
specClassical = Spec {
    specName = "classical",
    baseSystem = Just specIntuitionistic,
    newOperators = [],
    newAxioms = [Axiom "Excluded Middle" (parse [cond, bot, orOp] "P v (P -> Bot)")],
    newInferenceRules = []
}

box :: Operator
box = Operator "Box" "Box" 1

specK :: Spec
specK = Spec {
    specName = "K",
    baseSystem = Just specClassical,
    newOperators = [box],
    newAxioms = [Axiom "K Axiom" (parse [cond, box] "Box (P -> Q) -> (Box P -> Box Q)")],
    newInferenceRules = [InferenceRule "N" (parse [] "P", Nothing) (parse [box] "Box P")]
}

specsList :: [Spec]
specsList = [   specMinimalSmall, specIntuitionisticSmall, specClassicalSmall, 
                specMinimal, specIntuitionistic, specClassical,
                specK
            ]