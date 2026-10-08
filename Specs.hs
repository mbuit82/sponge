module Specs where

import Core

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

bot :: Operator
bot = Operator "Bot" "Bot" 0

impl :: Operator
impl = Operator "Implication" "->" 2

specIntuitionistic :: Spec
specIntuitionistic = Spec {
    specName = "intuitionistic",
    baseSystem = Nothing,
    newOperators = [bot, impl],
    newAxioms = [
                    Axiom "Axiom2" (OpNode impl [Atom "P", OpNode impl [Atom "Q", Atom "P"]]),
                    Axiom "Axiom3" (OpNode impl [OpNode impl [Atom "P", Atom "Q"], OpNode impl [OpNode impl [Atom "P", OpNode impl [Atom "Q", Atom "R"]], OpNode impl [Atom "P", Atom "R"]]]),
                    Axiom "Axiom4" (OpNode impl [OpNode impl [Atom "P", OpNode bot []], OpNode impl [Atom "P", Atom "Q"]])],
    newInferenceRules = [InferenceRule "Modus Ponens" (Atom "P", Just (OpNode impl [Atom "P", Atom "Q"])) (Atom "Q")]
}

specClassical :: Spec
specClassical = Spec {
    specName = "classical",
    baseSystem = Just specIntuitionistic,
    newOperators = [],
    newAxioms = [Axiom "Axiom5" (OpNode impl [OpNode impl [OpNode impl [Atom "P", OpNode bot []], OpNode bot []], Atom "P"])],
    newInferenceRules = []
}

box :: Operator
box = Operator "Box" "Box" 1

specK :: Spec
specK = Spec {
    specName = "K",
    baseSystem = Just specClassical,
    newOperators = [box],
    newAxioms = [Axiom "K Axiom" (OpNode impl [OpNode box [OpNode impl [Atom "P", Atom "Q"]], OpNode impl [OpNode box [Atom "P"], OpNode box [Atom "Q"]]])],
    newInferenceRules = [InferenceRule "N" (Atom "P", Nothing) (OpNode box [Atom "P"])]
}