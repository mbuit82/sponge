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


impl :: Operator
impl = Operator "Implication" "->" 2

specMinimalSmall :: Spec
specMinimalSmall = Spec {
    specName = "minimal_small",
    baseSystem = Nothing,
    newOperators = [impl],
    newAxioms = [
                    Axiom "Axiom2" (OpNode impl [Atom "P", OpNode impl [Atom "Q", Atom "P"]]),
                    Axiom "Axiom3" (OpNode impl [OpNode impl [Atom "P", Atom "Q"], OpNode impl [OpNode impl [Atom "P", OpNode impl [Atom "Q", Atom "R"]], OpNode impl [Atom "P", Atom "R"]]])],
    newInferenceRules = [InferenceRule "Modus Ponens" (Atom "P", Just (OpNode impl [Atom "P", Atom "Q"])) (Atom "Q")]
}

bot :: Operator
bot = Operator "Bot" "Bot" 0

specIntuitionisticSmall :: Spec
specIntuitionisticSmall = Spec {
    specName = "intuitionistic_small",
    baseSystem = Just specMinimalSmall,
    newOperators = [bot],
    newAxioms = [Axiom "Axiom4" (OpNode impl [OpNode impl [Atom "P", OpNode bot []], OpNode impl [Atom "P", Atom "Q"]])],
    newInferenceRules = []
}

specClassicalSmall :: Spec
specClassicalSmall = Spec {
    specName = "classical_small",
    baseSystem = Just specIntuitionisticSmall,
    newOperators = [],
    newAxioms = [Axiom "Axiom5" (OpNode impl [OpNode impl [OpNode impl [Atom "P", OpNode bot []], OpNode bot []], Atom "P"])],
    newInferenceRules = []
}

box :: Operator
box = Operator "Box" "Box" 1

specK :: Spec
specK = Spec {
    specName = "K",
    baseSystem = Just specClassicalSmall,
    newOperators = [box],
    newAxioms = [Axiom "K Axiom" (OpNode impl [OpNode box [OpNode impl [Atom "P", Atom "Q"]], OpNode impl [OpNode box [Atom "P"], OpNode box [Atom "Q"]]])],
    newInferenceRules = [InferenceRule "N" (Atom "P", Nothing) (OpNode box [Atom "P"])]
}