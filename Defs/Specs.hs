module Defs.Specs where

import Defs.Operators
import Defs.Axioms
import Defs.Rules
import Core

import qualified Data.Map as Map

data Spec = Spec
  { specName :: String,
    baseSystem :: Maybe Spec,
    newOperators :: [Operator],
    newDefinedOperators :: [DefinedOperator],
    newAxioms :: [Axiom],
    newInferenceRules :: [InferenceRule],
    newDerivedRules :: Map.Map String Transformation
  }

getLogicFromSpec :: Spec -> Logic
getLogicFromSpec spec = 
    case (baseSystem spec) of
        Nothing ->  (Logic { 
                        logicName = specName spec, 
                        operators = newOperators spec, 
                        definedOperators = newDefinedOperators spec,
                        axioms = newAxioms spec, 
                        inferenceRules = newInferenceRules spec,
                        derivedRules = newDerivedRules spec })
        Just base -> let baseLogic = getLogicFromSpec base in
                    (Logic { 
                        logicName = specName spec, 
                        operators = operators baseLogic ++ newOperators spec, 
                        definedOperators = definedOperators baseLogic ++ newDefinedOperators spec,
                        axioms = axioms baseLogic ++ newAxioms spec, 
                        inferenceRules = inferenceRules baseLogic ++ newInferenceRules spec,
                        derivedRules = Map.union (derivedRules baseLogic) (newDerivedRules spec) })

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
    newAxioms = [axiom2, axiom3],
    newInferenceRules = [modusPonens],
    newDerivedRules = Map.empty
}

specIntuitionisticSmall :: Spec
specIntuitionisticSmall = Spec {
    specName = "intuitionistic_small",
    baseSystem = Just specMinimalSmall,
    newOperators = [bot],
    newDefinedOperators = [],
    newAxioms = [axiom4],
    newInferenceRules = [],
    newDerivedRules = Map.empty
}

specClassicalSmall :: Spec
specClassicalSmall = Spec {
    specName = "classical_small",
    baseSystem = Just specIntuitionisticSmall,
    newOperators = [],
    newDefinedOperators = [], -- in theory you could add all the definitions here... ugh i don't wanna
    newAxioms = [axiom5],
    newInferenceRules = [],
    newDerivedRules = Map.empty
}

specMinimal :: Spec
specMinimal = Spec {
    specName = "minimal",
    baseSystem = Nothing,
    newOperators = [cond, andOp, orOp],
    newDefinedOperators = [bicond],
    newAxioms = [axiom2, axiom3, andEL, andER, andI, orIL, orIR, orE],
    newInferenceRules = [modusPonens],
    newDerivedRules = Map.fromList [
        andElimLDerivedRule, andElimRDerivedRule, adjunctionDerivedRule, 
        orElimDerivedRule, 
        hypSyllDerivedRule, modusTollens]
}

specIntuitionistic :: Spec
specIntuitionistic = Spec {
    specName = "intuitionistic",
    baseSystem = Just specMinimal,
    newOperators = [bot],
    newDefinedOperators = [neg],
    newAxioms = [explosion],
    newInferenceRules = [],
    newDerivedRules = Map.empty
}

specClassical :: Spec
specClassical = Spec {
    specName = "classical",
    baseSystem = Just specIntuitionistic,
    newOperators = [],
    newDefinedOperators = [],
    newAxioms = [lem],
    newInferenceRules = [], -- you should add disjunctive syllogism
    newDerivedRules = Map.empty
}

specK :: Spec
specK = Spec {
    specName = "K",
    baseSystem = Just specClassical,
    newOperators = [box],
    newDefinedOperators = [diamond],
    newAxioms = [kAxiom],
    newInferenceRules = [necessitation],
    newDerivedRules = Map.empty
}

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
        InferenceRule "cut-rule" (parse [linOr] [] "A + B", Just (parse [linNeg, linOr] [] "~B + C")) (parse [linOr] [] "A + C")],
    newDerivedRules = Map.empty
}

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
    ],
    newDerivedRules = Map.empty
}

specsList :: [Spec]
specsList = [   specMinimalSmall, specIntuitionisticSmall, specClassicalSmall, 
                specMinimal, specIntuitionistic, specClassical,
                specK,
                specLinearIntensionalKernelHesselink, specLinearHesselink
            ]