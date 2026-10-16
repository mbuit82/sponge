module Defs.Specs (getLogic, logicNames) where

import Core
import Parse.Sentences

import Defs.Operators
import Defs.Axioms
import Defs.Rules

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
                        
extendWithAxioms :: Spec -> [Axiom] -> String -> Spec
extendWithAxioms baseSpec newAxs newName =
    Spec newName (Just baseSpec) [] [] newAxs []

-- Add any specs to here if you want to use them!
specsList :: [Spec]
specsList = [   specMinimalSmall, specIntuitionisticSmall, specClassicalSmall, 
                specMinimal, specIntuitionistic, specClassical,
                specK, 
                specD, specKT, specKB, 
                specS4, specS5,
                specSE, 
                specS42, specS44,
                specS43, specK43,
                specKW, specKH,
                specKD4, specKD45,
                specLinearIntensionalKernelHesselink, specLinearHesselink
            ]
    

-- specs
-- see Defs.Operators for definitions of operators and Defs.Axioms for Axioms, and Defs.Rules for inference rules
specMinimalSmall :: Spec
specMinimalSmall = Spec {
    specName = "minimal_small",
    baseSystem = Nothing,
    newOperators = [cond, bot], -- from core, since it plays role in deduction lemma thing
    newDefinedOperators = [],
    newAxioms = [axiom2, axiom3],
    newInferenceRules = [modusPonens]
}

specIntuitionisticSmall :: Spec
specIntuitionisticSmall = extendWithAxioms specMinimalSmall [axiom4] "intuitionistic_small"

specClassicalSmall :: Spec
specClassicalSmall = extendWithAxioms specIntuitionisticSmall [axiom5] "classical_small"

specMinimal :: Spec
specMinimal = Spec {
    specName = "minimal",
    baseSystem = Nothing,
    newOperators = [cond, andOp, orOp, bot],
    newDefinedOperators = [bicond, neg],
    newAxioms = [simp, frege, andEL, andER, andI, orIL, orIR, orE],
    newInferenceRules = [modusPonens]
}

specIntuitionistic :: Spec
specIntuitionistic = extendWithAxioms specMinimal [explosion] "intuitionistic"

specClassical :: Spec
specClassical = extendWithAxioms specIntuitionistic [lem] "classical"

specK :: Spec
specK = Spec {
    specName = "K",
    baseSystem = Just specClassical,
    newOperators = [box],
    newDefinedOperators = [diamond],
    newAxioms = [kAxiom],
    newInferenceRules = [necessitation]
}

specD :: Spec
specD = extendWithAxioms specK [dAxiom] "D"

specKT :: Spec
specKT = extendWithAxioms specK [tAxiom] "KT"

specKB :: Spec
specKB = extendWithAxioms specK [brouwerscheAxiom] "KB"

specS4 :: Spec
specS4 = extendWithAxioms specKT [fourAxiom] "S4"

specS5 :: Spec
specS5 = extendWithAxioms specS4 [brouwerscheAxiom] "S5"

specSE :: Spec
specSE = extendWithAxioms specKB [elsewhereAxiom] "SE"

specS42 :: Spec
specS42 = extendWithAxioms specS4 [convergenceAxiom] "S4.2"

specS44 :: Spec
specS44 = extendWithAxioms specS4 [gettierAxiom] "S4.4"

specS43 :: Spec
specS43 = extendWithAxioms specS4 [d1Axiom] "S4.3"

specK43 :: Spec
specK43 = extendWithAxioms specK [fourAxiom, d2Axiom] "K4.3"

specKW :: Spec
specKW = extendWithAxioms specK [glAxiom] "KW"

specKH :: Spec
specKH = extendWithAxioms specK [hAxiom] "KH"

specKD4 :: Spec
specKD4 = extendWithAxioms specD [fourAxiom] "KD4"

specKD45 :: Spec
specKD45 = extendWithAxioms specKD4 [fiveAxiom] "KD45"

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

makeLogicsDict :: [Spec] -> Map.Map String Logic
makeLogicsDict specs = Map.fromList (map (\s -> (specName s, getLogicFromSpec s)) specs)

-- this map is not to be exported. use the below anywhere this could be needed instead. 
logicsDict :: Map.Map String Logic
logicsDict = makeLogicsDict specsList 

-- the only things exported from here
getLogic :: String -> Logic
getLogic logicName = case logicsDict Map.!? logicName of
    Nothing -> error (logicName ++ " not in available logics right now")
    Just logic -> logic

logicNames :: [String]
logicNames = Map.keys logicsDict
