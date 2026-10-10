module Specs where

import Core
import Proofs

import Data.Maybe
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
    newAxioms = [   
        Axiom "Axiom2" (parse [cond] [] "P -> (Q -> P)"),
        Axiom "Axiom3" (parse [cond] [] "(P -> Q) -> ((P -> (Q -> R)) -> (P -> R))")],
    newInferenceRules = [InferenceRule "Modus Ponens" (parse [] [] "P", Just (parse [cond] [] "P -> Q")) (parse [] [] "Q")],
    newDerivedRules = Map.empty
}

bot :: Operator
bot = Operator { operatorName = "Bot", operatorSymbol = "Bot", arity = 0}

specIntuitionisticSmall :: Spec
specIntuitionisticSmall = Spec {
    specName = "intuitionistic_small",
    baseSystem = Just specMinimalSmall,
    newOperators = [bot],
    newDefinedOperators = [],
    newAxioms = [Axiom "Axiom4" (parse [cond, bot] [] "(P -> Bot) -> (P -> Q)")],
    newInferenceRules = [],
    newDerivedRules = Map.empty
}

specClassicalSmall :: Spec
specClassicalSmall = Spec {
    specName = "classical_small",
    baseSystem = Just specIntuitionisticSmall,
    newOperators = [],
    newDefinedOperators = [], -- in theory you could add all the definitions here... ugh i don't wanna
    newAxioms = [Axiom "Axiom5" (parse [cond, bot] [] "((P -> Bot) -> Bot) -> P")],
    newInferenceRules = [],
    newDerivedRules = Map.empty
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
    newInferenceRules = [InferenceRule "Modus Ponens" (parse [] [] "P", Just (parse [cond] [] "P -> Q")) (parse [] [] "Q")],
    newDerivedRules = Map.fromList [
        ("And Elim L", andElimLTransformation), 
        ("And Elim R", andElimRTransformation), 
        ("Adjunction", adjunctionTransformation)]
}

negDef :: [Sentence] -> Sentence
negDef = \[a] -> (OpNode cond [a, OpNode bot []])

neg :: DefinedOperator
neg = DefinedOperator "Not" "~" 1 negDef

specIntuitionistic :: Spec
specIntuitionistic = Spec {
    specName = "intuitionistic",
    baseSystem = Just specMinimal,
    newOperators = [bot],
    newDefinedOperators = [neg],
    newAxioms = [Axiom "Explosion" (parse [cond, bot] [] "Bot -> P")],
    newInferenceRules = [],
    newDerivedRules = Map.empty
}

specClassical :: Spec
specClassical = Spec {
    specName = "classical",
    baseSystem = Just specIntuitionistic,
    newOperators = [],
    newDefinedOperators = [],
    newAxioms = [Axiom "Excluded Middle" (parse [cond] [neg] "~ ~ P -> P")],
    newInferenceRules = [],
    newDerivedRules = Map.empty
}

box :: Operator
box = Operator "Box" "L" 1

diamondDef :: [Sentence] -> Sentence
diamondDef = \singleA -> negDef [OpNode box [negDef singleA]]

diamond :: DefinedOperator
diamond = DefinedOperator "Diamond" "M" 1 diamondDef

specK :: Spec
specK = Spec {
    specName = "K",
    baseSystem = Just specClassical,
    newOperators = [box],
    newDefinedOperators = [diamond],
    newAxioms = [Axiom "K Axiom" (parse [cond, box] [] "L (P -> Q) -> (L P -> L Q)")],
    newInferenceRules = [InferenceRule "N" (parse [] [] "P", Nothing) (parse [box] [] "L P")],
    newDerivedRules = Map.empty
}

-- the following axiomatization of linear logic comes from Hesselink 1990
linNull :: Operator
linNull = Operator "Null" "0" 0

linOr :: Operator
linOr = Operator "LinearDisjunction" "+" 2

linNeg :: Operator
linNeg = Operator "LinearNegation" "~" 1

lolliDef :: [Sentence] -> Sentence
lolliDef = \[a, b] -> (OpNode linOr [OpNode linNeg [a], b])

lolli :: DefinedOperator
lolli = DefinedOperator "Lollipop" "-o" 2 lolliDef

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
    ],
    newDerivedRules = Map.empty
}

specsList :: [Spec]
specsList = [   specMinimalSmall, specIntuitionisticSmall, specClassicalSmall, 
                specMinimal, specIntuitionistic, specClassical,
                specK,
                specLinearIntensionalKernelHesselink, specLinearHesselink
            ]


andElimLTransformation :: Transformation
andElimLTransformation transformant =
    [Line n (applySubst "PandQ -> P" [("PandQ", lineContent pandqLine), ("P", lineContent currLine)]) "And-EL" [] Nothing,
     Line (n + 1) (lineContent currLine) "Modus Ponens" [lineNumber pandqLine, n] (userNumber currLine)]
    where 
        applySubst = getApplySubstFromTransformant transformant
        currLine = fromJust (curr transformant)
        n = lineNumber (currLine) + (offset transformant)
        [pandqLine] = getCurrentRefLines transformant

andElimRTransformation :: Transformation
andElimRTransformation transformant =
    [Line n (applySubst "PandQ -> Q" [("PandQ", lineContent pandqLine), ("Q", lineContent currLine)]) "And-ER" [] Nothing,
     Line (n + 1) (lineContent currLine) "Modus Ponens" [lineNumber pandqLine, n] (userNumber currLine)]
    where 
        applySubst = getApplySubstFromTransformant transformant
        currLine = fromJust (curr transformant)
        n = lineNumber (currLine) + (offset transformant)
        [pandqLine] = getCurrentRefLines transformant

adjunctionTransformation :: Transformation
adjunctionTransformation transformant =
    [
        Line n (applySubst "P -> (Q -> (P & Q))" [("P", lineContent pLine), ("Q", lineContent qLine)]) "And-I" [] Nothing,
        Line (n + 1) (applySubst "Q -> (P & Q)" [("P", lineContent pLine), ("Q", lineContent qLine)]) "Modus Ponens" [lineNumber pLine, n] Nothing,
        Line (n + 2) (applySubst "P & Q" [("P", lineContent pLine), ("Q", lineContent qLine)]) "Modus Ponens" [lineNumber qLine, n +1] (userNumber currLine)
    ]
    where 
        applySubst = getApplySubstFromTransformant transformant
        currLine = fromJust (curr transformant)
        n = lineNumber (currLine) + (offset transformant)
        [pLine, qLine] = getCurrentRefLines transformant

-- -- for Or Intro L and Or Intro R, we need to be able to add sentences to the additional material
-- orIntroLTransformation :: Transformation
-- orIntroLTransformation transformant =
--     [
--         Line n (OpNode cond [])
--     ]
--     where 
--         currLine = fromJust (curr transformant)
--         n = lineNumber (currLine) + (offset transformant)
--         [pLine] = getCurrentRefLines transformant

orElimTransformation :: Transformation
orElimTransformation transformant =
    [
        Line n (applySubst "PR -> (QR -> (PorQ -> R))" [("PR", pr), ("QR", qr), ("PorQ", porq), ("R", r)]) "Or-E" [] Nothing,
        Line (n + 1) (applySubst "QR -> (PorQ -> R)" [("QR", qr), ("PorQ", porq), ("R", r)]) "Modus Ponens" [lineNumber prLine, n] Nothing,
        Line (n + 2) (applySubst "PorQ -> R" [("PorQ", porq), ("R", r)]) "Modus Ponens" [lineNumber qrLine, n + 1] Nothing,
        Line (n + 3) r "Modus Ponens" [lineNumber porqLine, n + 2] (userNumber currLine)
    ]
    where 
        applySubst = getApplySubstFromTransformant transformant
        pr = lineContent prLine
        qr = lineContent qrLine
        porq = lineContent porqLine
        r = lineContent currLine
        currLine = fromJust (curr transformant)
        n = lineNumber (currLine) + (offset transformant)
        [prLine, qrLine, porqLine] = getCurrentRefLines transformant