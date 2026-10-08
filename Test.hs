import Core
import Specs
import Proofs
import ToDatalog
import qualified Data.Map as Map

testEngines :: IO ()
testEngines = do
    compileDatalogEngine "minimal_small"
    compileDatalogEngine "intuitionistic_small"
    compileDatalogEngine "classical_small"
    compileDatalogEngine "minimal"
    compileDatalogEngine "intuitionistic"
    compileDatalogEngine "classical"
    compileDatalogEngine "K"

smallMpc = getLogic "minimal_small"
smallIpc = getLogic "intuitionistic_small"
smallCpc = getLogic "classical_small"

l1 = Line 1 (OpNode cond [OpNode cond [Atom "A", OpNode cond [Atom "A", Atom "A"]], OpNode cond [OpNode cond [Atom "A", OpNode cond [OpNode cond [Atom "A", Atom "A"], Atom "A"]], OpNode cond [Atom "A", Atom "A"]]]) "Axiom3" Nothing (Just 1)
l2 = Line 2 (OpNode cond [Atom "A", OpNode cond [Atom "A", Atom "A"]]) "Axiom2" Nothing (Just 2)
l3 = Line 3 (OpNode cond [OpNode cond [Atom "A", OpNode cond [OpNode cond [Atom "A", Atom "A"], Atom "A"]], OpNode cond [Atom "A", Atom "A"]]) "Modus Ponens" (Just (2, 1)) (Just 3)
l4 = Line 4 (OpNode cond [Atom "A", OpNode cond [OpNode cond [Atom "A", Atom "A"], Atom "A"]]) "Axiom2" Nothing (Just 4)
l5 = Line 5 (OpNode cond [Atom "A", Atom "A"]) "Modus Ponens" (Just (4, 3)) (Just 5)

testPureProof :: IO ()
testPureProof = compileDatalogProof "axiom1" (OpNode cond [Atom "A", Atom "A"]) smallMpc [l1, l2, l3, l4, l5]

testOffset :: IO ()
testOffset = compileDatalogProof "axiom1offset" (OpNode cond [Atom "A", Atom "A"]) smallMpc (applyOffsetToLines 10 [l1, l2, l3, l4, l5])

dl1 = Line 1 (OpNode bot []) "Assumption" Nothing (Just 1)
dl2 = Line 2 (OpNode cond [OpNode bot [], (OpNode cond [OpNode cond [Atom "A", OpNode bot []], OpNode bot []])]) "Axiom2" Nothing (Just 2)
dl3 = Line 3 (OpNode cond [OpNode cond [Atom "A", OpNode bot []], OpNode bot []]) "Modus Ponens" (Just (1, 2)) (Just 3)
dl4 = Line 4 (OpNode cond [OpNode cond [OpNode cond [Atom "A", OpNode bot []], OpNode bot []], Atom "A"]) "Axiom5" Nothing (Just 4)
dl5 = Line 5 (Atom "A") "Modus Ponens" (Just (3, 4)) (Just 5)

proofBeforeDeduction = [dl1, dl2, dl3, dl4, dl5]
proofAfterDeduction = useDeduction smallCpc (OpNode bot []) proofBeforeDeduction

testDeduction :: IO ()
testDeduction = compileDatalogProof "exfalso_deduction" (OpNode cond [OpNode bot [], Atom "A"]) smallCpc proofAfterDeduction


-- TEST: deduction twice
ddll1 = Line 1 (Atom "A") "Assumption" Nothing (Just 1)
ddll2 = Line 2 (OpNode cond [Atom "A", OpNode bot []]) "Assumption" Nothing (Just 2)
ddll3 = Line 3 (OpNode bot []) "Modus Ponens" (Just (1, 2)) (Just 3)
ddll4 = Line 4 (OpNode cond [OpNode bot [], (OpNode cond [OpNode cond [Atom "B", OpNode bot []], OpNode bot []])]) "Axiom2" Nothing (Just 4)
ddll5 = Line 5 (OpNode cond [OpNode cond [Atom "B", OpNode bot []], OpNode bot []]) "Modus Ponens" (Just (3, 4)) (Just 5)
ddll6 = Line 6 (OpNode cond [(OpNode cond [OpNode cond [Atom "B", OpNode bot []], OpNode bot []]), Atom "B"]) "Axiom5" Nothing (Just 6)
ddll7 = Line 7 (Atom "B") "Modus Ponens" (Just (5, 6)) (Just 7)

firstDeduction = (useDeduction smallCpc (Atom "A") [ddll1, ddll2, ddll3, ddll4, ddll5, ddll6, ddll7])

proofAfterDeductionTwice = useDeduction smallCpc (OpNode cond [Atom "A", OpNode bot []]) firstDeduction

testDeductionTwice :: IO ()
testDeductionTwice = compileDatalogProof "axiom4_deductiontwice" (OpNode cond [OpNode cond [Atom "A", OpNode bot []], OpNode cond [Atom "A", Atom "B"]]) smallCpc proofAfterDeductionTwice


testOps = [bot, box, cond]
parseTest0 = parse testOps "A" == Atom "A"
parseTest1 = parse testOps "Bot" == OpNode bot []
parseTest2 = parse testOps "(A -> A)" == OpNode cond [Atom "A", Atom "A"]
parseTest3 = parse testOps "(A -> C)" == OpNode cond [Atom "A", Atom "C"]
parseTest4 = parse testOps "(A -> Bot)" == OpNode cond [Atom "A", OpNode bot []]
parseTest5 = parse testOps "(A -> (B -> A))" == OpNode cond [Atom "A", OpNode cond [Atom "B", Atom "A"]]
parseTest6 = parse testOps "BoxA" == OpNode box [Atom "A"]
parseTest7 = parse testOps "Box(A)" == OpNode box [Atom "A"]
parseTest8 = parse testOps "(BoxA)" == OpNode box [Atom "A"]
parseTest9 = parse testOps "Box A" == OpNode box [Atom "A"]
parseTest10 = parse testOps "Box (A -> B)" == OpNode box [OpNode cond [Atom "A", Atom "B"]]
parseTest11 = parse testOps "Box(A -> B)" == OpNode box [OpNode cond [Atom "A", Atom "B"]]
parseTest12 = parse testOps "(A -> Box (A -> Bot))" == OpNode cond [Atom "A", OpNode box [OpNode cond [Atom "A", OpNode bot []]]]
parseTest13 = parse testOps "A -> A" == OpNode cond [Atom "A", Atom "A"]
parseTest14 = parse testOps "(A -> A) -> (A -> A)" == OpNode cond [OpNode cond [Atom "A", Atom "A"], OpNode cond [Atom "A", Atom "A"]]
parseTest15 = parse testOps "Box A -> B" == OpNode cond [OpNode box [Atom "A"], Atom "B"]
-- currently pass all up to here (expected, tolerable: we can parse the fully parenthesized fragment, and no top level)
parseTest16 = parse testOps "~A" == OpNode cond [Atom "A", OpNode bot []]
parseTest17 = parse testOps "~(A)" == OpNode cond [Atom "A", OpNode bot []]
parseTest18 = parse testOps "(~A)" == OpNode cond [Atom "A", OpNode bot []]
parseTest19 = parse testOps "~ A" == OpNode cond [Atom "A", OpNode bot []]
parseTest20 = parse testOps "(A -> (B -> ~ A))" == OpNode cond [Atom "A", OpNode cond [Atom "B", OpNode cond [Atom "A", OpNode bot []]]]
parseTest21 = parse testOps "(A -> B -> A)" == OpNode cond [Atom "A", OpNode cond [Atom "B", Atom "A"]]
parseTest22 = parse testOps "A -> B -> A" == OpNode cond [Atom "A", OpNode cond [Atom "B", Atom "A"]]
parseTest23 = parse testOps "A -> B -> ~A" == OpNode cond [Atom "A", OpNode cond [Atom "B", OpNode cond [Atom "A", OpNode bot []]]]



ht1 = getLineFromUser testOps "1. |- ((A -> (A -> A)) -> ((A -> ((A -> A) -> A)) -> (A -> A))) by Axiom3"
ht2 = getLineFromUser testOps "2. |- (A -> (A -> A))                                           by Axiom2"
ht3 = getLineFromUser testOps "3. |- ((A -> ((A -> A) -> A)) -> (A -> A))                      by Modus Ponens, 2 1"
ht4 = getLineFromUser testOps "4. |- (A -> ((A -> A) -> A))                                    by Axiom2"
ht5 = getLineFromUser testOps "5. |- (A -> A)                                                  by Modus Ponens, 4 3"

testLineParser :: IO ()
testLineParser = compileDatalogProof "axiom1" (parse testOps "(A -> A)") smallIpc [ht1, ht2, ht3, ht4, ht5]

htd1 = getLineFromUser testOps "1. |- Bot                                   by Assumption"
htd2 = getLineFromUser testOps "2. |- (Bot -> ((A -> Bot) -> Bot))   by Axiom2"
htd3 = getLineFromUser testOps "3. |- ((A -> Bot) -> Bot)                   by Modus Ponens, 1 2"
htd4 = getLineFromUser testOps "4. |- (((A -> Bot) -> Bot) -> A)            by Axiom5"
htd5 = getLineFromUser testOps "5. |- A                                     by Modus Ponens, 3 4"

-- proofAfterDeduction = useDeduction smallCpc (OpNode bot []) [htd1, htd2, htd3, htd4, htd5]

testParserWithDeduction :: IO ()
testParserWithDeduction = compileDatalogProof "exfalso_deduction" (parse testOps "(Bot -> A)") smallCpc (useDeduction smallCpc (OpNode bot []) [htd1, htd2, htd3, htd4, htd5])

asdf = parse testOps "(Bot -> ((A -> Bot) -> Bot) -> Bot)"

htdd1 = getLineFromUser testOps "1. |- A                             by Assumption"
htdd2 = getLineFromUser testOps "2. |- (A -> Bot)                    by Assumption"
htdd3 = getLineFromUser testOps "3. |- Bot                           by Modus Ponens, 1 2"
htdd4 = getLineFromUser testOps "4. |- (Bot -> ((B -> Bot) -> Bot))  by Axiom2"
htdd5 = getLineFromUser testOps "5. |- ((B -> Bot) -> Bot)           by Modus Ponens, 3 4"
htdd6 = getLineFromUser testOps "6. |- (((B -> Bot) -> Bot) -> B)    by Axiom5"
htdd7 = getLineFromUser testOps "7. |- B                             by Modus Ponens, 5 6"

deductionOnceLineParser = useDeduction smallCpc (parse testOps "A") [htdd1, htdd2, htdd3, htdd4, htdd5, htdd6, htdd7]
deductionTwiceLineParser = useDeduction smallCpc (parse testOps "(A -> Bot)") deductionOnceLineParser
testParserWithTwoDeductions = compileDatalogProof "axiom4_deductiontwice" (parse testOps "((A -> Bot) -> (A -> B))") smallCpc deductionTwiceLineParser