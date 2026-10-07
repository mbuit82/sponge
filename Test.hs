import Core
import Specs
import Proofs
import Data.List

testEngines :: IO ()
testEngines = do
    compileDatalogEngine specIntuitionistic
    compileDatalogEngine specClassical
    compileDatalogEngine specK

ipc = getLogic specIntuitionistic
cpc = getLogic specClassical

l1 = Line 1 (OpNode impl [OpNode impl [Atom "A", OpNode impl [Atom "A", Atom "A"]], OpNode impl [OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]], OpNode impl [Atom "A", Atom "A"]]]) "Axiom3" Nothing (Just 1)
l2 = Line 2 (OpNode impl [Atom "A", OpNode impl [Atom "A", Atom "A"]]) "Axiom2" Nothing (Just 2)
l3 = Line 3 (OpNode impl [OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]], OpNode impl [Atom "A", Atom "A"]]) "Modus Ponens" (Just (2, 1)) (Just 3)
l4 = Line 4 (OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]]) "Axiom2" Nothing (Just 4)
l5 = Line 5 (OpNode impl [Atom "A", Atom "A"]) "Modus Ponens" (Just (4, 3)) (Just 5)

testPureProof :: IO ()
testPureProof = compileDatalogProof "axiom1" (OpNode impl [Atom "A", Atom "A"]) ipc [l1, l2, l3, l4, l5]

testOffset :: IO ()
testOffset = compileDatalogProof "axiom1offset" (OpNode impl [Atom "A", Atom "A"]) ipc (applyOffsetToLines 10 [l1, l2, l3, l4, l5])

dl1 = Line 1 (OpNode bot []) "Assumption" Nothing (Just 1)
dl2 = Line 2 (OpNode impl [OpNode bot [], (OpNode impl [OpNode impl [Atom "A", OpNode bot []], OpNode bot []])]) "Axiom2" Nothing (Just 2)
dl3 = Line 3 (OpNode impl [OpNode impl [Atom "A", OpNode bot []], OpNode bot []]) "Modus Ponens" (Just (1, 2)) (Just 3)
dl4 = Line 4 (OpNode impl [OpNode impl [OpNode impl [Atom "A", OpNode bot []], OpNode bot []], Atom "A"]) "Axiom5" Nothing (Just 4)
dl5 = Line 5 (Atom "A") "Modus Ponens" (Just (3, 4)) (Just 5)

proofBeforeDeduction = [dl1, dl2, dl3, dl4, dl5]
proofAfterDeduction = useDeduction cpc (OpNode bot []) proofBeforeDeduction

testDeduction :: IO ()
testDeduction = compileDatalogProof "exfalso_deduction" (OpNode impl [OpNode bot [], Atom "A"]) cpc proofAfterDeduction


-- TEST: deduction twice
ddll2 = Line 1 (Atom "A") "Assumption" Nothing (Just 1)
ddll1 = Line 2 (OpNode impl [Atom "A", OpNode bot []]) "Assumption" Nothing (Just 2)
ddll3 = Line 3 (OpNode bot []) "Modus Ponens" (Just (1, 2)) (Just 3)
ddll4 = Line 4 (OpNode impl [OpNode bot [], (OpNode impl [OpNode impl [Atom "B", OpNode bot []], OpNode bot []])]) "Axiom2" Nothing (Just 4)
ddll5 = Line 5 (OpNode impl [OpNode impl [Atom "B", OpNode bot []], OpNode bot []]) "Modus Ponens" (Just (3, 4)) (Just 5)
ddll6 = Line 6 (OpNode impl [(OpNode impl [OpNode impl [Atom "B", OpNode bot []], OpNode bot []]), Atom "B"]) "Axiom5" Nothing (Just 6)
ddll7 = Line 7 (Atom "B") "Modus Ponens" (Just (5, 6)) (Just 7)

firstDeduction = (useDeduction cpc (Atom "A") [ddll1, ddll2, ddll3, ddll4, ddll5, ddll6, ddll7])

proofAfterDeductionTwice = useDeduction cpc (OpNode impl [Atom "A", OpNode bot []]) firstDeduction

testDeductionTwice :: IO ()
testDeductionTwice = compileDatalogProof "axiom4_deductiontwice" (OpNode impl [OpNode impl [Atom "A", OpNode bot []], OpNode impl [Atom "A", Atom "B"]]) cpc proofAfterDeductionTwice


testOps = [bot, box, impl]
parseTest0 = parseSentence testOps "A" == Atom "A"
parseTest1 = parseSentence testOps "Bot" == OpNode bot []
parseTest2 = parseSentence testOps "(A -> A)" == OpNode impl [Atom "A", Atom "A"]
parseTest3 = parseSentence testOps "(A -> C)" == OpNode impl [Atom "A", Atom "C"]
parseTest4 = parseSentence testOps "(A -> Bot)" == OpNode impl [Atom "A", OpNode bot []]
parseTest5 = parseSentence testOps "(A -> (B -> A))" == OpNode impl [Atom "A", OpNode impl [Atom "B", Atom "A"]]
parseTest6 = parseSentence testOps "BoxA" == OpNode box [Atom "A"]
parseTest7 = parseSentence testOps "Box(A)" == OpNode box [Atom "A"]
parseTest8 = parseSentence testOps "(BoxA)" == OpNode box [Atom "A"]
parseTest9 = parseSentence testOps "Box A" == OpNode box [Atom "A"]
parseTest10 = parseSentence testOps "Box (A -> B)" == OpNode box [OpNode impl [Atom "A", Atom "B"]]
parseTest11 = parseSentence testOps "Box(A -> B)" == OpNode box [OpNode impl [Atom "A", Atom "B"]]
parseTest12 = parseSentence testOps "(A -> Box (A -> Bot))" == OpNode impl [Atom "A", OpNode box [OpNode impl [Atom "A", OpNode bot []]]]
parseTest13 = parseSentence testOps "A -> A" == OpNode impl [Atom "A", Atom "A"]
parseTest14 = parseSentence testOps "(A -> A) -> (A -> A)" == OpNode impl [OpNode impl [Atom "A", Atom "A"], OpNode impl [Atom "A", Atom "A"]]
parseTest15 = parseSentence testOps "Box A -> B" == OpNode impl [OpNode box [Atom "A"], Atom "B"]
-- currently pass all up to here (expected, tolerable: we can parseSentence the fully parenthesized fragment, and no top level)
parseTest16 = parseSentence testOps "~A" == OpNode impl [Atom "A", OpNode bot []]
parseTest17 = parseSentence testOps "~(A)" == OpNode impl [Atom "A", OpNode bot []]
parseTest18 = parseSentence testOps "(~A)" == OpNode impl [Atom "A", OpNode bot []]
parseTest19 = parseSentence testOps "~ A" == OpNode impl [Atom "A", OpNode bot []]
parseTest20 = parseSentence testOps "(A -> (B -> ~ A))" == OpNode impl [Atom "A", OpNode impl [Atom "B", OpNode impl [Atom "A", OpNode bot []]]]
parseTest21 = parseSentence testOps "(A -> B -> A)" == OpNode impl [Atom "A", OpNode impl [Atom "B", Atom "A"]]
parseTest22 = parseSentence testOps "A -> B -> A" == OpNode impl [Atom "A", OpNode impl [Atom "B", Atom "A"]]
parseTest23 = parseSentence testOps "A -> B -> ~A" == OpNode impl [Atom "A", OpNode impl [Atom "B", OpNode impl [Atom "A", OpNode bot []]]]

parseTests :: IO ()
parseTests = do
    print parseTest0
    print parseTest1
    print parseTest2
    print parseTest3
    print parseTest4
    print parseTest5
    print parseTest6
    print parseTest7
    print parseTest8
    print parseTest9
    print parseTest10
    print parseTest11
    print parseTest12
    print parseTest13
    print parseTest14
    print parseTest15
    print parseTest16
    print parseTest17
    print parseTest18
    print parseTest19
    print parseTest20
    print parseTest21
    print parseTest22


ht1 = getLineFromUser testOps "1. |- ((A -> (A -> A)) -> ((A -> ((A -> A) -> A)) -> (A -> A))) by Axiom3"
ht2 = getLineFromUser testOps "2. |- (A -> (A -> A))                                           by Axiom2"
ht3 = getLineFromUser testOps "3. |- ((A -> ((A -> A) -> A)) -> (A -> A))                      by Modus Ponens, 2 1"
ht4 = getLineFromUser testOps "4. |- (A -> ((A -> A) -> A))                                    by Axiom2"
ht5 = getLineFromUser testOps "5. |- (A -> A)                                                  by Modus Ponens, 4 3"

testLineParser :: IO ()
testLineParser = compileDatalogProof "axiom1" (parseSentence testOps "(A -> A)") ipc [ht1, ht2, ht3, ht4, ht5]

htd1 = getLineFromUser testOps "1. |- Bot                                   by Assumption"
htd2 = getLineFromUser testOps "2. |- (Bot -> ((A -> Bot) -> Bot))   by Axiom2"
htd3 = getLineFromUser testOps "3. |- ((A -> Bot) -> Bot)                   by Modus Ponens, 1 2"
htd4 = getLineFromUser testOps "4. |- (((A -> Bot) -> Bot) -> A)            by Axiom5"
htd5 = getLineFromUser testOps "5. |- A                                     by Modus Ponens, 3 4"

-- proofAfterDeduction = useDeduction cpc (OpNode bot []) [htd1, htd2, htd3, htd4, htd5]

testParserWithDeduction :: IO ()
testParserWithDeduction = compileDatalogProof "exfalso_deduction" (parseSentence testOps "(Bot -> A)") cpc (useDeduction cpc (OpNode bot []) [htd1, htd2, htd3, htd4, htd5])

asdf = parseSentence testOps "(Bot -> ((A -> Bot) -> Bot) -> Bot)"

htdd1 = getLineFromUser testOps "1. |- A                             by Assumption"
htdd2 = getLineFromUser testOps "2. |- (A -> Bot)                    by Assumption"
htdd3 = getLineFromUser testOps "3. |- Bot                           by Modus Ponens, 1 2"
htdd4 = getLineFromUser testOps "4. |- (Bot -> ((B -> Bot) -> Bot))  by Axiom2"
htdd5 = getLineFromUser testOps "5. |- ((B -> Bot) -> Bot)           by Modus Ponens, 3 4"
htdd6 = getLineFromUser testOps "6. |- (((B -> Bot) -> Bot) -> B)    by Axiom5"
htdd7 = getLineFromUser testOps "7. |- B                             by Modus Ponens, 5 6"

deductionOnceLineParser = useDeduction cpc (parseSentence testOps "A") [htdd1, htdd2, htdd3, htdd4, htdd5, htdd6, htdd7]
deductionTwiceLineParser = useDeduction cpc (parseSentence testOps "(A -> Bot)") deductionOnceLineParser
testParserWithTwoDeductions = compileDatalogProof "axiom4_deductiontwice" (parseSentence testOps "((A -> Bot) -> (A -> B))") cpc deductionTwiceLineParser