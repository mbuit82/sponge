import Core
import Specs
import Proofs
import Data.List

testEngines :: IO ()
testEngines = do
    compileDatalogEngine specIntuitionistic
    compileDatalogEngine specClassical
    compileDatalogEngine specK

l1 = Line 1 (OpNode impl [OpNode impl [Atom "A", OpNode impl [Atom "A", Atom "A"]], OpNode impl [OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]], OpNode impl [Atom "A", Atom "A"]]]) "Axiom3" Nothing (Just 1)
l2 = Line 2 (OpNode impl [Atom "A", OpNode impl [Atom "A", Atom "A"]]) "Axiom2" Nothing (Just 2)
l3 = Line 3 (OpNode impl [OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]], OpNode impl [Atom "A", Atom "A"]]) "Modus Ponens" (Just (2, 1)) (Just 3)
l4 = Line 4 (OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]]) "Axiom2" Nothing (Just 4)
l5 = Line 5 (OpNode impl [Atom "A", Atom "A"]) "Modus Ponens" (Just (4, 3)) (Just 5)

testPureProof :: IO ()
testPureProof = compileDatalogProof "axiom1" (OpNode impl [Atom "A", Atom "A"]) (getLogic specIntuitionistic) [l1, l2, l3, l4, l5]

testOffset :: IO ()
testOffset = compileDatalogProof "axiom1offset" (OpNode impl [Atom "A", Atom "A"]) (getLogic specIntuitionistic) (applyOffsetToLines 10 [l1, l2, l3, l4, l5])

dl1 = Line 1 (OpNode bot []) "Assumption" Nothing (Just 1)
dl2 = Line 2 (OpNode impl [OpNode bot [], (OpNode impl [OpNode impl [Atom "A", OpNode bot []], OpNode bot []])]) "Axiom2" Nothing (Just 2)
dl3 = Line 3 (OpNode impl [OpNode impl [Atom "A", OpNode bot []], OpNode bot []]) "Modus Ponens" (Just (1, 2)) (Just 3)
dl4 = Line 4 (OpNode impl [OpNode impl [OpNode impl [Atom "A", OpNode bot []], OpNode bot []], Atom "A"]) "Axiom5" Nothing (Just 4)
dl5 = Line 5 (Atom "A") "Modus Ponens" (Just (3, 4)) (Just 5)

proofBeforeDeduction = [dl1, dl2, dl3, dl4, dl5]
proofAfterDeduction = useDeduction (OpNode bot []) proofBeforeDeduction

testDeduction :: IO ()
testDeduction = compileDatalogProof "exfalso_deduction" (OpNode impl [OpNode bot [], Atom "A"]) (getLogic specClassical) proofAfterDeduction


-- TEST: deduction twice
ddll1 = Line 1 (Atom "A") "Assumption" Nothing (Just 1)
ddll2 = Line 2 (OpNode impl [Atom "A", OpNode bot []]) "Assumption" Nothing (Just 2)
ddll3 = Line 3 (OpNode bot []) "Modus Ponens" (Just (1, 2)) (Just 3)
ddll4 = Line 4 (OpNode impl [OpNode bot [], (OpNode impl [OpNode impl [Atom "B", OpNode bot []], OpNode bot []])]) "Axiom2" Nothing (Just 4)
ddll5 = Line 5 (OpNode impl [OpNode impl [Atom "B", OpNode bot []], OpNode bot []]) "Modus Ponens" (Just (3, 4)) (Just 5)
ddll6 = Line 6 (OpNode impl [(OpNode impl [OpNode impl [Atom "B", OpNode bot []], OpNode bot []]), Atom "B"]) "Axiom5" Nothing (Just 6)
ddll7 = Line 7 (Atom "B") "Modus Ponens" (Just (5, 6)) (Just 7)

firstDeduction = (useDeduction (Atom "A") [ddll1, ddll2, ddll3, ddll4, ddll5, ddll6, ddll7])

proofAfterDeductionTwice = useDeduction (OpNode impl [Atom "A", OpNode bot []]) firstDeduction

testDeductionTwice :: IO ()
testDeductionTwice = compileDatalogProof "axiom4_deductiontwice" (OpNode impl [OpNode impl [Atom "A", OpNode bot []], OpNode impl [Atom "A", Atom "B"]]) (getLogic specClassical) proofAfterDeductionTwice


testOps = [bot, box, impl]
parseTest0 = parse testOps "A" == Atom "A"
parseTest1 = parse testOps "Bot" == OpNode bot []
parseTest2 = parse testOps "(A -> A)" == OpNode impl [Atom "A", Atom "A"]
parseTest3 = parse testOps "(A -> C)" == OpNode impl [Atom "A", Atom "C"]
parseTest4 = parse testOps "(A -> Bot)" == OpNode impl [Atom "A", OpNode bot []]
parseTest5 = parse testOps "(A -> (B -> A))" == OpNode impl [Atom "A", OpNode impl [Atom "B", Atom "A"]]
parseTest6 = parse testOps "BoxA" == OpNode box [Atom "A"]
parseTest7 = parse testOps "Box(A)" == OpNode box [Atom "A"]
parseTest8 = parse testOps "(BoxA)" == OpNode box [Atom "A"]
parseTest9 = parse testOps "Box A" == OpNode box [Atom "A"]
parseTest10 = parse testOps "Box (A -> B)" == OpNode box [OpNode impl [Atom "A", Atom "B"]]
parseTest11 = parse testOps "Box(A -> B)" == OpNode box [OpNode impl [Atom "A", Atom "B"]]
parseTest12 = parse testOps "(A -> Box (A -> Bot))" == OpNode impl [Atom "A", OpNode box [OpNode impl [Atom "A", OpNode bot []]]]
parseTest13 = parse testOps "A -> A" == OpNode impl [Atom "A", Atom "A"]
parseTest14 = parse testOps "Box A -> B" == OpNode impl [OpNode box [Atom "A"], Atom "B"]
parseTest15 = parse testOps "~A" == OpNode impl [Atom "A", OpNode bot []]
parseTest16 = parse testOps "~(A)" == OpNode impl [Atom "A", OpNode bot []]
parseTest17 = parse testOps "(~A)" == OpNode impl [Atom "A", OpNode bot []]
parseTest18 = parse testOps "~ A" == OpNode impl [Atom "A", OpNode bot []]
parseTest19 = parse testOps "(A -> (B -> ~ A))" == OpNode impl [Atom "A", OpNode impl [Atom "B", OpNode impl [Atom "A", OpNode bot []]]]
parseTest20 = parse testOps "(A -> B -> A)" == OpNode impl [Atom "A", OpNode impl [Atom "B", Atom "A"]]
parseTest21 = parse testOps "A -> B -> A" == OpNode impl [Atom "A", OpNode impl [Atom "B", Atom "A"]]
parseTest22 = parse testOps "A -> B -> ~A" == OpNode impl [Atom "A", OpNode impl [Atom "B", OpNode impl [Atom "A", OpNode bot []]]]

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


