import Core
import Specs
import Proofs

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
ddll1 = Line 1 (OpNode impl [Atom "A", OpNode bot []]) "Assumption" Nothing (Just 1)
ddll2 = Line 2 (Atom "A") "Assumption" Nothing (Just 2)
ddll3 = Line 3 (OpNode bot []) "Modus Ponens" (Just (2, 1)) (Just 3)
ddll4 = Line 4 (OpNode impl [OpNode bot [], (OpNode impl [OpNode impl [Atom "B", OpNode bot []], OpNode bot []])]) "Axiom2" Nothing (Just 4)
ddll5 = Line 5 (OpNode impl [OpNode impl [Atom "B", OpNode bot []], OpNode bot []]) "Modus Ponens" (Just (3, 4)) (Just 5)
ddll6 = Line 6 (OpNode impl [(OpNode impl [OpNode impl [Atom "B", OpNode bot []], OpNode bot []]), Atom "B"]) "Axiom5" Nothing (Just 6)
ddll7 = Line 7 (Atom "B") "Modus Ponens" (Just (5, 6)) (Just 7)

firstDeduction = (useDeduction (Atom "A") [ddll1, ddll2, ddll3, ddll4, ddll5, ddll6, ddll7])

proofAfterDeductionTwice = useDeduction (OpNode impl [Atom "A", OpNode bot []]) firstDeduction

testDeductionTwice :: IO ()
testDeductionTwice = compileDatalogProof "axiom4_deductiontwice" (OpNode impl [OpNode impl [Atom "A", OpNode bot []], OpNode impl [Atom "A", Atom "B"]]) (getLogic specClassical) proofAfterDeductionTwice

