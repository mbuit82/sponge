import Core
import Specs
import Proofs

testEngines :: IO ()
testEngines = do
    compileDatalogEngine specIntuitionistic
    compileDatalogEngine specClassical
    compileDatalogEngine specK

l1 = Line 1 (OpNode impl [OpNode impl [Atom "A", OpNode impl [Atom "A", Atom "A"]], OpNode impl [OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]], OpNode impl [Atom "A", Atom "A"]]]) "Axiom3" Nothing
l2 = Line 2 (OpNode impl [Atom "A", OpNode impl [Atom "A", Atom "A"]]) "Axiom2" Nothing
l3 = Line 3 (OpNode impl [OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]], OpNode impl [Atom "A", Atom "A"]]) "Modus Ponens" (Just (2, 1))
l4 = Line 4 (OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]]) "Axiom2" Nothing
l5 = Line 5 (OpNode impl [Atom "A", Atom "A"]) "Modus Ponens" (Just (4, 3))

-- axiom1Proof = Proof "axiom1" (OpNode impl [Atom "A", Atom "A"]) (getLogic specIntuitionistic) [l1, l2, l3, l4, l5]

testPureProof :: IO ()
testPureProof = compileDatalogProof "axiom1" (OpNode impl [Atom "A", Atom "A"]) (getLogic specIntuitionistic) [l1, l2, l3, l4, l5]

testOffset :: IO ()
testOffset = compileDatalogProof "axiom1offset" (OpNode impl [Atom "A", Atom "A"]) (getLogic specIntuitionistic) (applyOffsetToProof 10 [l1, l2, l3, l4, l5])