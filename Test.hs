import Core
import Specs
import Proofs

l1 = Line 1 (OpNode impl [OpNode impl [Atom "A", OpNode impl [Atom "A", Atom "A"]], OpNode impl [OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]], OpNode impl [Atom "A", Atom "A"]]]) ("Axiom3", 0, 0)
l2 = Line 2 (OpNode impl [Atom "A", OpNode impl [Atom "A", Atom "A"]]) ("Axiom2", 0, 0)
l3 = Line 3 (OpNode impl [OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]], OpNode impl [Atom "A", Atom "A"]]) ("Modus Ponens", 2, 1)
l4 = Line 4 (OpNode impl [Atom "A", OpNode impl [OpNode impl [Atom "A", Atom "A"], Atom "A"]]) ("Axiom2", 0, 0)
l5 = Line 5 (OpNode impl [Atom "A", Atom "A"]) ("Modus Ponens", 4, 3)

axiom1Proof = Proof "axiom1" (OpNode impl [Atom "A", Atom "A"]) (getLogic specIntuitionistic) [l1, l2, l3, l4, l5]