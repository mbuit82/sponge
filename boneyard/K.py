system_name = "K"

base_system = "classical"

operators = [("Box", 1)]

axioms = [("K Axiom", ["Implication", ["Box", ["Implication", "P", "Q"]], ["Implication", ["Box", "P"], ["Box", "Q"]]])]

inference_rules = [("N", ("P", ["Box", "P"]))]
