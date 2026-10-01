# system_name = "intuitionistic"

# base_system = None

# operators = [("Bot", 0), ("Implication", 2)]

# axioms = [("Axiom1", ["Implication", "P", "P"]),
#           ("Axiom2", ["Implication", "P", ["Implication", "Q", "P"]]),
#           ("Axiom3", ["Implication", ["Implication", "P", "Q"], ["Implication", ["Implication", "P", ["Implication", "Q", "R"]], ["Implication", "P", "R"]]]),
#           ("Axiom4", ["Implication", ["Implication", "P", ["Bot"]], ["Implication", "P", "Q"]])]

# inference_rules = [("Modus Ponens", ("P", ["Implication", "P", "Q"], "Q"))]


system_name = "intuitionistic"
base_system = None
operators = {"Bot": 0, "Implication": 2}
axioms = {
                "Axiom1": ["Implication", "P", "P"],
                "Axiom2": ["Implication", "P", ["Implication", "Q", "P"]],
                "Axiom3": ["Implication", ["Implication", "P", "Q"], ["Implication", ["Implication", "P", ["Implication", "Q", "R"]], ["Implication", "P", "R"]]],
                "Axiom4": ["Implication", ["Implication", "P", ["Bot"]], ["Implication", "P", "Q"]]}
inference_rules = {"Modus Ponens": {"premises": ["P", ["Implication", "P", "Q"]], "conclusion": "Q"}}
