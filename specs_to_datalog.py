import json

def operator_to_datalog(op_name, arity):
    return_str = op_name + " {"
    for i in range(arity):
        arg_num = i+1
        return_str += f"s{arg_num}: Sentence"
        if arg_num != arity:
            return_str += ", "
    return_str += "}"
    return return_str

def syntax_to_datalog(operators):
    return_str = ".type Sentence = Atom {name: symbol}"
    for op_name in operators:
        return_str += " | "
        arity = operators[op_name]
        return_str += operator_to_datalog(op_name, arity)
    return return_str + "\n"

def sentence_to_datalog(sentence):
    if isinstance(sentence, str):
        return sentence
    constructor = sentence[0]
    arguments = sentence[1:]
    args_str = ""
    for i, arg in enumerate(arguments):
        args_str += sentence_to_datalog(arg)
        if i != len(arguments) - 1:
            args_str += ", "
    return "$" + constructor + "(" + args_str + ")"

def make_datalog_Line(sentence, name="_", n="n", i="_", j="_"):
    return_str = "Line(" + n + ", "
    return_str += (sentence_to_datalog(sentence) + ", ")
    name = ("\"" + name + "\"") if name != "_" else name
    return_str += (name + ", " + i + ", " + j + ", " + "goal)")
    return return_str

# assumes tuple format
def axioms_to_datalog(axioms):
    return_str = ""
    for axiom_name in axioms:
        return_str += "Justified(n, goal) :- "
        axiom_content = axioms[axiom_name]
        return_str += (make_datalog_Line(axiom_content, axiom_name) + ".\n")
    return return_str

def inference_rule_to_datalog(rule_name, rule_content):
    premises = rule_content["premises"]
    conclusion = rule_content["conclusion"]

    # conclusion
    if len(premises) == 1:
        i, j = "i", "_"
    elif len(premises) == 2:
        i, j = "i", "j"
    else:
        raise ValueError("should be one or two premises for an inference rule for now")
    return_str = "Justified(n, goal) :- "
    return_str += (make_datalog_Line(conclusion, rule_name, "n", i, j) + ",\n\t")

    # now premises
    for i, prem in enumerate(premises):
        ix_var = "i" if i == 0 else "j" # guaranteed len 1 or 2 at this point bc of above error
        return_str += (ix_var + " < n,\n\t")
        return_str += "Justified(" + ix_var + ", goal),\n\t"
        return_str += (make_datalog_Line(prem, "_", ix_var) + ",\n\t")
    return_str = return_str[:-3] + "." # remove last comma, add period
    return return_str

def inference_rules_to_datalog(inference_rules):
    return_str = ""
    for rule_name in inference_rules:
        rule_content = inference_rules[rule_name]
        return_str += (inference_rule_to_datalog(rule_name, rule_content) + "\n")
    return return_str

def get_system_specs(system_name):
    json_filename = "specs/" + system_name + ".json"
    system_specs = json.load(open(json_filename, "r"))
    assert system_specs["system_name"] == system_name, "something's gone wrong with names"
    base_system = system_specs["base_system"]
    if base_system:
        operators, axioms, inference_rules = get_system_specs(base_system)
        operators = operators | system_specs["operators"] if system_specs["operators"] else operators
        axioms = axioms | system_specs["axioms"] if system_specs["axioms"] else axioms
        inference_rules = inference_rules | system_specs["inference_rules"] if system_specs["inference_rules"] else inference_rules
    else:
        operators = system_specs["operators"]
        axioms = system_specs["axioms"]
        inference_rules = system_specs["inference_rules"]
    return operators, axioms, inference_rules

def compile_datalog_engine(system_name):
    operators, axioms, inference_rules = get_system_specs(system_name)
    datalog_filename = "datalog_engines/" + system_name + ".dl"
    with open(datalog_filename, "w", encoding="utf-8") as f:
        f.write(syntax_to_datalog(operators))
        f.write(".type Goal = ToProve {s: Sentence}\n\n")
        f.write(".decl Line(line_num: unsigned, line_content: Sentence, line_just: symbol, i: unsigned, j: unsigned, goal: Goal)\n")
        f.write(".decl Justified(n: unsigned, goal: Goal)\n")
        f.write(".decl Unjustified(n: unsigned, goal: Goal)\n")
        f.write(".decl UnjustifiedCount(c: number, goal: Goal)\n")
        f.write(".decl Claim(goal: Goal)\n")
        f.write(".decl Proven(f: Sentence)\n\n")
        f.write("Unjustified(n, goal) :- Line(n, _, _, _, _, goal), !Justified(n, goal).\n")
        f.write("UnjustifiedCount(c, goal) :- Claim(goal), c = count : { Unjustified(_, goal) }.\n")
        f.write("Proven(f) :- Claim($ToProve(f)),\n\tLine(n, f, _, _, _, $ToProve(f)),\n\tJustified(n, $ToProve(f)),\n\tUnjustifiedCount(0, $ToProve(f)).\n\n")
        f.write(".output Unjustified\n.output Justified\n.output Proven\n\n")
        f.write(axioms_to_datalog(axioms))
        f.write(inference_rules_to_datalog(inference_rules))

compile_datalog_engine("intuitionistic")
compile_datalog_engine("classical")
compile_datalog_engine("K")