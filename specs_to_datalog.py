from specs import intuitionistic

def operator_to_datalog(operator):
    name, arity = operator
    return_str = name + " {"
    for i in range(arity):
        arg_num = i+1
        return_str += f"s{arg_num}: Sentence"
        if arg_num != arity:
            return_str += ", "
    return_str += "}"
    return return_str

def syntax_to_datalog(operators):
    return_str = ".type Sentence = Atom {name: symbol}"
    for operator in operators:
        return_str += " | "
        return_str += operator_to_datalog(operator)
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

def axioms_to_datalog(axioms):
    return_str = ""
    for axiom in axioms:
        return_str += "Justified(n, goal) :- "
        return_str += (make_datalog_Line(axiom[1], axiom[0]) + ".\n")
    return return_str

def inference_rule_to_datalog(inference_rule):
    name, judgements = inference_rule
    premises, conclusion = judgements[:-1], judgements[-1] # conclusion is a sentence. i.e., either a str or a list

    # conclusion
    if len(premises) == 1:
        i, j = "i", "_"
    elif len(premises) == 2:
        i, j = "i", "j"
    else:
        raise ValueError("should be one or two premises for an inference rule for now")
    return_str = "Justified(n, goal) :- "
    return_str += (make_datalog_Line(conclusion, name, "n", i, j) + ",\n\t")

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
    for rule in inference_rules:
        return_str += (inference_rule_to_datalog(rule) + "\n")
    return return_str


def compile_datalog_engine(system_spec):
    datalog_filename = system_spec.system_name + ".dl"
    with open(datalog_filename, "w", encoding="utf-8") as f:
        f.write(syntax_to_datalog(system_spec.operators))
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
        f.write(axioms_to_datalog(system_spec.axioms))
        f.write(inference_rules_to_datalog(system_spec.inference_rules))

compile_datalog_engine(intuitionistic)