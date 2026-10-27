module Defs.Operators where

import Core
import Parse.Sentences

-- classical operators
cond :: Operator
cond = Operator "Conditional" "->" 2

bot :: Operator
bot = Operator {operatorName = "Bot", operatorSymbol = "Bot", arity = 0}

andOp :: Operator
andOp = Operator {operatorName = "And", operatorSymbol = "&", arity = 2}

orOp :: Operator
orOp = Operator "Or" "v" 2 -- can also just make operators like this (order follows order in above e.g. in andOp)

negDef :: [Sentence] -> Sentence
negDef = \[a] -> (OpNode cond [a, OpNode bot []])
neg :: DefinedOperator
neg = DefinedOperator "Not" "~" 1 negDef

negOp :: Operator
negOp = Operator "Not" "~" 1

bicondDef :: [Sentence] -> Sentence
bicondDef = \[a, b] -> parseWithSubst [cond, andOp] [] "(A -> B) & (B -> A)" [("A", a), ("B", b)]
bicond :: DefinedOperator
bicond = DefinedOperator "Biconditional" "<>" 2 bicondDef



-- Modal logic
box :: Operator
box = Operator "Box" "L" 1

diamondDef :: [Sentence] -> Sentence
diamondDef = \[singleA] -> parseWithSubst [box, negOp] [] "~L~A" [("A", singleA)]
diamond :: DefinedOperator
diamond = DefinedOperator "Diamond" "M" 1 diamondDef



-- Linear logic (Hesselink 1990)
linNull :: Operator
linNull = Operator "Null" "0" 0

linOr :: Operator
linOr = Operator "LinearDisjunction" "+" 2

linNeg :: Operator
linNeg = Operator "LinearNegation" "~" 1

lolliDef :: [Sentence] -> Sentence
lolliDef = \[a, b] -> (OpNode linOr [OpNode linNeg [a], b])
lolli :: DefinedOperator
lolli = DefinedOperator "Lollipop" "-o" 2 lolliDef

quest :: Operator
quest = Operator "Quest" "?" 1