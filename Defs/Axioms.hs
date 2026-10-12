module Defs.Axioms where

import Core
import Defs.Operators

-- FOR SOME POINTERS: the parse function needs to know what symbols are operators and what symbols are defined operators. The first list passed to parse is the list of operators it needs to know about to parse the string, and the second list is the list of defined operators. 

-- the names for these come from the axiomatization in 18.510. Axiom 1 was P -> P, but that's not necessary so took it out
-- I like K combinator and S combinator as names for axiom2 and axiom3, but since we have modal axiom K I'm iffy abt using it in case of confusion. In my indecision these names have remained. 
axiom2 :: Axiom
axiom2 = Axiom "Axiom2" (parse [cond] [] "P -> (Q -> P)")
axiom3 :: Axiom
axiom3 = Axiom "Axiom3" (parse [cond] [] "(P -> Q) -> ((P -> (Q -> R)) -> (P -> R))")
axiom4 :: Axiom
axiom4 = Axiom "Axiom4" (parse [cond, bot] [] "(P -> Bot) -> (P -> Q)")
axiom5 :: Axiom
axiom5 = Axiom "Axiom5" (parse [cond, bot] [] "((P -> Bot) -> Bot) -> P")

-- These are from an ND-ish axiomatization; I took them from Bezhanishvili's book on intuitionistic logic
andEL :: Axiom
andEL = Axiom "And-EL" (parse [cond, andOp, orOp] [] "(P & Q) -> P")
andER :: Axiom
andER = Axiom "And-ER" (parse [cond, andOp, orOp] [] "(P & Q) -> Q")
andI :: Axiom
andI = Axiom "And-I" (parse [cond, andOp, orOp] [] "P -> (Q -> (P & Q))")
orIL :: Axiom
orIL = Axiom "Or-IL" (parse [cond, andOp, orOp] [] "P -> (P v Q)")
orIR :: Axiom
orIR = Axiom "Or-IR" (parse [cond, andOp, orOp] [] "Q -> (P v Q)")
orE :: Axiom
orE = Axiom "Or-E" (parse [cond, andOp, orOp] [] "(P -> R) -> ((Q -> R) -> ((P v Q) -> R))")
explosion :: Axiom
explosion = Axiom "Explosion" (parse [cond, bot] [] "Bot -> P")
lem :: Axiom
lem = Axiom "Excluded Middle" (parse [cond] [neg] "~ ~ P -> P") -- note that Bot gets in there even though it's not passed to the parsing function

-- modal axioms
kAxiom :: Axiom
kAxiom = Axiom "K Axiom" (parse [cond, box] [] "L (P -> Q) -> (L P -> L Q)")
tAxiom :: Axiom
tAxiom = Axiom "T Axiom" (parse [cond, box] [] "L P -> P")
dAxiom :: Axiom
dAxiom = Axiom "D Axiom" (parse [cond, box] [diamond] "L P -> M P")
fourAxiom :: Axiom
fourAxiom = Axiom "4 Axiom" (parse [cond, box] [] "L P -> L L P")
brouwerscheAxiom :: Axiom
brouwerscheAxiom = Axiom "B Axiom" (parse [cond, box] [diamond] "P -> L M P")
fiveAxiom :: Axiom
fiveAxiom = Axiom "5 Axiom" (parse [cond, box] [diamond] "M P -> L M P")
elsewhereAxiom :: Axiom
elsewhereAxiom = Axiom "Elsewhere Axiom" (parse [cond, orOp] [diamond] "M M P -> (P v M P)")
convergenceAxiom :: Axiom
convergenceAxiom = Axiom "Convergence Axiom" (parse [cond, box] [diamond] "M L P -> L M P")
gettierAxiom :: Axiom -- S4.4 axiom that gets Gettier cases in S4.4 as a logic of belief/knowledge
gettierAxiom = Axiom "Gettier Axiom" (parse [cond, andOp, orOp, box] [diamond] "(P & M L Q) -> L(P v Q)")
glAxiom :: Axiom
glAxiom = Axiom "GL Axiom" (parse [cond, box] [] "L((LP -> P) -> LP)")
hAxiom :: Axiom -- used in KH logic, slightly weaker than KW
hAxiom = Axiom "H Axiom" (parse [cond, box] [bicond] "L((LP <> P) -> LP)")
d1Axiom :: Axiom
d1Axiom = Axiom "D1 Axiom" (parse [cond, box, orOp] [] "L(LP -> Q) v L(LQ -> P)")
d2Axiom :: Axiom
d2Axiom = Axiom "D2 Axiom" (parse [cond, box, orOp, andOp] [] "L((P & LP) -> Q) v L((Q & LQ) -> P)")
