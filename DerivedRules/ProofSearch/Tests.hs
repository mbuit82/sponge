module DerivedRules.ProofSearch.Tests where

import Core
import Defs.Specs
import Defs.Operators
import DerivedRules.UseDerivedRules
import DerivedRules.ProofSearch.Sequents
import DerivedRules.ProofSearch.G4Compiler

import qualified Data.Set as Set

g4StrPS :: G4Logic -> String -> SequentProof
g4StrPS g4Logic = (g4ProofSearch g4Logic) . parseSequent

g4ThmStrPS :: G4Logic -> String -> SequentProof
g4ThmStrPS g4Logic str = g4StrPS g4Logic ("=> " ++ str)

t :: String -> SequentProof
t = g4ThmStrPS g4ip

g4Test :: G4Logic -> String -> Bool
g4Test g4Logic = checkSeqProof . (g4ThmStrPS g4Logic)

testG4AndCompiler :: G4Logic -> String -> IO Bool
testG4AndCompiler g4Logic str = do
    let compiledProof = compileG4 (g4ThmStrPS g4Logic str)
    unfolded <- useEverythingButDeduction "classical" compiledProof 
    pure (checkProof (getLogic "classical") unfolded)

ruleInProof :: SequentRule -> SequentProof -> Bool 
ruleInProof seqrl seqpf@(SequentProof seqpfc seqpfj subseqpfs) =
    if seqrl == seqpfj 
        then True
        else case subseqpfs of
            Nothing -> False
            Just s -> or (map (ruleInProof seqrl) s)

getRulesInProof :: SequentProof -> Set.Set SequentRule
getRulesInProof seqpf@(SequentProof _ seqpfj subseqpfs) =
    case subseqpfs of
        Nothing -> Set.singleton seqpfj
        Just s -> Set.union (Set.singleton seqpfj) (Set.unions (map getRulesInProof s))

c :: SequentProof -> IO ()
c seqpf = mapM_ print (proofTreeToLines (compileG4 seqpf))

condTests :: [String]
condTests = [
    "A -> A", -- identity
    "A -> (B -> A)", -- Simp
    "(A -> (B -> C)) -> ((A -> B) -> (A -> C))", -- Frege
    "A -> ((A -> B) -> B)", -- modus ponens (assertion)
    "(A -> B) -> ((B -> C) -> (A -> C))", -- suffixing (hyp syll)
    "(B -> C) -> ((A -> B) -> (A -> C))", -- prefixing (transitivity)
    "(A -> B) -> ((P -> (B -> C)) -> (P -> (A -> C)))", -- both suffixing and prefixing
    "(A -> (B -> C)) -> (B -> (A -> C))" -- switch args
    ]

andTests :: [String]
andTests = [
    "A -> (B -> (A & B))", -- And Intro
    "(A & B) -> A", -- And Elim L
    "(A & B) -> B", -- And Elim R
    "(A & B) -> (B & A)", -- and comm
    "(A & (B & C)) -> ((A & B) & C)", -- and assoc 1
    "((A & B) & C) -> (A & (B & C))", -- and assoc 2
    "((A & B) -> C) -> (A -> (B -> C))", -- currying
    "(A -> (B -> C)) -> ((A & B) -> C)", -- uncurrying
    "(((D -> G) & B) -> C) -> ((D -> G) -> (B -> C))" -- L->4 test
    ]

orTests :: [String]
orTests = [
    "A -> (A v B)", -- Or Intro L
    "B -> (A v B)", -- Or Intro L
    "(A -> C) -> ((B -> C) -> ((A v B) -> C))", -- Or Elim
    "(A v B) -> (B v A)", -- or comm
    "(A v (B v C)) -> ((A v B) v C)", -- or assoc 1
    "((A v B) v C) -> (A v (B v C))", -- or assoc 2
    "((A v B) -> C) -> ((A -> C) & (B -> C))", -- idk what it's called
    "((A v B) -> C) -> ((D -> (A v B)) -> (D -> C))",
    "((A -> C) & (B -> C)) -> ((A v B) -> C)", -- reverse of abovs
    "((A -> A) -> (B v C)) -> (B v C)", -- test Rv embedded in L->->
    "(A & (B v C)) -> ((A & B) v (A & C))", -- dist and over or
    "(A v (B & C)) -> ((A v B) & (A v C))", -- dist or over and
    "((A & B) -> (C1 v C2)) -> (A -> (B -> (C1 v C2)))" -- currying  modified
    ]

modalTests :: [String]
modalTests = [
    "LA -> LA",
    "((LA & (LA -> (LB v LC))) -> (LB v LC))"
    ]

negTests :: [String]
negTests = [
    "~(A & ~A)", -- lnc
    "(A -> B) -> (~B -> ~A)", -- contraposition
    "A -> ~~A", -- dni
    "(A -> ~B) -> (B -> ~A)", -- wiki neg axiom
    "(A -> ~A) -> ~A", -- reductio (Hackstaff)
    "~A -> (A -> B)", -- neg elim
    "(A -> B) -> ((A -> ~B) -> ~A)", -- neg intro
    "~A -> ((A v B) -> B)", -- disjunctive syllogism
    "(A -> B) -> (~~A -> ~~B)", -- double contraposition
    "(~A v B) -> (A -> B)", -- or implies arrow
    "~(A v B) -> (~A & ~B)", -- DM
    "(~A & ~B) -> ~(A v B)", -- DM
    "(~A v ~B) -> ~(A & B)", -- DM
    "(C & ~D) -> ~(C -> D)",
    "~(C -> D) -> ~~(C & ~D)",
    "~(C -> D) -> ~~C",
    "((~C -> B) & ~B) -> ~~C",
    "~~((~C -> B) -> (C v B))",
    "((~C -> B) & ~~~B) -> ~~C",
    "((~A -> B) & ~~~A) -> B" -- case where you need L5 (checked)
    ]


classicalTests :: [String] -- should fail for G4mp and G4ip
classicalTests = [
    "((A -> B) -> A) -> A", -- peirce
    "A v ~A", -- lem
    "~~A -> A", -- dne
    "(A -> B) -> (~A v B)", -- arrow implies or
    "(~B -> ~A) -> (A -> B)", -- backward contraposition
    "~(A & B) -> (~A v ~B)", -- demorgans classical case
    "~(~A & ~B) -> (A v B)", -- SF version of DM
    "(~A -> A) -> A" -- consequentia mirabilis
    ]

doubleNegTests :: [String] -- should pass for G4ip
doubleNegTests = map (\s -> "~~(" ++ s ++ ")") classicalTests