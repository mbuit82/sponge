module DerivedRules.Sequents where

import Core 
import Parse.Sentences
import Defs.Operators
import DerivedRules.Utils
import DerivedRules.Deduction

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List
import Data.Char

parseIP :: String -> Maybe Sentence
parseIP str = 
    if (all isSpace str)
        then Nothing
        else Just (parse [andOp, orOp, cond, negOp] [] str)

isAtomic :: Sentence -> Bool
isAtomic (Atom _) = True
isAtomic _ = False

data Sequent = Sequent {
    antecedent :: Set.Set Sentence,
    succedent :: Set.Set Sentence
} deriving (Show, Eq, Read)

data SequentRule = SequentRule {
    seqRuleName :: String,
    seqPremises :: [Sequent],
    seqConclusion :: Sequent
} deriving (Eq, Show, Read)

data SequentProof = SequentProof {
    seqContent :: Sequent,
    seqJustification :: SequentRule,
    seqSubProofs :: Maybe [SequentProof]
} deriving (Show, Eq, Read)

splitOnX :: String -> String -> [String]
splitOnX [] _ = error "splitOnX: empty delimiter"
splitOnX delim str = filter (/=[]) (go [] str)
  where
    n = length delim
    go acc [] = [reverse acc]
    go acc s@(c:cs)
      | delim `isPrefixOf` s = reverse acc : go [] (drop n s)
      | otherwise            = go (c:acc) cs

parseSet :: String -> Set.Set Sentence
parseSet setStr = 
    let sentStrs = (splitOnX "," setStr) in
    let withNothings = map parseIP (filter (\str -> not ("Gamma" `isInfixOf` str)) sentStrs) in
        Set.fromList (map fromJust (filter (/= Nothing) withNothings))

parseSequent :: String -> Sequent
parseSequent seqStr' = let seqStr = " " ++ seqStr' ++ " " in
    case splitOnX "=>" seqStr of 
        [antStr, succStr] -> Sequent (parseSet antStr) (parseSet succStr)
        _ -> error "error in sequent parsing"

mkSequentRule :: String -> [String] -> String -> SequentRule
mkSequentRule rn prems concl = SequentRule rn (map parseSequent prems) (parseSequent concl)

ax :: SequentRule
ax = mkSequentRule "Ax" 
    []
    "Gamma, P => P"
andR :: SequentRule
andR = mkSequentRule "R&" 
    ["Gamma => A", "Gamma => B"] 
    "Gamma => A & B"
orR0 :: SequentRule
orR0 = mkSequentRule "Rv0"
    ["Gamma => A"]
    "Gamma => A v B"
orR1 :: SequentRule
orR1 = mkSequentRule "Rv1"
    ["Gamma => B"]
    "Gamma => A v B"
arrowR :: SequentRule
arrowR = mkSequentRule "R->"
    ["Gamma, A => B"]
    "Gamma => A -> B"
andL :: SequentRule
andL = mkSequentRule "L&"
    ["Gamma, A, B => C"]
    "Gamma, A & B => C"
orL :: SequentRule
orL = mkSequentRule "Lv"
    ["Gamma => A -> C", "Gamma => B -> C"]
    "Gamma, A v B => C"
arrowL1 :: SequentRule
arrowL1 = mkSequentRule "L->1"
    ["Gamma, P, B => E"]
    "Gamma, P -> B, P => E"
arrowL2 :: SequentRule
arrowL2 = mkSequentRule "L->2"
    ["Gamma, C -> (D -> B) => E"]
    "Gamma, (C & D) -> B => E"
arrowL3 :: SequentRule
arrowL3 = mkSequentRule "L->3"
    ["Gamma, C -> B, D -> B => E"]
    "Gamma, (C v D) -> B => E"
arrowL4 :: SequentRule
arrowL4 = mkSequentRule "L->4"
    ["Gamma, C, D -> B => D", "Gamma, B => E"]
    "Gamma, (C -> D) -> B => E"
negR :: SequentRule
negR = mkSequentRule "R~"
    ["Gamma, A => VOID"]
    "Gamma => ~A"
negL1 :: SequentRule
negL1 = mkSequentRule "L~1" 
    []
    "Gamma, P, ~P => E"
negL2 :: SequentRule
negL2 = mkSequentRule "L~2"
    ["Gamma, C -> ~D => E"]
    "Gamma, ~(C & D) => E"
negL3 :: SequentRule
negL3 = mkSequentRule "L~3" 
    ["Gamma, ~C, ~D => E"]
    "Gamma, ~(C v D) => E"
negL4 :: SequentRule
negL4 = mkSequentRule "L~4"
    ["Gamma, C, ~D => D"]
    "Gamma, ~(C -> D) => E"
arrowL5 :: SequentRule
arrowL5 = mkSequentRule "L->5" 
    ["Gamma, C, => VOID", "Gamma, B => E"]
    "Gamma, (~C -> B) => E"
negL5 :: SequentRule
negL5 = mkSequentRule "L~5"
    ["Gamma, C => VOID"]
    "Gamma, ~~C => E"
-- VOID can be thought of as a metasymbol. It would represent the empty set.
-- However, it is currently an object language constant in the proof search, 
-- Meaning the proof search isn't the moral solution to primitive negation
-- It is however though the only immoral thing left I think

invertibleRules :: [SequentRule]
invertibleRules = [ax, andL, arrowR, arrowL1, arrowL2, arrowL3, negL1, negL2, negL3, negR, andR, orL]

noninvertibleRules :: [SequentRule]
noninvertibleRules = [arrowL4, negL4, arrowL5, negL5, orR0, orR1]


-- this unification procedure only works on sets.
-- would have problem in case of schema set {A -> B, C -> D} if it wasn't for just sets
type Substitution = [(String, Sentence)]

getSubstFragment :: Set.Set Sentence -> Sentence -> Set.Set Substitution
getSubstFragment sents schema =
    Set.map fromJust (Set.filter (/= Nothing) (Set.map (getSubst schema) sents))

getSubstFragments :: Set.Set Sentence -> Set.Set Sentence -> Set.Set (Set.Set Substitution)
getSubstFragments schemas sents = Set.map (getSubstFragment sents) schemas

checkPairsCohere :: (String, Sentence) -> (String, Sentence) -> Bool
checkPairsCohere (a1, s1) (a2, s2) 
    | a1 == a2 && s1 /= s2 = False
    | otherwise = True

-- checks if a pair is coherent with an entire subst. 
-- true if it's coherent with all the pairs in the subst.
checkPairWithSubst :: Substitution -> (String, Sentence) -> Bool
checkPairWithSubst [] p = True
checkPairWithSubst (p':ps') p = checkPairsCohere p' p && checkPairWithSubst ps' p

checkSubstsCohere :: Substitution -> Substitution -> Bool
checkSubstsCohere subst1 subst2 = and (map (checkPairWithSubst subst1) subst2)

extendSubst :: Substitution -> (String, Sentence) -> Substitution
extendSubst subst pair = if pair `elem` subst then subst else pair:subst

sumSubsts :: Substitution -> Substitution -> Substitution
sumSubsts = foldl' extendSubst

sumIfCoherent :: Substitution -> Substitution -> Maybe Substitution
sumIfCoherent subst1 subst2 =
    if checkSubstsCohere subst1 subst2 then Just (sumSubsts subst1 subst2) else Nothing

-- given a set of substs and a subst, return the set of coherent extensions by the second arg
getPossibleSubsts'' :: Set.Set Substitution -> Substitution -> Set.Set Substitution
getPossibleSubsts'' baseSubsts extendingSubst =
    Set.map fromJust (Set.filter (/= Nothing) (Set.map (sumIfCoherent extendingSubst) baseSubsts))

getPossibleSubsts' :: Set.Set Substitution -> Set.Set Substitution -> Set.Set Substitution
getPossibleSubsts' substSet1 substSet2 =
    Set.unions (Set.map (getPossibleSubsts'' substSet1) substSet2)

getPossibleSubsts :: Set.Set (Set.Set Substitution) -> Set.Set Substitution
getPossibleSubsts setOfSubsts = Set.foldl' getPossibleSubsts' (Set.fromList [[]]) setOfSubsts -- empty should work here?

checkPPropositional :: Substitution -> Bool
checkPPropositional [] = True
checkPPropositional (p:ps) = case p of
    ("P", (OpNode _ _)) -> False
    _ -> checkPPropositional ps

getSubsts' :: Set.Set Sentence -> Set.Set Sentence -> Set.Set Substitution
getSubsts' schemas sents = getPossibleSubsts (getSubstFragments schemas sents)

getSubsts :: Set.Set Sentence -> Set.Set Sentence -> Set.Set Substitution
getSubsts schemas sents = Set.filter checkPPropositional (getSubsts' schemas sents)

getSetSubst :: Set.Set Sentence -> Set.Set Sentence -> Maybe Substitution
getSetSubst schemas sents = Set.lookupMin (getSubsts schemas sents)

applySubst :: Substitution -> Sentence -> Sentence
applySubst subst (Atom a) = instantiateVar (Map.fromList subst) a
applySubst subst (OpNode op args) = OpNode op (map (applySubst subst) args)

instantiateSet :: Substitution -> Set.Set Sentence -> Set.Set Sentence
instantiateSet subst set = Set.map (applySubst subst) set

-- this also checks if a rule is applicable
-- need to have a dumb fix for case where succedent is empty.
-- reason can't do kosher fix is that it would mean making both sides sets, ie make it basically classical
tryUnifySeqs :: Sequent -> Sequent -> Maybe Substitution
tryUnifySeqs (Sequent schemaAnt schemaSucc) (Sequent currAnt currSucc) =
    let (antSubsts, succSubsts) = (getSubsts schemaAnt currAnt, getSubsts schemaSucc currSucc) in
    Set.lookupMin (getPossibleSubsts' antSubsts succSubsts)

getGamma :: Sequent -> Sequent -> Substitution -> Set.Set Sentence
getGamma schemaSeq currSeq subst = 
    (antecedent currSeq) Set.\\ (Set.map (applySubst subst) (antecedent schemaSeq))

instantiateSequent :: Set.Set Sentence -> Substitution -> Sequent -> Sequent
instantiateSequent gamma subst (Sequent schemaAnt schemaSucc) = 
    Sequent (Set.union gamma (instantiateSet subst schemaAnt)) 
            (instantiateSet subst schemaSucc)

useRule :: SequentRule -> Sequent -> Maybe [Sequent]
useRule (SequentRule rn prems concl) seq =
    case tryUnifySeqs concl seq of
        Nothing -> Nothing
        Just subst -> 
            let gamma = getGamma concl seq subst in
                Just (map (instantiateSequent gamma (("VOID", Atom "VOID"):subst)) prems)

tryInvertibleRules:: [SequentRule] -> Sequent -> Maybe (SequentRule, [Sequent])
tryInvertibleRules [] _ = Nothing
tryInvertibleRules (rl:rls) seq = case useRule rl seq of
    Nothing -> tryInvertibleRules rls seq
    Just prems -> Just (rl, prems)

invertibleStep :: Sequent -> Maybe (SequentRule, [Sequent])
invertibleStep = tryInvertibleRules invertibleRules

tryNoninvertRule :: SequentRule -> Sequent -> Maybe SequentProof
tryNoninvertRule rl seq = case useRule rl seq of
    Just subSeqs -> 
        let rest = SequentProof seq rl (Just (map g4ProofSearch subSeqs)) in
        if checkProof rest then Just rest else Nothing
    Nothing -> Nothing

notProvable :: SequentRule
notProvable = mkSequentRule "NOT PROVABLE" [] ("Gamma => S")

tryNoninvertRules :: [SequentRule] -> Sequent -> SequentProof
tryNoninvertRules [] seq = SequentProof seq notProvable Nothing
tryNoninvertRules (rl:rls) seq = case tryNoninvertRule rl seq of
    Just rest -> rest
    Nothing -> tryNoninvertRules rls seq

noninvertibleStep :: Sequent -> SequentProof
noninvertibleStep = tryNoninvertRules noninvertibleRules

g4ProofSearch :: Sequent -> SequentProof
g4ProofSearch seq = case invertibleStep seq of
    Just (rl, subSeqs) -> SequentProof seq rl (Just (map g4ProofSearch subSeqs))
    Nothing -> noninvertibleStep seq

checkProof :: SequentProof -> Bool
checkProof seqPf = case seqSubProofs seqPf of
    Nothing -> False
    Just sspfs -> and (map checkProof sspfs)

g4StrPS :: String -> SequentProof
g4StrPS = g4ProofSearch . parseSequent 

g4Test :: String -> Bool
g4Test = checkProof . g4StrPS

condTests :: [String]
condTests = [
    "=> A -> A", -- identity
    "=> A -> (B -> A)", -- Simp
    "=> (A -> (B -> C)) -> ((A -> B) -> (A -> C))", -- Frege
    "=> A -> ((A -> B) -> B)", -- modus ponens (assertion)
    "=> (A -> B) -> ((B -> C) -> (A -> C))", -- suffixing (hyp syll)
    "=> (B -> C) -> ((A -> B) -> (A -> C))", -- prefixing (transitivity)
    "=> (A -> B) -> ((P -> (B -> C)) -> (P -> (A -> C)))", -- both suffixing and prefixing
    "=> (A -> (B -> C)) -> (B -> (A -> C))" -- switch args
    ]

andTests :: [String]
andTests = [
    "=> A -> (B -> (A & B))", -- And Intro
    "=> (A & B) -> A", -- And Elim L
    "=> (A & B) -> B", -- And Elim R
    "=> (A & B) -> (B & A)", -- and comm
    "=> (A & (B & C)) -> ((A & B) & C)", -- and assoc 1
    "=> ((A & B) & C) -> (A & (B & C))", -- and assoc 2
    "=> ((A & B) -> C) -> (A -> (B -> C))", -- currying
    "=> (A -> (B -> C)) -> ((A & B) -> C)" -- uncurrying
    ]

orTests :: [String]
orTests = [
    "=> A -> (A v B)", -- Or Intro L
    "=> B -> (A v B)", -- Or Intro L
    "=> (A -> C) -> ((B -> C) -> ((A v B) -> C))", -- Or Elim
    "=> (A v B) -> (B v A)", -- or comm
    "=> (A v (B v C)) -> ((A v B) v C)", -- or assoc 1
    "=> ((A v B) v C) -> (A v (B v C))", -- or assoc 2
    "=> ((A v B) -> C) -> ((A -> C) & (B -> C))", -- idk what it's called
    "=> ((A -> C) & (B -> C)) -> ((A v B) -> C)", -- reverse of abovs
    "=> ((A -> A) -> (B v C)) -> (B v C)", -- test Rv embedded in L->->
    "=> (A & (B v C)) -> ((A & B) v (A & C))", -- dist and over or
    "=> (A v (B & C)) -> ((A v B) & (A v C))" -- dist or over and
    ]

negTests :: [String]
negTests = [
    "=> (A -> B) -> (~B -> ~A)", -- contraposition
    "=> A -> ~~A", -- dni
    "=> (A -> ~B) -> (B -> ~A)", -- wiki neg axiom
    "=> (A -> ~A) -> ~A", -- reductio (Hackstaff)
    "=> ~A -> (A -> B)", -- neg elim
    "=> (A -> B) -> ((A -> ~B) -> ~A)", -- neg intro
    "=> ~A -> ((A v B) -> B)", -- disjunctive syllogism
    "=> (A -> B) -> (~~A -> ~~B)", -- double contraposition
    "=> (~A v B) -> (A -> B)", -- or implies arrow
    "=> ~(A v B) -> (~A & ~B)", -- DM
    "=> (~A & ~B) -> ~(A v B)", -- DM
    "=> (~A v ~B) -> ~(A & B)" -- DM
    ]

classicalTests :: [String] -- should fail for G4mp and G4ip
classicalTests = [
    "=> ((A -> B) -> A) -> A", -- peirce
    "=> A v ~A", -- lem
    "=> ~~A -> A", -- dne
    "=> (A -> B) -> (~A v B)", -- arrow implies or
    "=> (~B -> ~A) -> (A -> B)", -- backward contraposition
    "=> ~(A & B) -> (~A v ~B)", -- demorgans classical case
    "=> ~(~A & ~B) -> (A v B)", -- SF version of DM
    "=> (~A -> A) -> A" -- consequentia mirabilis
    ]

doubleNegTests :: [String] -- should pass for G4ip
doubleNegTests = map (\s -> "=> ~~(" ++ drop 3 s ++ ")") classicalTests

getSuccSent :: Sequent -> Sentence
getSuccSent (Sequent _ succ) = (fromJust (Set.lookupMin succ))

-- this should work, but defensively adding an error in case it doesn't so it fails
getStepSubst :: SequentProof -> [(String, Sentence)]
getStepSubst seqPf@(SequentProof seqpfc rl subseqpfs) =
    case tryUnifySeqs (seqConclusion rl) seqpfc of
        Nothing -> error "something's wrong"
        Just subst -> subst

-- really consider changing the order of substitutions
parseForSeq :: [(String, Sentence)] -> String -> Sentence
parseForSeq subst str = parseWithSubst [andOp, orOp, cond, negOp] [] str subst

-- I think there are some edge cases to this not working. 
-- particularly, deduct the same arg twice. Stupid, but still an edge case. 
-- e.g. (A -> (A -> A)) would potentially be funny
-- but it wouldn't even tbh one of the things would just get overridden bc substs become maps
-- I actually think that issue may come up earlier, in Deduction.hs
compileG4' :: [(Sentence, ProofTree)] -> SequentProof -> ProofTree
compileG4' oldDerivations seqPf@(SequentProof seqpfc rl subseqpfs) =
    let p = parseForSeq (getStepSubst seqPf) in -- I think lazy eval makes this good :D
    case (seqRuleName rl) of
        "Ax" -> ProofTree (getSuccSent seqpfc) "Assumption" []
        "R&" -> 
            let [aRecCall, bRecCall] = map (compileG4' oldDerivations) (fromJust subseqpfs) in
            ProofTree
                (getSuccSent seqpfc)
                "Modus Ponens"
                    [bRecCall,
                    ProofTree (p "B -> (A & B)") "Modus Ponens" 
                        [aRecCall,
                        ProofTree (p "A -> (B -> (A & B))") "And Intro" []]]
        "L&" -> -- unsure about where I need to add old and new derivations
            let aDerivation = ProofTree 
                    (p "A") 
                    "Modus Ponens" 
                    [(ProofTree (p "A & B") "Assumption" []), (ProofTree (p "(A & B) -> A") "And Elim L" [])] in
            let bDerivation = ProofTree 
                    (p "B") 
                    "Modus Ponens" 
                    [(ProofTree (p "A & B") "Assumption" []), (ProofTree (p "(A & B) -> B") "And Elim R" [])] in
            let newDerivations = [((p "A"), aDerivation), (p "B", bDerivation)] in
            let [recCall] = map (compileG4' (oldDerivations ++ newDerivations)) (fromJust subseqpfs) in
            composeDerivations newDerivations recCall
        "Rv0" -> 
            let [recCall] = map (compileG4' oldDerivations) (fromJust subseqpfs) in
            ProofTree 
                (getSuccSent seqpfc)
                "Modus Ponens"
                    [recCall,
                    ProofTree (p "A -> (A v B)") "Or Intro L" []]
        "Rv1" -> 
            let [recCall] = map (compileG4' oldDerivations) (fromJust subseqpfs) in
            ProofTree 
                (getSuccSent seqpfc)
                "Modus Ponens"
                    [recCall,
                    ProofTree (p "B -> (A v B)") "Or Intro R" []]
        "Lv" -> 
            let [aRecCall, bRecCall] = map (compileG4' oldDerivations) (fromJust subseqpfs) in
            ProofTree 
                (getSuccSent seqpfc)
                "Modus Ponens"
                [ProofTree (p "A v B") "Assumption" [],
                ProofTree (p "(A v B) -> C") "Modus Ponens"
                    [bRecCall,
                    ProofTree (p "(B -> C) -> ((A v B) -> C)") "Modus Ponens"
                        [aRecCall,
                        ProofTree (p "(A -> C) -> ((B -> C) -> ((A v B) -> C))") "Or Elim" []]]]
        "R->" -> -- you could instead have it collect deduction args... I think I like that more
        -- you would use makeDeductionsFunc, and have this always return a list of deduction args you're keeping track of
            let [recCall] = map (compileG4' oldDerivations) (fromJust subseqpfs) in
            let [deductionArg] = getNEmbeddedAntecedents cond 1 (getSuccSent seqpfc) in
            useDeduction deductionArg recCall

compileG4 :: SequentProof -> ProofTree
compileG4 = compileG4' []

g4TheoremSearch :: Sentence -> SequentProof
g4TheoremSearch sent = g4ProofSearch (Sequent Set.empty (Set.fromList [sent]))

proofSearch :: Sentence -> ProofTree
proofSearch = compileG4 . g4TheoremSearch
-- with classical stuff it'd look something like this
    -- let iSearch = g4TheoremSearch sent in
    -- if checkProof iSearch == True
    --     then compileG4 iSearch
    --     else 
    --         ProofTree
    --             sent
    --             "DNE"

useProofSearch' :: ProofTree -> ProofTree
useProofSearch' pfTree =
    if (pfJustification pfTree) == "classical result"
        then proofSearch (pfContent pfTree)
        else pfTree

useProofSearch :: ProofTree -> ProofTree
useProofSearch = applyOverTree useProofSearch'