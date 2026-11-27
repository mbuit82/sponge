module DerivedRules.ProofSearch.Sequents where

import Core 
import DerivedRules.Utils

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List

isAtomic :: Sentence -> Bool
isAtomic (Atom _) = True
isAtomic _ = False

data Sequent = Sequent {
    antecedent :: Set.Set Sentence,
    succedent :: Set.Set Sentence
} deriving (Eq, Ord)
instance Show Sequent where
    show = prettyPrintSequent

prettyPrintSet :: Set.Set Sentence -> String
prettyPrintSet sent = show (Set.toList sent)

prettyPrintSequent :: Sequent -> String
prettyPrintSequent seq@(Sequent ant succ) =
    prettyPrintSet ant ++ " => " ++ prettyPrintSet succ

data SequentRule = SequentRule {
    seqRuleName :: String,
    seqPremises :: [Sequent],
    seqConclusion :: Sequent
} deriving (Eq, Ord)
instance Show SequentRule where
    show = seqRuleName

data SequentProof = SequentProof {
    seqContent :: Sequent,
    seqJustification :: SequentRule,
    seqSubProofs :: Maybe [SequentProof]
} deriving (Show, Eq, Ord)

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

-- particular choice of rules is mix of Troelstra book and Dyckoff
-- important modifications are ax and arrowL1. Both changes are admissible
-- details are in README of ProofSearch
ax :: SequentRule
ax = mkSequentRule "Ax" 
    []
    "Gamma, A => A"
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
    ["Gamma, A, B => E"]
    "Gamma, A -> B, A => E"
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
    ["Gamma, D -> B, => C -> D", "Gamma, B => E"]
    "Gamma, (C -> D) -> B => E"
negR :: SequentRule
negR = mkSequentRule "R~"
    ["Gamma, A => NotA"]
    "Gamma => ~A"
-- negRLoop :: SequentRule
-- negRLoop = mkSequentRule "R~"
--     ["Gamma, A => ~A"]
--     "Gamma => ~A"
negL1 :: SequentRule
negL1 = mkSequentRule "L~1" 
    []
    "Gamma, A, ~A => E"
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
    ["Gamma, ~D => C -> D"]
    "Gamma, ~(C -> D) => E"
arrowL5 :: SequentRule
arrowL5 = mkSequentRule "L->5" 
    ["Gamma => ~C", "Gamma, B => E"]
    "Gamma, (~C -> B) => E"
negL5 :: SequentRule
negL5 = mkSequentRule "L~5"
    ["Gamma => ~C"]
    "Gamma, ~~C => E"
-- NotA can be thought of as a metasymbol.
-- Looking _only_ at the sequent system, it can be thought of as the empty set. 
-- (This is not formally the case in the code though.)
-- However, you can think of NotA as ~A too and you get a sound rule that is useful for the compiler case for R~. 
-- Replacing NotA with ~A in the rule you get a version of reductio: (A -> ~A) -> ~A. 
-- The R~ case would then reduce to that, which has a rather short proof (either immediate or 7 lines, depending on choice of axiomatization).
-- However, if we used that in the sequent proof search, we'd have a rule that loops. 
-- we can avoid doing the loop this way because the rule is also sound with an empty succedent (by translation of Bot). 
-- So we can use the rule like this, and then when it comes time to compile, replace NotA with ~A. 
-- For the sequent system by itself, this is immoral, but the compiler I think justifies this for this use case

mInvertibleRules :: [SequentRule]
mInvertibleRules = [ax, andL, arrowR, arrowL1, arrowL2, arrowL3, andR, orL]
mNoninvertibleRules :: [SequentRule]
mNoninvertibleRules = [orR0, orR1, arrowL4]

iInvertibleRules :: [SequentRule]
iInvertibleRules = mInvertibleRules ++ [negL1, negL2, negL3, negR]
iNoninvertibleRules :: [SequentRule]
iNoninvertibleRules = mNoninvertibleRules ++ [negL4, negL5, arrowL5]

data G4Logic = G4Logic {
    invertibleRules :: [SequentRule], 
    noninvertibleRules :: [SequentRule]}
-- order of application should be invertible, then loop, then noninvertible. 

g4mp :: G4Logic
g4mp = G4Logic mInvertibleRules mNoninvertibleRules
g4ip :: G4Logic
g4ip = G4Logic iInvertibleRules iNoninvertibleRules

-- this unification procedure only works on sets.
-- would have problem in case of schema set {A -> B, C -> D} if it wasn't for just sets

getSubstFragment :: Set.Set Sentence -> Sentence -> Set.Set Substitution
getSubstFragment sents schema =
    Set.map fromJust (Set.filter (/= Nothing) (Set.map (getSubst schema) sents))

getSubstFragments :: Set.Set Sentence -> Set.Set Sentence -> Set.Set (Set.Set Substitution)
getSubstFragments schemas sents = Set.map (getSubstFragment sents) schemas

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
                Just (map (instantiateSequent gamma (("NotA", Atom "NotA"):subst)) prems)

tryInvertibleRules:: [SequentRule] -> Sequent -> Maybe (SequentRule, [Sequent])
tryInvertibleRules [] _ = Nothing
tryInvertibleRules (rl:rls) seq = case useRule rl seq of
    Nothing -> tryInvertibleRules rls seq
    Just prems -> Just (rl, prems)

invertibleStep :: G4Logic -> Sequent -> Maybe (SequentRule, [Sequent])
invertibleStep g4Logic = tryInvertibleRules (invertibleRules g4Logic)

-- tryLoopRule :: G4Logic -> SequentRule -> Sequent -> Maybe (SequentRule, [Sequent])
-- tryLoopRule g4Logic rl seq =
--     -- try the rule. 
--     -- if for the result of trying the rule, everything in the original sequent (ant, succ) is in the new (ant, succ), then Nothing
--     -- else use it

tryNoninvertRule :: G4Logic -> SequentRule -> Sequent -> Maybe SequentProof
tryNoninvertRule g4Logic rl seq = case useRule rl seq of
    Just subSeqs -> 
        let rest = SequentProof seq rl (Just (map (g4ProofSearch g4Logic) subSeqs)) in
        if checkSeqProof rest then Just rest else Nothing
    Nothing -> Nothing

giveUp :: SequentRule
giveUp = mkSequentRule "NOT PROVABLE" [] "Gamma => S"

tryNoninvertRules :: G4Logic -> [SequentRule] -> Sequent -> SequentProof
tryNoninvertRules _ [] seq = SequentProof seq giveUp Nothing
tryNoninvertRules g4Logic (rl:rls) seq = case tryNoninvertRule g4Logic rl seq of
    Just rest -> rest
    Nothing -> tryNoninvertRules g4Logic rls seq

noninvertibleStep :: G4Logic -> Sequent -> SequentProof
noninvertibleStep g4Logic = tryNoninvertRules g4Logic (noninvertibleRules g4Logic)

g4ProofSearch :: G4Logic -> Sequent -> SequentProof
g4ProofSearch g4Logic seq = case invertibleStep g4Logic seq of
    Just (rl, subSeqs) -> SequentProof seq rl (Just (map (g4ProofSearch g4Logic) subSeqs))
    Nothing -> noninvertibleStep g4Logic seq

checkSeqProof :: SequentProof -> Bool -- very informal
checkSeqProof seqPf = case seqSubProofs seqPf of
    Nothing -> False
    Just sspfs -> and (map checkSeqProof sspfs)