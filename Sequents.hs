module Sequents where

import Core 
import Parse.Sentences
import Defs.Operators

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List
import Language.Haskell.TH (arrowK)

-- type MultiSet = Map.Map Sentence Int

parseIP :: String -> Sentence
parseIP = parse [andOp, orOp, cond, negOp] []

isAtomic :: Sentence -> Bool
isAtomic (Atom _) = True
isAtomic _ = False

data Sequent = Sequent {
    antecedent :: Set.Set Sentence,
    succedent :: Sentence
} deriving (Show, Eq, Read)

-- PROOFTREES BASICS
data SequentProof = SequentProof {
    seqContent :: Sequent,
    seqJustification :: String,
    subSeqProofs :: Maybe [SequentProof]
} deriving (Show, Eq, Read)

-- technically the more kosher way of doing things (compared to RuleSchema)
-- but not even that much more because this is for rule instsances, which are pretty useless
data SequentRule = SequentRule {
    ruleName :: String,
    premises :: [Sequent],
    conclusion :: Sequent
} deriving (Eq, Show, Read)

type RuleSchema = ([String], String)
andR :: RuleSchema
andR = (["Gamma => A", "Gamma => B"],
        "Gamma => A & B")
orR0 :: RuleSchema
orR0 = (["Gamma => A"],
        "Gamma => A v B")
orR1 :: RuleSchema
orR1 = (["Gamma => B"],
        "Gamma => A v B")
arrowR :: RuleSchema
arrowR = (["Gamma, A => B"],
        "Gamma => A -> B")
andL :: RuleSchema
andL = (["Gamma, A, B => C"], 
        "Gamma, A & B => C")
orL :: RuleSchema
orL = (["Gamma, A => C", "Gamma, B => C"], 
        "Gamma, A v B => C")
arrowL2 :: RuleSchema
arrowL2 = (["Gamma, C -> (D -> B) => E"], 
        "Gamma, (C & D) -> B => E")
arrowL3 :: RuleSchema
arrowL3 = (["Gamma, C -> B, D -> B => E"], 
        "Gamma, (C v D) -> B => E")
arrowL4 :: RuleSchema
arrowL4 = (["Gamma, C, D -> B => D", "Gamma, B => E"],
        "Gamma, (C -> D) -> B => E")
ax :: RuleSchema
ax = ([],
        "Gamma, P => P")
arrowL1 :: RuleSchema
arrowL1 = (["Gamma, P, B => E"],
        "Gamma, P -> B, P => E")

g4 :: Map.Map String RuleSchema
g4 = Map.fromList [
    ("Ax", ax), 
    ("L&", andL), ("R&", andR),
    ("Lv", orL), ("Rv0", orR0), ("Rv1", orR1),
    ("R->", arrowR),
    ("L->1", arrowL1), ("L->2", arrowL2), ("L->3", arrowL3), ("L->4", arrowL4)]

invertibleRules :: [String]
invertibleRules = ["Ax", "R->", "L&", "L->1", "L->2", "L->3", "R&", "Lv"]
noninvertibleRules :: [String]
noninvertibleRules = ["L->4", "Rv0", "Rv1"]

getRule :: String -> RuleSchema
getRule ruleStr = 
    case Map.lookup ruleStr g4 of
        Nothing -> error ("rule not in logic currently: " ++ ruleStr)
        Just rule -> rule

-- notice reversed order from isInstance
isInstanceStr :: String -> Sentence -> Bool
isInstanceStr schemaStr sent = 
    isInstance sent (parseIP schemaStr)

-- this function takes a schema, and returns a maybe with a matching sentence
-- the matching sentence is the principal formula (this is only for left rules)
getLMatch :: (Sentence -> Bool) -> Set.Set Sentence -> Maybe Sentence
getLMatch filterF ant = 
    Set.lookupMin (Set.filter filterF ant)

mkAnt :: Set.Set Sentence -> [Sentence] -> Set.Set Sentence
mkAnt baseAnt toAdd = foldl' (flip Set.insert) baseAnt toAdd

splitOnX :: String -> String -> [String]
splitOnX [] _ = error "splitOnX: empty delimiter"
splitOnX delim str = filter (/=[]) (go [] str)
  where
    n = length delim
    go acc [] = [reverse acc]
    go acc s@(c:cs)
      | delim `isPrefixOf` s = reverse acc : go [] (drop n s)
      | otherwise            = go (c:acc) cs

instantiateSchema :: String -> [(String, Sentence)] -> Sentence
instantiateSchema = parseWithSubst [andOp, orOp, cond] []

getSet :: (String -> Sentence) -> Set.Set Sentence -> String -> Set.Set Sentence
getSet func base setStr =
    mkAnt base (map func (filter (\str -> not ("Gamma" `isInfixOf` str)) (splitOnX "," setStr)))

parseSet :: String -> Set.Set Sentence
parseSet = getSet parseIP Set.empty

instantiateSet :: String -> Set.Set Sentence -> [(String, Sentence)] -> Set.Set Sentence
instantiateSet setStr gamma subst =
    getSet (\s -> instantiateSchema s subst) gamma setStr

parseSequent :: String -> Sequent
parseSequent seqStr =
    case splitOnX "=>" seqStr of 
        [succStr] -> Sequent Set.empty (parseIP succStr)
        [antStr, succStr] -> Sequent (parseSet antStr) (parseIP succStr)
        _ -> error "error in sequent parsing"

instantiateSequent :: String -> Set.Set Sentence -> [(String, Sentence)] -> Sequent
instantiateSequent seqStr gamma subst =
    let [antStr, succStr] = splitOnX "=>" seqStr in
    Sequent (instantiateSet antStr gamma subst) (instantiateSchema succStr subst)

-- assumes there is only one other thing besides Gamma
getLPrincipalStr :: RuleSchema -> String
getLPrincipalStr rule = 
    let [antStr, _] = splitOnX "=>" (snd rule) in        
    let [princ] = (filter (/= "Gamma") (splitOnX "," antStr)) in
    princ

getSuccStr :: RuleSchema -> String
getSuccStr rule =
    let [_, succStr] = splitOnX "=>" (snd rule) in
    succStr

-- we already have a witness for the principal formula in this function
getSubstL :: RuleSchema -> Sequent -> Sentence -> [(String, Sentence)]
getSubstL rule (Sequent ant succ) chosen = 
    getSubst chosen (parseIP (getLPrincipalStr rule)) ++ 
    getSubst succ (parseIP (getSuccStr rule))

getSubstAndGammaL :: RuleSchema -> Sequent -> Sentence -> ([(String, Sentence)], Set.Set Sentence)
getSubstAndGammaL rule seq chosenPrincipal =
    (getSubstL rule seq chosenPrincipal, Set.delete chosenPrincipal (antecedent seq))

getSubstR :: RuleSchema -> Sequent -> [(String, Sentence)]
getSubstR rule (Sequent ant succ) = 
    getSubst succ (parseIP (getSuccStr rule))

getSubstAndGammaR :: RuleSchema -> Sequent -> ([(String, Sentence)], Set.Set Sentence)
getSubstAndGammaR rule seq = 
    (getSubstR rule seq, antecedent seq)





-- USING RULES
useLRule :: RuleSchema -> Sequent -> Maybe [Sequent]
useLRule rule seq@(Sequent ant succ) =
    case getLMatch (isInstanceStr (getLPrincipalStr rule)) ant of
        Nothing -> Nothing
        Just chosen -> 
            let (subst, gamma) = getSubstAndGammaL rule seq chosen in
            Just (map (\s -> instantiateSequent s gamma subst) (fst rule))

useRRule :: RuleSchema -> Sequent -> Maybe [Sequent]
useRRule rule seq@(Sequent ant succ) =
    case isInstanceStr (getSuccStr rule) succ of
        False -> Nothing
        True -> 
            let (subst, gamma) = getSubstAndGammaR rule seq in
            Just (map (\seq -> instantiateSequent seq gamma subst) (fst rule))

useAx :: Sequent -> Maybe [Sequent]
useAx seq@(Sequent ant succ) = 
    if isAtomic succ && Set.member succ ant
        then Just []
        else Nothing

getArrowL1FilterF :: Set.Set Sentence -> Sentence -> Bool
getArrowL1FilterF ant =
    \s -> (isInstanceStr "P -> B" s) && (Set.member ((args s) !! 0) (Set.filter isAtomic ant))

useArrowL1 :: Sequent -> Maybe [Sequent]
useArrowL1 seq@(Sequent ant succ) =
    case getLMatch (getArrowL1FilterF ant) ant of
        Nothing -> Nothing
        Just chosen -> 
            let subst = getSubst chosen (parseIP "P -> B") ++ getSubst succ (parseIP (getSuccStr arrowL1)) in
            let gamma = Set.delete ((args chosen) !! 0) (Set.delete chosen ant) in
            Just (map (\s -> instantiateSequent s gamma subst) (fst arrowL1))

tryRule :: String -> Sequent -> Maybe [Sequent]
tryRule ruleStr seq
    | rule == ax = useAx seq
    | rule == arrowL1 = useArrowL1 seq
    | otherwise = 
        case parseIP (getSuccStr rule) of
            Atom a -> useLRule rule seq
            _ -> useRRule rule seq
    where rule = getRule ruleStr
        
tryInvertibleRules:: [String] -> Sequent -> Maybe (String, [Sequent])
tryInvertibleRules [] _ = Nothing
tryInvertibleRules (rl:rls) seq =
    case tryRule rl seq of
        Nothing -> tryInvertibleRules rls seq
        Just prems -> Just (rl, prems)

invertibleStep :: Sequent -> Maybe (String, [Sequent])
invertibleStep = tryInvertibleRules invertibleRules

tryNoninvertRule :: String -> Sequent -> Maybe SequentProof
tryNoninvertRule ruleName seq =
    case tryRule ruleName seq of
        Just subSeqs -> 
            let rest = SequentProof seq ruleName (Just (map g4ProofSearch subSeqs)) in
            if checkProof rest
                then Just rest
                else Nothing
        Nothing -> Nothing

tryNoninvertRules :: [String] -> Sequent -> SequentProof
tryNoninvertRules [] seq = SequentProof seq "NOT PROVABLE" Nothing
tryNoninvertRules (rl:rls) seq =
    case tryNoninvertRule rl seq of
        Just rest -> rest
        Nothing -> tryNoninvertRules rls seq

noninvertibleStep :: Sequent -> SequentProof
noninvertibleStep = tryNoninvertRules noninvertibleRules

g4ProofSearch :: Sequent -> SequentProof
g4ProofSearch seq =
    case invertibleStep seq of
        Just (j, subSeqs) -> SequentProof seq j (Just (map g4ProofSearch subSeqs))
        Nothing -> noninvertibleStep seq

checkProof :: SequentProof -> Bool
checkProof seqPf =
    case subSeqProofs seqPf of
        Nothing -> False
        Just sspfs -> and (map checkProof sspfs)

g4Test :: String -> Bool
g4Test = checkProof <$> g4ProofSearch <$> parseSequent 

condTests :: [String]
condTests = [
    "=> A -> A", -- identity
    "=> A -> (B -> A)", -- Simp
    "=> (A -> (B -> C)) -> ((A -> B) -> (A -> C))", -- Frege
    "=> A -> ((A -> B) -> B)", -- modus ponens (assertion)
    "=> (A -> B) -> ((B -> C) -> (A -> C))", -- suffixing (hyp syll)
    "=> (B -> C) -> ((A -> B) -> (A -> C))", -- prefixing (transitivity)
    "=> (A -> B) -> ((P -> (B -> C)) -> (P -> (A -> C)))" -- both suffixing and prefixing
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

testAll :: Bool
testAll = and(map g4Test (condTests ++ andTests ++ orTests))


compile_G4_G25 :: SequentProof -> SequentProof
compile_G4_G25 = undefined

compile_G2_ND :: SequentProof -> SequentProof
compile_G2_ND = undefined

compile_ND_Axioms :: SequentProof -> ProofTree
compile_ND_Axioms = undefined