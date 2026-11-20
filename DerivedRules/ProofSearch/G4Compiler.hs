module DerivedRules.ProofSearch.G4Compiler where

import Core 
import Parse.Sentences
import Defs.Operators
import Defs.Axioms
import DerivedRules.Utils
import DerivedRules.Deduction
import DerivedRules.ProofSearch.Sequents

import qualified Data.Set as Set
import Data.Maybe

getSuccSent :: Sequent -> Sentence
getSuccSent (Sequent _ succ) = (fromJust (Set.lookupMin succ))

-- this should work, but defensively adding an error in case it doesn't so it fails
getStepSubst :: SequentProof -> [(String, Sentence)]
getStepSubst seqPf@(SequentProof seqpfc rl subseqpfs) =
    case tryUnifySeqs (seqConclusion rl) seqpfc of
        Nothing -> error "something's wrong"
        Just subst -> subst

-- really consider changing the order of substitutions in parseWithSubst
-- that's the only reason this helper exists
compilerParseHelper :: [(String, Sentence)] -> String -> Sentence
compilerParseHelper subst str = parseWithSubst [andOp, orOp, cond, negOp] [] str subst

mkSentSubsts :: [ProofTree] -> [(Sentence, ProofTree)]
mkSentSubsts = map (\pft -> (pfContent pft, pft))

getSubFormulas :: Sentence -> Set.Set Sentence
getSubFormulas s@(Atom a) = Set.singleton s
getSubFormulas s@(OpNode op args) = 
    Set.union (Set.singleton s) (Set.unions (map getSubFormulas args))

getAllSubFormulas :: Set.Set Sentence -> Set.Set Sentence
getAllSubFormulas gamma = 
    Set.unions (Set.map getSubFormulas gamma)

derivesBot :: Set.Set Sentence -> Sentence -> Sentence -> Maybe (Sentence, SequentProof, SequentProof)
derivesBot gamma a tgtX =
    let posResult = g4ProofSearch g4ip (Sequent gamma (Set.singleton (OpNode cond [a, tgtX]))) in
    case checkSeqProof posResult of
        False -> Nothing
        True -> 
            let negResult = g4ProofSearch g4ip (Sequent gamma (Set.singleton (OpNode cond [a, OpNode negOp [tgtX]]))) in
            case checkSeqProof negResult of
                False -> Nothing
                True -> Just (tgtX, posResult, negResult)

getBotDerivations :: Set.Set Sentence -> Sentence -> Set.Set (Sentence, SequentProof, SequentProof)
getBotDerivations gamma a =
    Set.map fromJust (Set.filter (/= Nothing) (Set.map (derivesBot gamma a) (getAllSubFormulas gamma)))
    
-- I think there are some edge cases to this not working. 
-- particularly, deduct the same arg twice. Stupid, but still an edge case. 
-- e.g. (A -> (A -> A)) would potentially be funny
-- but it wouldn't even tbh one of the things would just get overridden bc substs become maps
-- I actually think that issue may come up earlier, in Deduction.hs
compileG4 :: SequentProof -> ProofTree
compileG4 seqPf@(SequentProof seqpfc rl subseqpfs) =
    let p = compilerParseHelper (getStepSubst seqPf) in -- I think lazy eval makes this good :D
    case (seqRuleName rl) of
        "Ax" -> ProofTree (getSuccSent seqpfc) "Assumption" []
        "R&" -> 
            let [aRecCall, bRecCall] = map compileG4 (fromJust subseqpfs) in
            ProofTree
                (getSuccSent seqpfc)
                "Modus Ponens"
                    [bRecCall,
                    ProofTree (p "B -> (A & B)") "Modus Ponens" 
                        [aRecCall,
                        ProofTree (p "A -> (B -> (A & B))") "And Intro" []]]
        "L&" ->
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let aDerivation = ProofTree 
                    (p "A") 
                    "Modus Ponens" 
                    [(ProofTree (p "A & B") "Assumption" []), (ProofTree (p "(A & B) -> A") "And Elim L" [])] in
            let bDerivation = ProofTree 
                    (p "B") 
                    "Modus Ponens" 
                    [(ProofTree (p "A & B") "Assumption" []), (ProofTree (p "(A & B) -> B") "And Elim R" [])] in
            composeDerivations (mkSentSubsts [aDerivation, bDerivation]) recCall
        "Rv0" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            ProofTree 
                (getSuccSent seqpfc)
                "Modus Ponens"
                    [recCall,
                    ProofTree (p "A -> (A v B)") "Or Intro L" []]
        "Rv1" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            ProofTree 
                (getSuccSent seqpfc)
                "Modus Ponens"
                    [recCall,
                    ProofTree (p "B -> (A v B)") "Or Intro R" []]
        "Lv" ->
            let [aRecCall, bRecCall] = map compileG4 (fromJust subseqpfs) in
            ProofTree 
                (getSuccSent seqpfc)
                "Modus Ponens"
                [ProofTree (p "A v B") "Assumption" [],
                ProofTree (p "(A v B) -> C") "Modus Ponens"
                    [bRecCall,
                    ProofTree (p "(B -> C) -> ((A v B) -> C)") "Modus Ponens"
                        [aRecCall,
                        ProofTree (p "(A -> C) -> ((B -> C) -> ((A v B) -> C))") "Or Elim" []]]]
        "R->" -> -- think about: could instead have it collect deduction args?
        -- you would use makeDeductionsFunc, and have this always return a list of deduction args you're keeping track of
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let [deductionArg] = getNEmbeddedAntecedents cond 1 (getSuccSent seqpfc) in
            useDeduction deductionArg recCall
        "L->1" ->
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let bDerivation = ProofTree
                    (p "B")
                    "Modus Ponens"
                    [ProofTree (p "A") "Assumption" [],
                    ProofTree (p "A -> B") "Assumption" []] in
            composeDerivations (mkSentSubsts [bDerivation]) recCall
        "L->2" ->
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let curriedDerivation = ProofTree
                    (p "C -> (D -> B)")
                    "Modus Ponens"
                    [ProofTree (p "(C & D) -> B") "Assumption" [],
                    ProofTree (p "((C & D) -> B) -> (C -> (D -> B))") "citing currying (from minimal)" []] in
            composeDerivations (mkSentSubsts [curriedDerivation]) recCall
        "L->3" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let cbDerivation = ProofTree
                    (p "C -> B")
                    "Modus Ponens"
                        [ProofTree (p "(C v D) -> B") "Assumption" [],
                        ProofTree (p "((C v D) -> B) -> (C -> B)") "citing or_antecedent_left (from minimal)" []] in
            let dbDerivation = ProofTree 
                    (p "D -> B")
                    "Modus Ponens"
                        [ProofTree (p "(C v D) -> B") "Assumption" [],
                        ProofTree (p "((C v D) -> B) -> (D -> B)") "citing or_antecedent_right (from minimal)" []] in
            composeDerivations (mkSentSubsts [cbDerivation, dbDerivation]) recCall
        "L->4" ->
            let [cdRecCall, rootRecCall] = map compileG4 (fromJust subseqpfs) in
            let bUnderDDerivation = ProofTree
                    (p "B")
                    "Modus Ponens"
                    [ProofTree (p "C -> D") "Modus Ponens"
                        [ProofTree (p "D") "Assumption" [],
                        ProofTree (p "D -> (C -> D)") "Simp" []],
                    ProofTree (p "(C -> D) -> B") "Assumption" []] in
            let dbDerivation = useDeduction (p "D") bUnderDDerivation in
            let cdDerivation = composeDerivations (mkSentSubsts [dbDerivation]) cdRecCall in
            let bDerivation = ProofTree 
                    (p "B")
                    "Modus Ponens"
                    [cdDerivation,
                    ProofTree (p "(C -> D) -> B") "Assumption" []] in
            composeDerivations (mkSentSubsts [bDerivation]) rootRecCall
        "L->5" -> undefined
        "R~" -> 
            case Set.lookupMin (getBotDerivations (antecedent seqpfc) (p "A")) of
                Nothing -> error "fucked up in R~ compiler case search for bot case"
                Just (x, axSeqDer, aNotXSeqDer) -> 
                    let negElim = applySubst [("P", (p "A")), ("Q", x)] (axiomContent negE) in
                    let consequentOfNegElim = (args negElim) !! 1 in
                    ProofTree 
                        (p "~A")
                        "Modus Ponens"
                        [compileG4 aNotXSeqDer,
                        ProofTree consequentOfNegElim "Modus Ponens"
                            [compileG4 axSeqDer,
                            ProofTree negElim "Negation Elim" []]]
        "L~1" -> 
            ProofTree 
                (p "E")
                "Modus Ponens"
                [ProofTree (p "A") "Assumption" [],
                ProofTree (p "A -> E") "Modus Ponens"
                    [ProofTree (p "~A") "Assumption" [],
                    ProofTree (p "~A -> (A -> E)") "Negation Elim" []]]
        "L~2" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let cndDerivation = ProofTree
                    (p "C -> ~D")
                    "Modus Ponens"
                    [ProofTree (p "~(C & D)") "Assumption" [],
                    ProofTree (p "~(C & D) -> (C -> ~D)") "citing neg_and (from intuitionistic)" []] in
            composeDerivations (mkSentSubsts [cndDerivation]) recCall
        "L~3" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let nCDerivation = ProofTree
                    (p "~C")
                    "Modus Ponens"
                        [ProofTree (p "~(C v D)") "Assumption" [],
                        ProofTree (p "~(C v D) -> ~C") "applying neg_or_left (from intuitionistic)" []] in
            let nDDerivation = ProofTree
                    (p "~D")
                    "Modus Ponens"
                        [ProofTree (p "~(C v D)") "Assumption" [],
                        ProofTree (p "~(C v D) -> ~D") "applying neg_or_right (from intuitionistic)" []] in
            composeDerivations (mkSentSubsts [nCDerivation, nDDerivation]) recCall
        "L~4" -> undefined
        "L~5" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in -- a derivation of ~C
             ProofTree
             (p "E")
             "Modus Ponens"
                [recCall,
                ProofTree (p "~C -> E") "Modus Ponens"
                    [ProofTree (p "~~C") "Assumption" [],
                    ProofTree (p "~~C -> (~C -> E)") "Negation Elim" []]]
        "NOT PROVABLE" -> error "trying to compile a proof for an unprovable statement"


g4TheoremSearch :: G4Logic -> Sentence -> SequentProof
g4TheoremSearch g4Logic sent = g4ProofSearch g4Logic (Sequent Set.empty (Set.fromList [sent]))

proofSearch :: G4Logic -> Sentence -> ProofTree
-- proofSearch g4Logic = compileG4 . (g4TheoremSearch g4Logic)
-- with classical stuff it'd look something like this
proofSearch g4Logic sent =
    let search = g4TheoremSearch g4Logic sent in
    if checkSeqProof search == True
        then compileG4 search
        else error (show sent ++ " is not a classical result it seems")

-- TODO: as soon as you finish the compiler, you can change this to g4ip
useProofSearch' :: ProofTree -> ProofTree
useProofSearch' pfTree =
    if (pfJustification pfTree) == "classical result"
        then proofSearch g4ip (pfContent pfTree)
        else pfTree

useProofSearch :: ProofTree -> ProofTree
useProofSearch = applyOverTree useProofSearch'