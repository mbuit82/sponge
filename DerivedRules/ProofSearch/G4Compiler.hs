module DerivedRules.ProofSearch.G4Compiler where

import Core 
import Parse.Sentences
import Defs.Operators
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
                    [ProofTree (p "P") "Assumption" [],
                    ProofTree (p "P -> B") "Assumption" []] in
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
        "R~" -> undefined -- would have to be some sort of neg intro?
        "L~1" -> 
            ProofTree 
                (p "E")
                "Modus Ponens"
                [ProofTree (p "P") "Assumption" [],
                ProofTree (p "P -> E") "Modus Ponens"
                    [ProofTree (p "~P") "Assumption" [],
                    ProofTree (p "~P -> (P -> E)") "Negation Elim" []]]
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
        "L~5" -> undefined


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