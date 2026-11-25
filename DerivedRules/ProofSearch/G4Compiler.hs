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

replaceNotA :: Sentence -> Sentence -> Sentence
replaceNotA replacement (Atom "NotA") = replacement
replaceNotA replacement (Atom a) = Atom a
replaceNotA replacement (OpNode op args) =
    OpNode op (map (replaceNotA replacement) args)

replaceNotAInTree' :: Sentence -> ProofTree -> ProofTree
replaceNotAInTree' sent (ProofTree pfc pfj spfs) =
    ProofTree (replaceNotA sent pfc) pfj spfs

replaceNotAInTree :: Sentence -> ProofTree -> ProofTree
replaceNotAInTree sent = applyOverTree (replaceNotAInTree' sent)

compileG4 :: SequentProof -> ProofTree
compileG4 seqPf@(SequentProof seqpfc rl subseqpfs) =
    let p = compilerParseHelper (getStepSubst seqPf) in
    case (seqRuleName rl) of
        "Ax" -> ProofTree (getSuccSent seqpfc) "Assumption" []
        "R&" -> 
            let [aRecCall, bRecCall] = map compileG4 (fromJust subseqpfs) in
            ProofTree (getSuccSent seqpfc) "Modus Ponens"
                [bRecCall,
                ProofTree (p "B -> (A & B)") "Modus Ponens" 
                    [aRecCall,
                    ProofTree (p "A -> (B -> (A & B))") "And Intro" []]]
        "L&" ->
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let aDerivation = 
                    ProofTree (p "A") "Modus Ponens" 
                        [(ProofTree (p "A & B") "Assumption" []), 
                        ProofTree (p "(A & B) -> A") "And Elim L" []] in
            let bDerivation = 
                    ProofTree (p "B") "Modus Ponens" 
                        [(ProofTree (p "A & B") "Assumption" []),
                        ProofTree (p "(A & B) -> B") "And Elim R" []] in
            composeDerivations (mkSentSubsts [aDerivation, bDerivation]) recCall
        "Rv0" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            ProofTree (getSuccSent seqpfc) "Modus Ponens"
                [recCall,
                ProofTree (p "A -> (A v B)") "Or Intro L" []]
        "Rv1" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            ProofTree (getSuccSent seqpfc) "Modus Ponens"
                [recCall,
                ProofTree (p "B -> (A v B)") "Or Intro R" []]
        "Lv" ->
            let [aRecCall, bRecCall] = map compileG4 (fromJust subseqpfs) in
            ProofTree (getSuccSent seqpfc) "Modus Ponens"
                [ProofTree (p "A v B") "Assumption" [],
                ProofTree (p "(A v B) -> C") "Modus Ponens"
                    [bRecCall,
                    ProofTree (p "(B -> C) -> ((A v B) -> C)") "Modus Ponens"
                        [aRecCall,
                        ProofTree (p "(A -> C) -> ((B -> C) -> ((A v B) -> C))") "Or Elim" []]]]
        "R->" ->
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let [deductionArg] = getNEmbeddedAntecedents cond 1 (getSuccSent seqpfc) in
            useDeduction deductionArg recCall
        "L->1" ->
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let bDerivation = 
                    ProofTree (p "B") "Modus Ponens"
                        [ProofTree (p "A") "Assumption" [],
                        ProofTree (p "A -> B") "Assumption" []] in
            composeDerivations (mkSentSubsts [bDerivation]) recCall
        "L->2" ->
            -- what would be nice here is to leave the citation of currying as an open term, 
            -- but only leaving one deduction open
            -- I wonder if that could be another optimization pass? 
            -- basically you want to check if you are doing modus ponens P -> Q, P with a P that is an assumption and a P -> Q that was formed from an open term, then you want to eliminate that detour
            -- this is basically normalization
            -- this issue is that you don't have a representation of open terms
            -- are these two differen things? normalization would be eliminating successive MP and deduction occurrences. 
            -- the only way I can think of doing this I'm not sure if it's nice:
            -- it would be to have a prooftree node that represents use of deduction. 
            -- that way you could literally have successive intro/elim terms you can syntactically eliminate. 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let curriedDerivation = 
                    ProofTree (p "C -> (D -> B)") "Modus Ponens"
                        [ProofTree (p "(C & D) -> B") "Assumption" [],
                        ProofTree (p "((C & D) -> B) -> (C -> (D -> B))") "citing currying (from minimal)" []] in
            composeDerivations (mkSentSubsts [curriedDerivation]) recCall
        "L->3" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let cbDerivation = 
                    ProofTree (p "C -> B") "Modus Ponens"
                        [ProofTree (p "(C v D) -> B") "Assumption" [],
                        ProofTree (p "((C v D) -> B) -> (C -> B)") "citing or_antecedent_left (from minimal)" []] in
            let dbDerivation = 
                    ProofTree (p "D -> B") "Modus Ponens"
                        [ProofTree (p "(C v D) -> B") "Assumption" [],
                        ProofTree (p "((C v D) -> B) -> (D -> B)") "citing or_antecedent_right (from minimal)" []] in
            composeDerivations (mkSentSubsts [cbDerivation, dbDerivation]) recCall
        "L->4" ->
            let [cdRecCall, rootRecCall] = map compileG4 (fromJust subseqpfs) in
            let bUnderDDerivation = 
                    ProofTree (p "B") "Modus Ponens"
                        [ProofTree (p "C -> D") "Modus Ponens"
                            [ProofTree (p "D") "Assumption" [],
                            ProofTree (p "D -> (C -> D)") "Simp" []],
                        ProofTree (p "(C -> D) -> B") "Assumption" []] in
            let dbDerivation = useDeduction (p "D") bUnderDDerivation in
            let cdDerivation = composeDerivations (mkSentSubsts [dbDerivation]) cdRecCall in
            let bDerivation = 
                    ProofTree (p "B") "Modus Ponens"
                        [cdDerivation,
                        ProofTree (p "(C -> D) -> B") "Assumption" []] in
            composeDerivations (mkSentSubsts [bDerivation]) rootRecCall
        "L->5" -> -- ~C -> B
            let [nCDerivation, eDerivation] = map compileG4 (fromJust subseqpfs) in
            let bDerivation = 
                    ProofTree (p "B") "Modus Ponens"
                        [nCDerivation,
                        ProofTree (p "~C -> B") "Assumption" []] in
            composeDerivations (mkSentSubsts [bDerivation]) eDerivation
        "R~" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            ProofTree (p "~A") "Modus Ponens"
                    [useDeduction (p "A") (replaceNotAInTree (p "~A") recCall),
                    ProofTree (p "(A -> ~A) -> ~A") "citing reductio (from intuitionistic)" []]
        "L~1" -> 
            ProofTree (p "E") "Modus Ponens"
                [ProofTree (p "A") "Assumption" [],
                ProofTree (p "A -> E") "Modus Ponens"
                    [ProofTree (p "~A") "Assumption" [],
                    ProofTree (p "~A -> (A -> E)") "Negation Elim" []]]
        "L~2" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let cndDerivation = 
                    ProofTree (p "C -> ~D") "Modus Ponens"
                        [ProofTree (p "~(C & D)") "Assumption" [],
                        ProofTree (p "~(C & D) -> (C -> ~D)") "citing neg_and (from intuitionistic)" []] in
            composeDerivations (mkSentSubsts [cndDerivation]) recCall
        "L~3" -> 
            let [recCall] = map compileG4 (fromJust subseqpfs) in
            let nCDerivation = 
                    ProofTree (p "~C") "Modus Ponens"
                        [ProofTree (p "~(C v D)") "Assumption" [],
                        ProofTree (p "~(C v D) -> ~C") "applying neg_or_left (from intuitionistic)" []] in
            let nDDerivation = 
                    ProofTree (p "~D") "Modus Ponens"
                        [ProofTree (p "~(C v D)") "Assumption" [],
                        ProofTree (p "~(C v D) -> ~D") "applying neg_or_right (from intuitionistic)" []] in
            composeDerivations (mkSentSubsts [nCDerivation, nDDerivation]) recCall
        "L~4" -> -- ~(C -> D)
            let [recCall] = map compileG4 (fromJust subseqpfs) in 
            let nDDerivation = 
                    ProofTree (p "~D") "Modus Ponens"
                        [ProofTree (p "~(C -> D)") "Assumption" [],
                        ProofTree (p "~(C -> D) -> ~D") "Modus Ponens" 
                            [ProofTree (p "D -> (C -> D)") "Simp" [],
                            ProofTree (p "(D -> (C -> D)) -> (~(C -> D) -> ~D)") "citing contrapositive_forward (from intuitionistic)" []]] in
            let cdDerivation = composeDerivations (mkSentSubsts [nDDerivation]) recCall in
            ProofTree (p "E") "Modus Ponens"
                [cdDerivation,
                ProofTree (p "(C -> D) -> E") "Modus Ponens" 
                    [ProofTree (p "~(C -> D)") "Assumption" [],
                    ProofTree (p "~(C -> D) -> ((C -> D) -> E)") "Negation Elim" []]]
        "L~5" -> -- is kinda similar to the L~4 case
            let [recCall] = map compileG4 (fromJust subseqpfs) in -- a derivation of ~C
            ProofTree (p "E") "Modus Ponens"
                [recCall,
                ProofTree (p "~C -> E") "Modus Ponens"
                    [ProofTree (p "~~C") "Assumption" [],
                    ProofTree (p "~~C -> (~C -> E)") "Negation Elim" []]]
        "NOT PROVABLE" -> error "trying to compile a proof for an unprovable statement"

g4TheoremSearch :: G4Logic -> Sentence -> SequentProof
g4TheoremSearch g4Logic sent = g4ProofSearch g4Logic (Sequent Set.empty (Set.fromList [sent]))

proofSearch :: G4Logic -> Sentence -> Maybe ProofTree
proofSearch g4Logic sent =
    let search = g4TheoremSearch g4Logic sent in
    if checkSeqProof search == True
        then Just (compileG4 search)
        else Nothing

iProofSearch :: Sentence -> Maybe ProofTree
iProofSearch = proofSearch g4ip

cProofSearch :: Sentence -> ProofTree
cProofSearch sent = 
    case iProofSearch sent of
        Just pf -> pf
        Nothing -> 
            case iProofSearch (OpNode negOp [OpNode negOp [sent]]) of
                Nothing -> error ("seems " ++ show sent ++ " is not a classical theorem")
                Just dnSearch -> 
                    ProofTree (sent) "Modus Ponens"
                        [dnSearch,
                        ProofTree (applySubst [("P", sent)] (axiomContent dne)) "DNE" []]

useProofSearch' :: ProofTree -> ProofTree
useProofSearch' pfTree@(ProofTree pfc pfj _) =
    case pfj of
        "classical result" -> cProofSearch pfc
        "intuitionistic result" -> 
            case iProofSearch pfc of
                Nothing -> error ("seems " ++ show pfc ++ " is not an intuitionistic theorem")
                Just pf -> pf
        _ -> pfTree

useProofSearch :: ProofTree -> ProofTree
useProofSearch = applyOverTree useProofSearch'

-- ProofTree {pfContent = ~((P & ~(P))), pfJustification = "Negation Intro", subProofs = [
--         ProofTree {pfContent = ((P & ~(P)) -> P), pfJustification = "And Elim L", subProofs = []},
--         ProofTree {pfContent = ((P & ~(P)) -> ~(P)), pfJustification = "And Elim R", subProofs = []}]}

-- ProofTree {pfContent = (~((A v B)) -> ~(B)), pfJustification = "applying contrapositive_forward (from intuitionistic)", subProofs = [
--     ProofTree {pfContent = (B -> (A v B)), pfJustification = "Or Intro R", subProofs = []}]}

-- keeping for posterity
newCaseNegR :: SequentProof -> (String -> Sentence) -> ProofTree
newCaseNegR (SequentProof seqpfc seqpfj subseqpfs) p = 
    let [recCall] = map compileG4 (fromJust subseqpfs) in
        ProofTree
            (p "~A")
            "Modus Ponens"
                [useDeduction (p "A") (replaceNotAInTree (p "~A") recCall),
                ProofTree (p "(A -> ~A) -> ~A") "citing reductio (from intuitionistic)" []]

oldCaseNegR :: SequentProof -> (String -> Sentence) -> ProofTree
oldCaseNegR (SequentProof seqpfc seqpfj subseqpfs) p = 
    case Set.lookupMin (getBotDerivations (antecedent seqpfc) (p "A")) of
                Nothing -> error ("R~ MESSED UP\n" ++ show seqpfc)
                Just (x, xSeqDer, nxSeqDer) -> 
                    let negIntro = applySubst [("P", (p "A")), ("Q", x)] (axiomContent negI) in
                    let axDer = useDeduction (p "A") (compileG4 xSeqDer) in
                    let anxDer = useDeduction (p "A") (compileG4 nxSeqDer) in 
                    let consequentOfNegElim = (args negIntro) !! 1 in
                    ProofTree 
                        (p "~A")
                        "Modus Ponens"
                        [anxDer,
                        ProofTree consequentOfNegElim "Modus Ponens"
                            [axDer,
                            ProofTree negIntro "Negation Intro" []]]

getSubFormulas :: Sentence -> Set.Set Sentence
getSubFormulas s@(Atom a) = Set.singleton s
getSubFormulas s@(OpNode op args) = 
    Set.union (Set.singleton s) (Set.unions (map getSubFormulas args))

getAllSubFormulas :: Set.Set Sentence -> Set.Set Sentence
getAllSubFormulas gamma = Set.unions (Set.map getSubFormulas gamma)

derivesBot :: Set.Set Sentence -> Sentence -> Sentence -> Maybe (Sentence, SequentProof, SequentProof)
derivesBot gamma a tgtX =
        let posResult = g4ProofSearch g4ip (Sequent (Set.union gamma (Set.singleton a)) (Set.singleton tgtX)) in
        case checkSeqProof posResult of
            False -> Nothing
            True -> 
                let negResult = g4ProofSearch g4ip (Sequent (Set.union gamma (Set.singleton a)) (Set.singleton (OpNode negOp [tgtX]))) in
                case checkSeqProof negResult of
                    False -> Nothing
                    True -> Just (tgtX, posResult, negResult)

getBotDerivations :: Set.Set Sentence -> Sentence -> Set.Set (Sentence, SequentProof, SequentProof)
getBotDerivations gamma a =
    Set.map fromJust (Set.filter (/= Nothing) (Set.map (derivesBot gamma a) (getAllSubFormulas (Set.union gamma (Set.singleton a)))))