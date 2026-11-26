module DerivedRules.Utils where

import Core

import qualified Data.Map as Map
import Data.Functor.Identity

applyOverTreeM :: Monad m => (ProofTree -> m ProofTree) -> ProofTree -> m ProofTree
applyOverTreeM func (ProofTree pfc pfj spfs) = do
    spfsUpdated <- mapM (applyOverTreeM func) spfs
    func (ProofTree pfc pfj spfsUpdated)

applyOverTree :: (ProofTree -> ProofTree) -> ProofTree -> ProofTree
applyOverTree func = runIdentity . applyOverTreeM (Identity . func)

applyPfs :: ProofTree -> [ProofTree] -> ProofTree
applyPfs pfTree [] = pfTree
applyPfs pfTree (spf:rem) = 
    applyPfs (ProofTree consq "Modus Ponens" [spf, pfTree]) rem 
    where 
        [_, consq] = args (pfContent pfTree)

mkSentSubsts :: [ProofTree] -> [(Sentence, ProofTree)]
mkSentSubsts = map (\pft -> (pfContent pft, pft))



-- are used for conditionals in strengthening and K derived rules, but are more general processes so leaving here
getNEmbeddedAntecedents :: Operator -> Int -> Sentence -> [Sentence]
getNEmbeddedAntecedents op 0 _ = []
getNEmbeddedAntecedents op n (OpNode op' [arg1, arg2])
    | op' == op = arg1 : getNEmbeddedAntecedents op (n-1) arg2
    | otherwise = error ("getting embedded left args for operator " ++ (show op))

getNthConsequent :: Operator -> Int -> Sentence -> Sentence
getNthConsequent op 0 sent = sent
getNthConsequent op n (OpNode op' [arg1, arg2])
    | op' == op = getNthConsequent op (n-1) arg2
    | otherwise = error "can only get Nth consequent on a conditional"
getNthConsequent op n sent = 
    error ("dunno what went wrong. debugging info: getNthConsequent, " ++ show n ++ ", " ++ show sent)

getEmbeddedAntecedentsUpTo :: Operator -> Sentence -> Sentence -> [Sentence]
getEmbeddedAntecedentsUpTo op stopSent sent
    | sent == stopSent = []
    | otherwise = case sent of
        Atom a -> error ("supposed to have reached stopSent " ++ show stopSent ++ " but never did?")
        (OpNode op' [arg1, arg2]) -> 
            if op' == op
                then arg1 : getEmbeddedAntecedentsUpTo op stopSent arg2
                else error ("can only get all antecedents on a chain of conditionals (sent, stopSent)=" ++ show (sent, stopSent))
        _ -> error ("supposed to have reached stopSent " ++ show stopSent ++ " but never did?")

-- the last element of the returned list is the stuff you need for weakening
getEmbeddedConsequentAfter :: Operator -> Sentence -> Sentence -> Sentence
getEmbeddedConsequentAfter op stopSent (Atom a) = error ("supposed to have reached stopSent " ++ show stopSent ++ " but never did?")
getEmbeddedConsequentAfter op stopSent (OpNode op' [arg1, arg2])
    | arg1 == stopSent = arg2
    | op' == op = getEmbeddedConsequentAfter op stopSent arg2
    | otherwise = error "can only get all antecedents on a chain of conditionals"
getEmbeddedConsequentAfter op stopSent sent = error (show op ++ "\n" ++ show stopSent ++ "\n" ++ show sent)

makeChain :: Operator -> [Sentence] -> Sentence -> Sentence
makeChain op [] consq = consq
makeChain op (p:rem) consq = OpNode op [p, makeChain op rem consq]

getChainLength :: Operator -> Sentence -> Int
getChainLength op (OpNode op' [arg1, arg2])
    | op == op' = 1 + getChainLength op arg2
    | otherwise = 0
getChainLength op _ = 0

axiomsDict :: Logic -> Map.Map String Axiom
axiomsDict logic = Map.fromList (map (\a -> (axiomName a, a)) (axioms logic))

-- NOTE: I don't like this here. Feel like it's too big a thing to be tucked away here. 
-- but needs to not be in UseDerivedRules in order to avoid import errors
-- inefficient with passing a list that's made into a map but useful in Sequents for clarity of code
-- also inefficient with checking every node. In theory, if you have an efficient proof, should not matter
-- particularly, if you've already derived an assumption, it will be less efficient
composeDerivations :: [(Sentence, ProofTree)] -> ProofTree -> ProofTree
composeDerivations pairs (ProofTree pfc pfj spfs) =
    case (Map.lookup pfc (Map.fromList pairs)) of
        Nothing -> ProofTree pfc pfj (map (composeDerivations pairs) spfs)
        Just newDerivation -> newDerivation
-- -- OLD. more efficient. Changed to make good for Sequents
-- derivationComposition pairs pft@(ProofTree pfc "Assumption" spfs) =
--     case (Map.lookup pfc (Map.fromList pairs)) of
--         Nothing -> pft
--         Just newDerivation -> newDerivation
-- derivationComposition pairs (ProofTree pfc pfj spfs) =
--     ProofTree pfc pfj (map (derivationComposition pairs) spfs)