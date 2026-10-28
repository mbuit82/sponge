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

makeModusPonensLines :: [ProofTree] -> ProofTree -> ProofTree
makeModusPonensLines [] pfTree = pfTree
makeModusPonensLines (spf:rem) pfTree = 
    makeModusPonensLines rem (ProofTree consq "Modus Ponens" [spf, pfTree])
    where 
        [_, consq] = args (pfContent pfTree)


-- are used for conditionals in strengthening and K derived rules, but are more general processes so leaving here
getNEmbeddedAntecedents :: Operator -> Int -> Sentence -> [Sentence]
getNEmbeddedAntecedents op 0 _ = []
getNEmbeddedAntecedents op n (OpNode op' [arg1, arg2])
    | op' == op = arg1 : getNEmbeddedAntecedents op (n-1) arg2
    | otherwise = error "can only get N antecedents on a conditional"

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

makeChain :: Operator -> [Sentence] -> Sentence -> Sentence
makeChain op [] consq = consq
makeChain op (p:rem) consq = OpNode op [p, makeChain op rem consq]

getChainLength :: Operator -> Sentence -> Int
getChainLength op (OpNode op' [arg1, arg2])
    | op == op' = 1 + getChainLength op arg2
    | otherwise = 0
getChainLength op _ = 0