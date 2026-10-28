module Defs.Rules where

import Core
import Parse.Sentences

import Defs.Operators

import qualified Data.Map as Map



-- INFERENCE RULES
modusPonens :: InferenceRule
modusPonens = InferenceRule "Modus Ponens" (parse [] [] "P", Just (parse [cond] [] "P -> Q")) (parse [] [] "Q")

necessitation :: InferenceRule
necessitation = InferenceRule "Necessitation" (parse [] [] "P", Nothing) (parse [box] [] "L P")


-- I think this is what i had in mind
-- won't work bc pfc is repeated. idk if there's an easy way to do this
-- because derived rules don't just grow leaves; they grow branches. We need to know what the branches look like before
chainRulesStep :: (ProofTree -> ProofTree) -> (ProofTree -> ProofTree) -> ProofTree -> ProofTree
chainRulesStep derRule1 derRule2 (ProofTree pfc pfj spfs) =
    derRule2 (ProofTree pfc pfj [derRule1 (ProofTree pfc pfj spfs)])

chainRules :: [ProofTree -> ProofTree] -> ProofTree -> ProofTree
chainRules [] = id
chainRules (rl:remrls) = chainRulesStep rl (chainRules remrls)
    -- undefined
    -- what do we need to do? We need to:
        -- zero out the userNumbers of the result of trans1 (we should do that at the end?)
            -- we actually don't need to do that
        -- feed the last line of trans1's result to trans2
    -- hitting a roadblock. Usually, in transformations, you want to end up with the content of the current line. 
    -- with this way of doing things, you kind of lose the content of the current line, and you need to add
    -- intermediate contents. (The contents of the line you feed to the dummy transformant)
    -- Really, what you are doing is syntactic sugar at the proof level. We just need to insert a few lines, that's it
    -- the problem for the diamond derived rule is that it has a cited theorem and a derived rule. So yeah, we can make it
    -- so that the derived rule can cite theorems, but we can't make it so that the derived rule cites other derived rules. 
    -- not at the object level. But at the action level yeah. To do tht at the object level is odd