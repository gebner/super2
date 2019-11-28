import super.prover_state

namespace super
open tactic

meta def inference.factoring : inference_rule | given :=
retrieve_packed $ do
(l1, i1) ← given.cls.literals.zip_with_index,
(l2, i2) ← given.cls.literals.zip_with_index,
guard $ i1 < i2,
guard $ l1.is_pos = l2.is_pos,
pure $ do
some () ← try_core (unify l1.formula l2.formula) | pure [],
pure [given.cls]

end super
