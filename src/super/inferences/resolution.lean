import super.prover_state super.resolve

namespace super
open tactic

private meta def get_selected_lits (cs : list derived_clause) : list (derived_clause × ℕ × literal) :=
do c ← cs, i ← c.selected, some l ← pure (c.cls.literals.nth i) | [], pure (c, i, l)

meta def inference.forward_resolution : inference_rule | given := do
active ← get_active,
retrieve_packed $ do
  (c1, i1, literal.pos a1) ← get_selected_lits active.values | [],
  (c2, i2, literal.neg a2) ← get_selected_lits [given] | [],
  pure $ do
    some _ ← try_core (unify a1 a2) | pure [],
    pure [clause.resolve c1.cls i1 c2.cls i2]

meta def inference.backward_resolution : inference_rule | given := do
active ← get_active,
retrieve_packed $ do
  (c1, i1, literal.pos a1) ← get_selected_lits [given] | [],
  (c2, i2, literal.neg a2) ← get_selected_lits active.values | [],
  pure $ do
    some _ ← try_core (unify a1 a2) | pure [],
    pure [clause.resolve c1.cls i1 c2.cls i2]

meta def inference.resolution : inference_rule | given :=
(++) <$> inference.forward_resolution given
     <*> inference.backward_resolution given

end super
