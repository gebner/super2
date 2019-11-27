import super.prover_state

namespace super

meta def simplification.forward_subsumption : simplification_rule | given := do
active ← get_active,
-- TODO TODO TODO
if ∃ a ∈ active.values, (a : derived_clause).cls.literals = given.literals then
  pure none
else
  pure given

meta def preprocessing.forward_subsumption : preprocessing_rule :=
simplification.forward_subsumption.as_preprocessing_rule

meta def preprocessing.subsumption_interreduction : preprocessing_rule | cs :=
-- TODO TODO TODO
pure $ cs.dup_by_native (λ c, c.ty.to_expr)

end super
