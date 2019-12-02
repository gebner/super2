import super.prover_state super.subsume

namespace super

meta def simplification.forward_subsumption : simplification_rule | given := do
active ← get_active,
s ← tactic.read,
if ∃ act ∈ active.values, does_subsume_pure s (act : derived_clause).cls given then
  pure none
else
  pure given

meta def preprocessing.forward_subsumption : preprocessing_rule :=
simplification.forward_subsumption.as_preprocessing_rule

private meta def interreduce {α} (subsumes : α → α → bool) : list α → list α
| [] := []
| (x :: ys) :=
  let ys := ys.filter (λ y, ¬ subsumes x y),
      ys := interreduce ys in
  if ∃ y ∈ ys, subsumes y x then ys else x :: ys

meta def preprocessing.subsumption_interreduction : preprocessing_rule | cs := do
s ← tactic.read,
pure $ interreduce (does_subsume_pure s) cs

meta def inference.backward_subsumption : inference_rule | given := do
active ← get_active,
s ← tactic.read,
let subsumed := active.values.filter $ λ act,
  act.id ≠ given.id ∧ does_subsume_pure s given.cls act.cls,
subsumed.mmap' $ λ ss, remove_redundant ss.id,
pure []

end super
