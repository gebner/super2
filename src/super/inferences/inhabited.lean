import super.prover_state super.resolve

namespace super
open tactic

meta def synth_via_type_class : expr → tactic (option expr)
| `(%%_ = %%_) := pure none
| ty := do
  (do inst ← mk_instance ty, pure inst) <|>
  (do inh ← mk_mapp ``default [ty, none], pure inh) <|>
  (do nonempty_ty ← mk_mapp ``nonempty [ty],
      inst ← mk_instance nonempty_ty,
      inh ← mk_mapp ``classical.choice [ty, inst],
      pure inh) <|>
  pure none

private meta def synth1_via_type_class (c : clause) : tactic clause :=
first $ c.literals.zip_with_index.reverse.map $ λ ⟨l, i⟩, do
  guard $ l.is_neg ∨ c.ty.num_neg_literals ≠ 0 ∨ c.ty.num_pos_literals > 1,
  some inst ← synth_via_type_class l.formula,
  trace inst,
  if l.is_pos then
    pure ⟨clause_type.atom l.formula, inst⟩
  else
    pure $ c.propg_pos i inst

meta def simplification.inhabited : simplification_rule | c := do
some c ← try_core (synth1_via_type_class c) | pure c,
simplification.inhabited c

meta def preprocessing.inhabited : preprocessing_rule :=
simplification.inhabited.as_preprocessing_rule

end super
