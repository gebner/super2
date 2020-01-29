import super.clause

namespace super

namespace clause

open tactic

meta def or_congr (c : clause) (fa fb : clause → tactic clause) : tactic clause :=
match c with
| ⟨clause_type.or a b, prf⟩ := do
  ae ← a.to_expr, ha ← mk_local_def ae.hyp_name_hint ae,
  be ← b.to_expr, hb ← mk_local_def be.hyp_name_hint be,
  ⟨a', prfa'⟩ ← fa ⟨a, ha⟩,
  ⟨b', prfb'⟩ ← fb ⟨b, hb⟩,
  match a', b' with
  | clause_type.ff, _ := do
    let hb' := `(@or.elim %%ae %%be _ %%prf
      %%(expr.mk_lambda ha `(@false.elim.{0} %%be %%prfa'))
      id),
    pure ⟨b', (expr.mk_lambda hb prfb').app' hb'⟩
  | _, clause_type.ff := do
    let ha' := `(@or.elim %%ae %%be _ %%prf
      id
      %%(expr.mk_lambda hb `(@false.elim.{0} %%ae %%prfb'))),
    pure ⟨a', (expr.mk_lambda ha prfa').app' ha'⟩
  | _, _ := do
    ⟨a', prfa'⟩ ← clause.to_prop ⟨a', prfa'⟩,
    ⟨b', prfb'⟩ ← clause.to_prop ⟨b', prfb'⟩,
    ae' ← a'.to_expr,
    be' ← b'.to_expr,
    pure ⟨clause_type.or a' b',
      `(@or.elim %%ae %%be (%%ae' ∨ %%be') %%prf
        %%(expr.mk_lambda ha `(@or.inl %%ae' %%be' %%prfa'))
        %%(expr.mk_lambda hb `(@or.inr %%ae' %%be' %%prfb')))⟩
  end
| _ := fail "or_congr"
end

meta def propg_pos : clause → ℕ → expr → tactic clause
| ⟨clause_type.ff, _⟩ _ _ := fail "propg_pos ff"
| ⟨clause_type.atom _, _⟩ _ _ := fail "propg_pos atom"
| ⟨clause_type.imp a b, prf⟩ 0 h := pure ⟨b, prf.app' h⟩
| ⟨clause_type.imp a b, prf⟩ (i+1) h := do
  l ← mk_local_def a.hyp_name_hint a,
  ⟨b', prf'⟩ ← propg_pos ⟨b, prf.app' l⟩ i h,
  pure ⟨clause_type.imp a b', expr.mk_lambda l prf'⟩
| c@⟨clause_type.or a b, prf⟩ i h := do
  let an := a.num_literals,
  if i < an then
    or_congr c (λ ca, propg_pos ca i h) pure
  else
    or_congr c pure (λ cb, propg_pos cb (i - an) h)
| ⟨clause_type.nonempty a, prf⟩ i h := do
  ha ← mk_mapp ``classical.choice [none, prf],
  propg_pos ⟨a, ha⟩ i h

meta def propg_neg : clause → ℕ → clause → ℕ → tactic clause
| ⟨clause_type.ff, _⟩ _ _ _ := fail "propg_neg ff"
| ⟨clause_type.atom _, _⟩ (i+1) _ _ := fail "propg_neg atom (i+1)"
| ⟨clause_type.atom _, prf⟩ 0 h j := propg_pos h j prf
| ⟨clause_type.imp _ _, _⟩ 0 _ _ := undefined_core "propg_neg imp 0"
| ⟨clause_type.imp a b, prf⟩ (i+1) h j := do
  ha ← mk_local_def a.hyp_name_hint a,
  ⟨b', prf'⟩ ← propg_neg ⟨b, prf.app' ha⟩ i h j,
  pure ⟨clause_type.imp a b', expr.mk_lambda ha prf'⟩
| c@⟨clause_type.or a b, prf⟩ i h j := do
  let an := a.literals.length,
  if i < an then
    or_congr c (λ ca, propg_neg ca i h j) pure
  else
    or_congr c pure (λ cb, propg_neg cb (i - an) h j)
| ⟨clause_type.nonempty a, prf⟩ i h j := do
  ha ← mk_mapp ``classical.choice [none, prf],
  propg_neg ⟨a, ha⟩ i h j

meta def resolve (a : clause) (ai : ℕ) (b : clause) (bi : ℕ) : tactic clause :=
on_exception (trace_call_stack >> trace (a, b)) $
clause.check_result_if_debug $ do
some (literal.pos al) ← pure (a.literals.nth ai) | fail "unknown literal",
some (literal.neg bl) ← pure (b.literals.nth bi) | fail "unknown literal",
is_def_eq al bl,
propg_neg a ai b bi

meta def mgu_resolve (a : clause) (ai : ℕ) (b : clause) (bi : ℕ) : tactic clause :=
clause.check_result_if_debug $ do
some (literal.pos al) ← pure (a.literals.nth ai) | fail "unknown literal",
some (literal.neg bl) ← pure (b.literals.nth bi) | fail "unknown literal",
unify al bl,
propg_neg a ai b bi

end clause

end super
