import super.clause

noncomputable def or.elim' {a b : Prop} {c : Sort*} :
  a ∨ b → (a → c) → (b → c) → c :=
λ ab ac bc,
match classical.prop_decidable a with
| decidable.is_true h := ac h
| decidable.is_false h := bc (ab.elim (λ ha, (h ha).elim) id)
end

namespace super

namespace clause

open tactic

meta def mk_or (a b : clause) (elim : expr → expr → tactic expr) : tactic clause := do
ae ← a.ty.to_expr,
be ← b.ty.to_expr,
ae_ip ← is_prop ae,
be_ip ← is_prop be,
if ae_ip ∧ be_ip then do
  prf ← elim `(@or.inl %%ae %%be %%a.prf) `(@or.inr %%ae %%be %%b.prf),
  pure ⟨clause_type.disj tt a.ty b.ty, prf⟩
else do
  prfa ← mk_mapp ``psum.inl [ae, be, a.prf],
  prfb ← mk_mapp ``psum.inr [ae, be, b.prf],
  prf ← elim prfa prfb,
  pure ⟨clause_type.disj ff a.ty b.ty, prf⟩

meta def or_congr (c : clause) (fa fb : clause → tactic clause) : tactic clause :=
match c with
| ⟨clause_type.disj io a b, prf⟩ := do
  ae ← a.to_expr, ha ← mk_local_def ae.hyp_name_hint ae,
  be ← b.to_expr, hb ← mk_local_def be.hyp_name_hint be,
  ⟨a', prfa'⟩ ← fa ⟨a, ha⟩,
  ⟨b', prfb'⟩ ← fb ⟨b, hb⟩,
  psumab ← mk_mapp ``psum [ae,be],
  match io, a', b' with
  | tt, clause_type.ff, _ := do
    let hb' := `(@or.elim %%ae %%be _ %%prf
      %%(expr.mk_lambda ha `(@false.elim.{0} %%be %%prfa'))
      id),
    pure ⟨b', (expr.mk_lambda hb prfb').app' hb'⟩
  | tt, _, clause_type.ff := do
    let ha' := `(@or.elim %%ae %%be _ %%prf
      id
      %%(expr.mk_lambda hb `(@false.elim.{0} %%ae %%prfb'))),
    pure ⟨a', (expr.mk_lambda ha prfa').app' ha'⟩
  | tt, _, _ := do
    ae' ← a'.to_expr,
    be' ← b'.to_expr,
    mk_or ⟨a',prfa'⟩ ⟨b',prfb'⟩ $ λ prfa'' prfb'', do
      motive ← infer_type prfa'',
      motive_ip ← is_prop motive,
      mk_mapp (if motive_ip then ``or.elim else ``or.elim') [ae, be, motive,
        expr.mk_lambda ha prfa'',
        expr.mk_lambda hb prfb'']
  | bool.ff, clause_type.ff, _ := do
    prfa' ← mk_mapp ``false.elim [be, prfa'],
    hb' ← mk_mapp ``psum.cases_on [ae, be,
      expr.lam `_ binder_info.default psumab be,
      prf,
      expr.mk_lambda ha prfa',
      expr.mk_lambda hb hb
    ],
    pure ⟨b', (expr.mk_lambda hb prfb').app' hb'⟩
  | ff, _, clause_type.ff := do
    tprf ← infer_type prf,
    prfb' ← mk_mapp ``false.elim [ae, prfb'],
    ha' ← mk_mapp ``psum.cases_on [ae, be,
      expr.lam `_ binder_info.default tprf ae,
      prf,
      expr.mk_lambda ha ha,
      expr.mk_lambda hb prfb'
    ],
    pure ⟨a', (expr.mk_lambda ha prfa').app' ha'⟩
  | ff, _, _ := do
    ae' ← a'.to_expr,
    be' ← b'.to_expr,
    mk_or ⟨a',prfa'⟩ ⟨b',prfb'⟩ $ λ prfa'' prfb'', do
      motive ← expr.lam `_ binder_info.default psumab <$> infer_type prfa'',
      mk_mapp ``psum.cases_on [ae, be, motive,
        expr.mk_lambda ha prfa'',
        expr.mk_lambda hb prfb'']
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
| c@⟨clause_type.disj _ a b, prf⟩ i h := do
  let an := a.num_literals,
  if i < an then
    or_congr c (λ ca, propg_pos ca i h) pure
  else
    or_congr c pure (λ cb, propg_pos cb (i - an) h)

meta def propg_neg : clause → ℕ → clause → ℕ → tactic clause
| ⟨clause_type.ff, _⟩ _ _ _ := fail "propg_neg ff"
| ⟨clause_type.atom _, _⟩ (i+1) _ _ := fail "propg_neg atom (i+1)"
| ⟨clause_type.atom _, prf⟩ 0 h j := propg_pos h j prf
| ⟨clause_type.imp _ _, _⟩ 0 _ _ := undefined_core "propg_neg imp 0"
| ⟨clause_type.imp a b, prf⟩ (i+1) h j := do
  ha ← mk_local_def a.hyp_name_hint a,
  ⟨b', prf'⟩ ← propg_neg ⟨b, prf.app' ha⟩ i h j,
  pure ⟨clause_type.imp a b', expr.mk_lambda ha prf'⟩
| c@⟨clause_type.disj _ a b, prf⟩ i h j := do
  let an := a.literals.length,
  if i < an then
    or_congr c (λ ca, propg_neg ca i h j) pure
  else
    or_congr c pure (λ cb, propg_neg cb (i - an) h j)

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
