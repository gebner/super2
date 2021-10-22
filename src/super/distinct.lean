import super.resolve data.list.alist

namespace super

namespace clause_type

meta def has_dups (t : clause_type) : bool :=
t.literals.has_dups

meta def is_or_ff_clean : clause_type → bool
| ff := tt
| (disj _ ff _) := bool.ff
| (disj _ _ ff) := bool.ff
| (disj _ a b) := a.is_or_ff_clean ∧ b.is_or_ff_clean
| (imp _ a) := a.is_or_ff_clean
| (atom _) := tt

end clause_type

namespace clause

meta def is_or_ff_clean (c : clause) : bool :=
c.ty.is_or_ff_clean

meta def has_dups (c : clause) : bool :=
c.ty.has_dups

open tactic

/-
meta def mk_elim_cases (e : expr) (c_true c_false : expr) : tactic expr := do
(expr.pi _ _ _ motive) ← infer_type c_true | fail "mk_elim_cases",
when motive.has_var (fail "mk_elim_cases: dependent elim"),
ip ← band <$> is_prop e <*> is_prop motive,
if ip then do
  mk_mapp ``classical.by_cases [e, motive, c_true, c_false]
else do
  s ← mk_mapp ``classical.type_decidable [e],
  st ← infer_type s,
  mk_mapp ``psum.rec [none, none, some (expr.lam `_ binder_info.default st motive), c_true, c_false, s]
-/

private meta def distinct_core : clause → alist (λ _ : literal, expr) → tactic clause
| c@⟨clause_type.ff, _⟩ _ := pure c
| ⟨clause_type.imp a b, prf⟩ ctx :=
  match ctx.lookup (literal.neg a) with
  | some h := distinct_core ⟨b, prf.app' h⟩ ctx
  | none := do
    h ← mk_local_def a.hyp_name_hint a,
    let ctx := ctx.insert (literal.neg a) h,
    ⟨b', prfb'⟩ ← distinct_core ⟨b, prf.app' h⟩ ctx,
    pure ⟨clause_type.imp a b', expr.mk_lambda h prfb'⟩
  end
| c@⟨clause_type.atom a, prf⟩ ctx :=
  match ctx.lookup (literal.pos a) with
  | some h := pure ⟨clause_type.ff, h.app' prf⟩
  | none := pure c
  end
| c@⟨clause_type.disj _ a b, prf⟩ ctx := do
  let dups := (a.literals ∩ b.literals) \ ctx.keys,
  match dups with
  | (literal.pos l :: _) := do
    l_ip ← is_prop l,
    clnl : clause ← (if l_ip then do
        prf ← mk_mapp ``or_not [l],
        pure (⟨clause_type.disj tt (clause_type.atom l)
          (clause_type.imp l clause_type.ff), prf⟩ : clause)
      else do
        prf ← mk_mapp ``classical.type_decidable [l],
        pure (⟨clause_type.disj ff (clause_type.atom l)
          (clause_type.imp l clause_type.ff), prf⟩ : clause)),
    clnl.check_if_debug,
    or_congr clnl
      (λ cl, pure cl)
      (λ cnl, distinct_core c (ctx.insert (literal.pos l) cnl.prf))
  | (literal.neg l :: _) := do
    hl ← mk_local_def l.hyp_name_hint l,
    ⟨ab', prf'⟩ ← distinct_core c (ctx.insert (literal.neg l) hl),
    pure ⟨clause_type.imp l ab', expr.mk_lambda hl prf'⟩
  | [] :=
    or_congr c (λ ca, distinct_core ca ctx) (λ cb, distinct_core cb ctx)
  end

meta def distinct (c : clause) : tactic clause :=
if c.is_or_ff_clean ∧ ¬ c.has_dups then pure c else
clause.check_result_if_debug $
distinct_core c ∅

end clause

end super
