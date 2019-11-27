import super.clause

namespace super

namespace clause

meta def propg_pos : clause → ℕ → expr → clause
| ⟨clause_type.ff, _⟩ _ _ := undefined_core "propg_pos ff"
| ⟨clause_type.atom _, _⟩ _ _ := undefined_core "propg_pos atom"
| ⟨clause_type.imp a b, prf⟩ 0 h := ⟨b, prf.app' h⟩
| ⟨clause_type.imp a b, prf⟩ (i+1) h :=
  let ⟨b', prf'⟩ := propg_pos ⟨b, prf.lift_vars 0 1 (expr.var 0)⟩ i h in
  ⟨clause_type.imp a b', expr.lam `h binder_info.default a prf'⟩
| ⟨clause_type.or a b, prf⟩ i h :=
  let an := a.literals.length in
  if i < (an : ℕ) then
    let ⟨a', prf'⟩ := propg_pos ⟨a, expr.var 0⟩ i h in
    ⟨clause_type.or a' b,
     `(@or_imp_congr_left %%b.to_expr %%a.to_expr %%a'.to_expr
        %%(expr.lam `h binder_info.default a.to_expr prf'))⟩
  else
    let ⟨b', prf'⟩ := propg_pos ⟨b, expr.var 0⟩ (i - an) h in
    ⟨clause_type.or a b',
     `(@or_imp_congr_right %%a.to_expr %%b.to_expr %%b'.to_expr
        %%(expr.lam `h binder_info.default b.to_expr prf'))⟩

meta def propg_neg : clause → ℕ → clause → clause
| ⟨clause_type.ff, _⟩ _ _ := undefined_core "propg_neg ff"
| ⟨clause_type.atom _, _⟩ (i+1) _ := undefined_core "propg_neg atom (i+1)"
| ⟨clause_type.atom _, prf⟩ 0 ⟨hty, hprf⟩ :=
  ⟨hty, hprf.instantiate_var prf⟩
| ⟨clause_type.imp _ _, _⟩ 0 _ := undefined_core "propg_neg imp 0"
| ⟨clause_type.imp a b, prf⟩ (i+1) h :=
  let ⟨b', prf'⟩ := propg_neg ⟨b, prf.lift_vars 0 1 (expr.var 0)⟩ i h in
  ⟨clause_type.imp a b', expr.lam `h binder_info.default a prf'⟩
| ⟨clause_type.or a b, prf⟩ i h :=
  let an := a.literals.length in
  if i < (an : ℕ) then
    let ⟨a', prf'⟩ := propg_neg ⟨a, expr.var 0⟩ i h in
    ⟨clause_type.or a' b,
     `(@or_imp_congr_left %%b.to_expr %%a.to_expr %%a'.to_expr
        %%(expr.lam `h binder_info.default a.to_expr prf'))⟩
  else
    let ⟨b', prf'⟩ := propg_neg ⟨b, expr.var 0⟩ (i - an) h in
    ⟨clause_type.or a b',
     `(@or_imp_congr_right %%a.to_expr %%b.to_expr %%b'.to_expr
        %%(expr.lam `h binder_info.default b.to_expr prf'))⟩

meta def resolve (a : clause) (ai : ℕ) (b : clause) (bi : ℕ) : clause :=
propg_neg a ai (propg_pos b bi (expr.var 0))

meta def mgu_resolve (a : clause) (ai : ℕ) (b : clause) (bi : ℕ) : tactic clause := do
some (literal.pos al) ← pure (a.literals.nth ai),
some (literal.neg bl) ← pure (b.literals.nth bi),
tactic.unify al bl,
pure $ propg_neg b bi (propg_pos a ai (expr.var 0))

end clause

end super
