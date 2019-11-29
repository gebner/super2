import super.resolve

namespace super

namespace clause_type

meta def has_dups (t : clause_type) : bool :=
t.literals.has_dups

meta def is_or_ff_clean : clause_type → bool
| ff := tt
| (or ff _) := bool.ff
| (or _ ff) := bool.ff
| (or a b) := a.is_or_ff_clean ∧ b.is_or_ff_clean
| (imp _ a) := a.is_or_ff_clean
| (atom _) := tt

end clause_type

namespace clause

meta def is_or_ff_clean (c : clause) : bool :=
c.ty.is_or_ff_clean

meta def has_dups (c : clause) : bool :=
c.ty.has_dups

private meta def distinct_core : clause → list literal → clause
| c@⟨clause_type.ff, _⟩ _ := c
| c@⟨clause_type.imp a b, prf⟩ ctx :=
  match ctx.index_of' (literal.neg a) with
  | some i := distinct_core ⟨b, prf (expr.var i)⟩ ctx
  | none :=
    let ⟨b', prf'⟩ :=
      distinct_core ⟨b, (prf.lift_vars 0 1).app' (expr.var 0)⟩ (literal.neg a :: ctx) in
    ⟨clause_type.imp a b', expr.lam a.hyp_name_hint binder_info.default a prf'⟩
  end
| c@⟨clause_type.atom a, prf⟩ ctx :=
  match ctx.index_of' (literal.pos a) with
  | some i := ⟨clause_type.ff, (expr.var i).app prf⟩
  | none := c
  end
| ⟨clause_type.or clause_type.ff b, prf⟩ ctx :=
  distinct_core ⟨b, `((@false_or %%b.to_expr).mp %%prf)⟩ ctx
| ⟨clause_type.or a clause_type.ff, prf⟩ ctx :=
  distinct_core ⟨a, `((@or_false %%a.to_expr).mp %%prf)⟩ ctx
| c@⟨clause_type.or a b, prf⟩ ctx :=
  if (a.literals ∩ b.literals) = [] then
    let ⟨a', prfa'⟩ := distinct_core ⟨a, expr.var 0⟩ (literal.neg a.to_expr :: ctx) in
    let ⟨b', prfb'⟩ := distinct_core ⟨b, expr.var 0⟩ (literal.neg b.to_expr :: ctx) in
    let res : clause := ⟨clause_type.or a' b',
    `(@or_imp_congr %%a.to_expr %%a'.to_expr %%b.to_expr %%b'.to_expr
      %%(expr.lam a.to_expr.hyp_name_hint binder_info.default a.to_expr prfa')
      %%(expr.lam b.to_expr.hyp_name_hint binder_info.default b.to_expr prfb')
      %%prf)⟩ in
    if res.is_or_ff_clean then res else distinct_core res ctx
  else
    match a with
    | clause_type.or a1 a2 :=
      distinct_core ⟨clause_type.or a1 (clause_type.or a2 b),
        `((@or.assoc %%a1.to_expr %%a2.to_expr %%b.to_expr).mp %%prf)⟩ ctx
    | clause_type.atom a :=
      let ⟨b', prf'⟩ := distinct_core ⟨b, expr.var 0⟩
        (literal.neg b.to_expr :: literal.pos a :: ctx) in
      let res : clause := ⟨clause_type.or (clause_type.atom a) b',
        `(@or_imp_congr_right_strong %%a %%b.to_expr %%b'.to_expr
          %%(expr.lam a.hyp_name_hint binder_info.default `(¬ %%a) $
            expr.lam b.to_expr.hyp_name_hint binder_info.default b.to_expr prf')
          %%prf)⟩ in
      if res.is_or_ff_clean then res else distinct_core res ctx
    | clause_type.ff := undefined_core "distinct_core ff"
    | clause_type.imp a1 clause_type.ff :=
      distinct_core ⟨clause_type.imp a1 b, `((@imp_iff_or_not %%a1 %%b.to_expr).mpr)⟩ ctx
    | clause_type.imp a1 a2 :=
      distinct_core ⟨clause_type.or (clause_type.or (clause_type.imp a1 clause_type.ff) a2) b,
        `(@or_imp_congr_left %%b.to_expr %%a.to_expr (¬ %%a1 ∨ %%a2.to_expr)
          %%(`(iff.mp $ @imp_iff_or_not %%a1 %%a2.to_expr)) %%prf)⟩ ctx
    end

meta def distinct (c : clause) : clause :=
if ¬ c.is_or_ff_clean ∨ c.has_dups then distinct_core c [] else c

end clause

end super
