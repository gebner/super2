import super.inferences.superposition

namespace super
open tactic

variables (gt : term_order)

meta def get_simpl_clauses : prover (list (expr × expr × clause)) := do
act ← get_active,
pure $ do act ← act.values,
          clause_type.atom `(%%r = %%l) ← pure act.cls.ty | [],
          pure (l,r,act.cls)

variables (simpl_clauses : list (expr × expr × clause))

meta def simplify1 : expr → tactic (expr × expr) | e :=
first $ do st ← closed_subterms e, (l, r, cls) ← simpl_clauses,
           pure $ tactic.retrieve $ do
unify st l transparency.reducible,
(do l_ty ← infer_type l, st_ty ← infer_type st, unify l_ty st_ty),
l ← instantiate_mvars l,
r ← instantiate_mvars r,
guard $ gt l r,
ty ← infer_type st,
ctx ← kabstract e l transparency.reducible ff,
prf ← mk_mapp ``congr_arg [none, none, r, l,
  expr.lam ty.hyp_name_hint binder_info.default ty ctx, cls.prf],
prf ← instantiate_mvars prf,
guard $ ¬ prf.has_meta_var,
pure (ctx.instantiate_var r, prf)

meta def simplify : expr → tactic (option $ expr × expr) | e := do
res ← try_core (simplify1 gt simpl_clauses e),
match res with
| none := pure none
| some (e', prf) := do
  res ← simplify e',
  match res with
  | none := pure (e', prf)
  | some (e'', prf') := do
    prf'' ← mk_mapp ``eq.trans [none, e'', e', e, prf', prf],
    pure (e'', prf'')
  end
end

meta def simplify_clause (cls : clause) : tactic (option clause) := do
⟨did_simpl, simpld⟩ ← (cls.literals.zip_with_index.mfoldr
  (λ ⟨l, i⟩ ⟨did_simpl, cls⟩, do
    res ← simplify gt simpl_clauses l.formula,
    match res with
    | none := pure (did_simpl, cls)
    | some (f', prf) := do
      if l.is_pos then do
        prf ← mk_mapp ``eq.mpr [f', l.formula, prf],
        pure (tt, clause.resolve cls i
          ⟨clause_type.imp l.formula (clause_type.atom f'), prf⟩ 0)
      else do
        prf ← mk_mapp ``eq.mp [f', l.formula, prf],
        pure (tt, clause.resolve
          ⟨clause_type.imp f' (clause_type.atom l.formula), prf⟩ 1
          cls i)
    end)
  (ff, cls) : tactic (bool × clause)),
if did_simpl then pure simpld else pure none

meta def simplify_with_ground (cls : clause) (tac : clause → tactic (option clause)) :
  tactic (option clause) := tactic.retrieve $ do
mvars ← cls.prf.sorted_mvars,
lcs ← abstract_mvar_telescope mvars >>= λ ms, mk_locals_core ms,
(mvars.zip lcs).mmap' $ λ ⟨m, lc⟩, unify m lc,
let umvars := cls.prf.univ_meta_vars.to_list,
ups ← umvars.mmap (λ _, mk_fresh_name),
(umvars.zip ups).mmap' $ λ ⟨m, p⟩, unify_level (level.mvar m) (level.param p),
cls ← cls.instantiate_mvars,
some simpld ← tac cls | pure none,
simpld ← simpld.instantiate_mvars,
when simpld.prf.has_meta_var $ fail "simplify_with_ground has_meta_var",
let simpld := simpld.abstract_locals (lcs.map expr.local_uniq_name),
let simpld := simpld.instantiate_univ_params (ups.zip (umvars.map level.mvar)),
pure simpld

meta def simplification.forward_demod : simplification_rule | cls := do
gt ← get_term_order,
simpl_clauses@(_::_) ← get_simpl_clauses | pure cls,
simpld ← simplify_with_ground cls $ simplify_clause gt simpl_clauses,
pure $ simpld.get_or_else cls

end super
