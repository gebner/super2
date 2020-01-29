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
guard $ ctx.has_var,
let ctx := expr.lam ty.hyp_name_hint binder_info.default ty ctx,
type_check ctx,
prf ← mk_mapp ``congr_arg [none, none, r, l, ctx, cls.prf],
prf ← instantiate_mvars prf,
guard $ ¬ prf.has_meta_var,
pure (ctx.app' r, prf)

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
⟨did_simpl, simpld⟩ ← (cls.literals.mfoldr
  (λ l ⟨did_simpl, cls⟩, do
    some i ← pure $ cls.literals.index_of' l,
    res ← simplify gt simpl_clauses l.formula,
    match res with
    | none := pure (did_simpl, cls)
    | some (f', prf) :=
      if l.is_pos then do
        prf ← mk_mapp ``eq.mpr [f', l.formula, prf],
        let prf : clause := ⟨clause_type.imp l.formula (clause_type.atom f'), prf⟩,
        prod.mk tt <$> clause.resolve cls i prf 0
      else do
        prf ← mk_mapp ``eq.mp [f', l.formula, prf],
        let prf : clause := ⟨clause_type.imp f' (clause_type.atom l.formula), prf⟩,
        prod.mk tt <$> clause.resolve prf 1 cls i
    end)
  (ff, cls) : tactic (bool × clause)),
if did_simpl then pure simpld else pure none

meta def simplify_with_ground_core (cls : clause) (tac : clause → tactic (option clause)) :
  tactic (option (list expr × packed_clause)) := tactic.retrieve $ do
mvars ← cls.prf.sorted_mvars,
free_var_tys ← abstract_mvar_telescope mvars,
lcs ← mk_locals_core free_var_tys,
(mvars.zip lcs).mmap' $ λ ⟨m, lc⟩, unify m lc,
let umvars := cls.prf.univ_meta_vars.to_list,
ups ← umvars.mmap (λ _, mk_fresh_name),
cls ← cls.instantiate_mvars,
let cls := cls.instantiate_univ_mvars (native.rb_map.of_list (umvars.zip (ups.map level.param))),
some simpld ← tac cls | pure none,
simpld ← simpld.instantiate_mvars,
simpld.check_if_debug,
when simpld.prf.has_meta_var $ fail "simplify_with_ground_core has_meta_var",
let simpld := simpld.abstract_locals (lcs.map expr.local_uniq_name).reverse,
let simpld := simpld.instantiate_univ_params (ups.zip (umvars.map level.mvar)),
pure $ some ⟨mvars, umvars, free_var_tys, simpld⟩

meta def simplify_with_ground (cls : clause) (tac : clause → tactic (option clause)) :
  tactic (option clause) :=
option.map (λ s : list expr × packed_clause, s.2.cls.instantiate_vars s.1) <$>
  simplify_with_ground_core cls tac

meta def simplification.forward_demod : simplification_rule | cls := do
gt ← get_term_order,
simpl_clauses@(_::_) ← get_simpl_clauses | pure cls,
simpld ← simplify_with_ground cls $ simplify_clause gt simpl_clauses,
simpld.to_list.mmap' (monad_lift ∘ clause.check_if_debug),
pure $ simpld.get_or_else cls

meta def simplify_with_ground_packed (cls : clause) (tac : clause → tactic (option clause)) :
  tactic (option packed_clause) :=
option.map prod.snd <$> simplify_with_ground_core cls tac

meta def inference.backward_demod : inference_rule | given := do
clause_type.atom `(@eq %%ty %%r %%l) ← pure given.cls.ty | pure [],
let simpl_clauses := [(l,r,given.cls)],
let funsym := name_of_funsym r.get_app_fn,
if funsym = name.anonymous then pure [] else do
gt ← get_term_order,
active ← get_active,
list.join <$> (active.values.mmap $ λ act,
  if act.id = given.id then pure [] else do
  act_ty ← act.cls.ty.to_expr,
  if (contained_funsyms act_ty).contains funsym then do
    simpld ← simplify_with_ground_packed act.cls $
      simplify_clause gt simpl_clauses,
    match simpld with
    | some simpld := do
      remove_redundant act.id,
      clause.check_results_if_debug $
        pure <$> simpld.unpack
    | none := pure []
    end
  else
    pure [])

end super
