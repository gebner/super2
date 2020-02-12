import super.utils super.clause

open tactic expr

namespace super

meta def get_eqn_lemma_clauses (n : name) : tactic (list clause) := do
els ← get_eqn_lemmas_for tt n,
els.mmap clause.of_const

meta def mk_inst_equations_core : expr → expr → tactic (list expr) | lhs rhs := do
type ← infer_type lhs,
(type_args, tgt) ← mk_local_pis_whnf type,
tgt ← whnf tgt,
let str := tgt.get_app_fn.const_name,
is_cls ← has_attribute' `class str,
e ← get_env,
if is_cls ∧ e.is_structure str then do
  if type_args ≠ [] then do
    let lhs := lhs.mk_app type_args,
    let rhs := rhs.instantiate_lambdas_or_apps type_args,
    eqns ← mk_inst_equations_core lhs rhs,
    pure $ eqns.map (mk_lambdas type_args)
  else do
    lhs ← whnf lhs transparency.reducible,
    projs ← e.structure_fields_full str,
    [intro] ← return $ e.constructors_of str | fail "unreachable code (3)",
    let params := get_app_args tgt, -- the parameters of the structure
    rhs ← whnf rhs,
    if is_constant_of rhs.get_app_fn intro then do -- if the value is a constructor application
      let rhs_args := rhs.get_app_args.drop params.length, -- the fields of the structure
      guard (rhs_args.length = projs.length) <|> fail "unreachable code (2)",
      list.join <$> (projs.zip rhs_args).mmap (λ ⟨proj, new_rhs⟩, do
        new_type ← infer_type new_rhs,
        b ← is_prop new_type,
        if b then
          -- Prop field
          pure []
        else do
          new_lhs ← mk_mapp proj ((params ++ [lhs]).map some),
          mk_inst_equations_core new_lhs new_rhs)
    else do
      -- class subfield that doesn't reduce to a constructor
      pure []
else do
  -- non-class field
  e ← mk_mapp ``eq [none, lhs, rhs],
  prfl ← mk_eq_refl lhs,
  pure <$> (expr.app <$> mk_mapp ``id_rhs [e] <*> pure prfl)

meta def mk_inst_equations (n : name) : tactic (list expr) := do
lhs ← mk_const n,
rhs ← whnf lhs,
mk_inst_equations_core lhs rhs

meta def mk_inst_eqn_clauses (n : name) : tactic (list clause) := do
prfs ← mk_inst_equations n,
prfs.mmap $ λ prf, clause.of_proof prf >>= clause.clone

meta def get_aux_lemma_clauses (n : name) : tactic (list clause) := do
is_inst ← has_attribute' `instance n,
if is_inst then
  mk_inst_eqn_clauses n
else
  get_eqn_lemma_clauses n

end super
