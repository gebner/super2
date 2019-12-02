import super.prover_state super.selection
  super.inferences.distinct super.inferences.resolution
  super.inferences.clausify super.inferences.empty_clause
  super.inferences.subsumption super.inferences.superposition
  super.inferences.factoring super.inferences.inhabited

namespace super
open native tactic

meta def default_preprocessing_rules : list preprocessing_rule :=
[ preprocessing.empty_clause,
  preprocessing.clausify,
  preprocessing.distinct,
  preprocessing.inhabited,
  preprocessing.pos_refl,
  preprocessing.neg_refl,
  preprocessing.flip_eq,
  preprocessing.distinct,
  preprocessing.subsumption_interreduction,
  -- preprocessing.forward_subsumption,
  preprocessing.empty_clause ]

meta def default_simplification_rules : list simplification_rule :=
[ simplification.forward_subsumption ]

meta def default_inference_rules : list inference_rule :=
[ inference.backward_subsumption,
  inference.resolution,
  inference.factoring,
  inference.forward_superposition,
  inference.backward_superposition,
  inference.unify_eq ]

meta structure options :=
(literal_selection : literal_selection_strategy := selection21)
(clause_selection : clause_selection_strategy := age_weight_clause_selection 3 4)
(simpl_rules : list simplification_rule := default_simplification_rules)
(inf_rules : list inference_rule := default_inference_rules)
(preproc_rules : list preprocessing_rule := default_preprocessing_rules)

meta def do_simplification (opts : options)
  (given : derived_clause) : prover (option derived_clause) := do
cls : option clause ← opts.simpl_rules.mfoldl (λ cls sr,
  match (cls : option clause) with
  | some cls := sr cls
  | none := pure none
  end) (some given.cls),
pure $ cls.map $ λ cls, { cls := cls, ..given }

meta def do_preprocessing (opts : options)
  (newly_derived : list clause) : prover (list clause) :=
opts.preproc_rules.mfoldl (λ cls pr, pr cls) newly_derived

declare_trace super

meta def main_loop (opts : options) : list clause → ℕ → prover (option expr) | newly_derived n := do
newly_derived ← do_preprocessing opts newly_derived,
let derived_empty_clauses := newly_derived.filter (λ c, c.ty.literals = []),
match derived_empty_clauses with
| (c::_) := do
  c ← c.instantiate_mvars,
  c.check,
  pure c.prf
| _ := do
newly_derived.mmap' (add_passive opts.literal_selection),
passive_size ← rb_map.size <$> get_passive,
if passive_size = 0 then
  do act ← get_active, tactic.trace act.values,
  pure none -- saturation
else do
  given_id ← opts.clause_selection n,
  given ← consume_passive given_id,
  given ← do_simplification opts given,
  match given with
  | none := main_loop [] (n+1)
  | some given := do
    when (is_trace_enabled_for `super)
      (do act ← get_active,
          given ← pp given,
          trace $ "[a=" ++ to_string act.size ++
                  ",p=" ++ to_string passive_size ++
                  "] " ++ to_string given),
    add_active given,
    given' ← given.clone,
    newly_derived ← list.join <$> opts.inf_rules.mmap (λ ir, ir given'),
    main_loop newly_derived (n+1)
  end
end

meta def main (opts : options) (initial : list clause) : tactic (option expr) := do
initial ← initial.mmap clause.clone, -- work around local context restriction
prod.fst <$> state_t.run (main_loop opts initial 0) prover_state.initial

meta def with_ground_mvars {α} (tac : tactic α) : tactic α := do
reverted_goal ← tactic.retrieve (unfreeze_local_instances >> revert_all >> target),
reverted_goal ← instantiate_mvars reverted_goal,
mvars ← reverted_goal.sorted_mvars,
lcs ← mk_locals_core mvars,
let univ_mvars := (reverted_goal.mk_app lcs).univ_meta_vars.to_list,
ups ← univ_mvars.mmap (λ _, mk_fresh_name),
(goal::goals) ← get_goals,
(res, proof) ← tactic.retrieve (do
  (mvars.zip lcs).mmap' (λ ⟨m, lc⟩, unify m lc),
  (univ_mvars.zip ups).mmap (λ ⟨m, up⟩, unify_level (level.mvar m) (level.param up)),
  set_goals [goal],
  instantiate_mvars_in_target,
  res ← tac,
  done,
  proof ← instantiate_mvars goal,
  pure (res, proof)),
let proof := (proof.abstract_locals (lcs.map expr.local_uniq_name)).instantiate_vars mvars,
let proof := proof.instantiate_univ_params
  ((ups.zip univ_mvars).map (λ ⟨up, m⟩, (up, level.mvar m))),
exact proof,
pure res

meta def solve (opts : options) (initial : list clause) : tactic unit := do
some empty_clause ← main opts initial | fail "saturation",
(target >>= is_def_eq `(false)) <|> exfalso,
exact empty_clause

meta def intros' : tactic (list expr) :=
(do x ← intro_core `_, xs ← intros', pure (x::xs)) <|> pure []

meta def solve_with_goal (opts : options) (initial : list clause) : tactic unit := do
classical,
hs ← intros',
tgt ← target,
hs ← if tgt = `(false) then pure hs else
  (::) <$> by_contradiction <*> pure hs,
initial ← (++ initial) <$> hs.mmap clause.of_proof,
some empty_clause ← main opts initial | fail "saturation",
exact empty_clause

meta def eqn_lemma_clauses (n : name) : tactic (list clause) := do
ls ← get_eqn_lemmas_for tt n,
ls.mmap $ λ l, tactic.retrieve (mk_const l >>= clause.of_proof >>= clause.pack)
                 >>= packed_clause.unpack

meta def eqn_lemma_clauses_of_pexpr_name (n : name) : tactic (list clause) := do
p ← resolve_name n,
let e := p.erase_annotations.get_app_fn.erase_annotations,
match e with
| expr.const n _ := do
ls ← get_eqn_lemmas_for tt n,
ls.mmap $ λ l, tactic.retrieve (mk_const l >>= clause.of_proof >>= clause.pack)
                 >>= packed_clause.unpack
| _ := pure []
end

meta def eqn_lemma_clauses_of_pexpr : pexpr → tactic (list clause)
| (expr.const n _) := eqn_lemma_clauses_of_pexpr_name n
| (expr.local_const n _ _ _) := eqn_lemma_clauses_of_pexpr_name n
| _ := pure []

meta def clauses_of_simp_arg_type : simp_arg_type → tactic (list clause)
| simp_arg_type.all_hyps := do lctx ← local_context, lctx.mmap clause.of_proof
| (simp_arg_type.except _) := fail "super [-foo] not supported"
| (simp_arg_type.expr e) := do
  eqn_lems ← eqn_lemma_clauses_of_pexpr e,
  cls ← tactic.retrieve (to_expr e >>= clause.of_proof >>= clause.pack) >>= packed_clause.unpack,
  pure (cls :: eqn_lems)

meta def clauses_of_simp_arg_type_list (simp_args : list simp_arg_type) : tactic (list clause) :=
list.join <$> simp_args.mmap clauses_of_simp_arg_type

end super

namespace tactic.interactive
open lean.parser
open interactive
open interactive.types
open tactic

-- TODO: show unused arguments
meta def super (args : parse simp_arg_list)
               (opts : super.options := {}) : tactic unit :=
_root_.super.with_ground_mvars $ do
cs ← _root_.super.clauses_of_simp_arg_type_list args,
_root_.super.solve_with_goal opts cs

end tactic.interactive
