import super.prover_state super.selection
  super.inferences.distinct super.inferences.resolution
  super.inferences.clausify super.inferences.empty_clause
  super.inferences.subsumption

namespace super
open native tactic

meta def default_preprocessing_rules : list preprocessing_rule :=
[ preprocessing.empty_clause,
  preprocessing.distinct,
  preprocessing.clausify,
  preprocessing.subsumption_interreduction,
  preprocessing.forward_subsumption ]

meta def default_simplification_rules : list simplification_rule :=
[ simplification.forward_subsumption ]

meta def default_inference_rules : list inference_rule :=
[ inference.resolution ]

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

meta def main_loop (opts : options) : ℕ → prover (option expr) | n := do
passive_size ← rb_map.size <$> get_passive,
if passive_size = 0 then
  do act ← get_active, tactic.trace act.values,
  pure none -- saturation
else do
  given_id ← opts.clause_selection n,
  given ← consume_passive given_id,
  given ← do_simplification opts given,
  match given with
  | some given := do
    add_active given,
    trace given,
    given' ← given.clone,
    newly_derived ← list.join <$> opts.inf_rules.mmap (λ ir, ir given'),
    newly_derived ← do_preprocessing opts newly_derived,
    let derived_empty_clauses := newly_derived.filter (λ c, c.ty.literals = []),
    match derived_empty_clauses with
    | (c::_) := pure c.prf
    | _ := do
      newly_derived.mmap' (add_passive opts.literal_selection),
      main_loop (n+1)
    end
  | none := main_loop (n+1)
  end

meta def main (opts : options) (initial : list clause) : tactic (option expr) := do
initial ← initial.mmap clause.clone, -- work around local context restriction
prod.fst <$> state_t.run (do
    initial ← do_preprocessing opts initial,
    initial.mmap' (add_passive opts.literal_selection),
    main_loop opts 0)
  prover_state.initial

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

meta def clauses_of_simp_arg_type : simp_arg_type → tactic (list clause)
| simp_arg_type.all_hyps := do lctx ← local_context, lctx.mmap clause.of_proof
| (simp_arg_type.except _) := fail "super [-foo] not supported"
| (simp_arg_type.expr e) := do
  -- TODO: eqn lemmas
  cls ← tactic.retrieve (to_expr e >>= clause.of_proof >>= clause.pack),
  cls ← cls.unpack,
  pure [cls]

meta def clauses_of_simp_arg_type_list (simp_args : list simp_arg_type) : tactic (list clause) :=
list.join <$> simp_args.mmap clauses_of_simp_arg_type

end super

namespace tactic.interactive
open lean.parser
open interactive
open interactive.types
open tactic

meta def super (args : parse simp_arg_list)
               (opts : super.options := {}) : tactic unit := do
cs ← _root_.super.clauses_of_simp_arg_type_list args,
_root_.super.solve_with_goal opts cs

end tactic.interactive

set_option profiler true
-- set_option trace.type_context.is_def_eq true
-- set_option trace.type_context.is_def_eq_detail true
lemma foo (p : ℕ → Prop) (h1 : ∀ x, ¬ p x) : ∃ x, ¬ p (x + 1) :=
let x : ℕ := 1 in
by super *

lemma bar (p : ℕ → Prop) : p 0 → (∀ x, p x → p (x + 1)) → p 10 :=
by super

#print foo
