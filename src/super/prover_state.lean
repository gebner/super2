import super.clause super.lpo

namespace super
open tactic native

@[reducible]
def clause_id := ℕ

@[derive decidable_eq]
meta structure derived_clause :=
(id : clause_id)
(cls : clause)
(selected : list ℕ)

namespace derived_clause

meta instance : has_to_tactic_format derived_clause :=
⟨λ c, do c_fmt ← pp c.cls,
  pure $ to_fmt c.id ++ ": " ++ c_fmt ++ " (sel: " ++ to_fmt c.selected ++ ")"⟩

meta instance : has_to_string derived_clause :=
⟨λ c, to_string c.id ++ ": " ++ to_string c.cls ++ " (sel: " ++ to_string c.selected ++ ")"⟩

meta instance : has_repr derived_clause := ⟨to_string⟩

meta def clone (dc : derived_clause) : tactic derived_clause := do
cls' ← dc.cls.clone,
pure { cls := cls', ..dc }

meta def selected_lits (dc : derived_clause) : list (literal × ℕ) := do
let lits := dc.cls.literals,
i ← dc.selected,
some l ← pure (lits.nth i) | [],
pure (l, i)

end derived_clause

meta structure prover_state :=
(active : rb_map clause_id derived_clause)
(passive : rb_map clause_id derived_clause)
(prec : list name)
(clause_counter : ℕ)
(steps : list (expr × expr))

meta def prover_state.initial : prover_state :=
{ active := mk_rb_map,
  passive := mk_rb_map,
  prec := [],
  clause_counter := 0,
  steps := [] }

meta def prover := state_t prover_state tactic

namespace prover
local attribute [reducible] prover

meta instance : monad prover := infer_instance
meta instance : alternative prover := infer_instance
meta instance : monad_state _ prover := infer_instance
meta instance : has_monad_lift tactic prover := infer_instance
meta instance (α : Type) : has_coe (tactic α) (prover α) :=
⟨monad_lift⟩

end prover

meta def literal_selection_strategy := derived_clause → prover derived_clause

meta def clause_selection_strategy := ℕ → prover clause_id

meta def get_active : prover (rb_map clause_id derived_clause) :=
prover_state.active <$> get

meta def add_active (a : derived_clause) : prover punit :=
modify $ λ st, { active := st.active.insert a.id a, ..st }

meta def get_passive : prover (rb_map clause_id derived_clause) :=
prover_state.passive <$> get

meta def consume_passive (id : clause_id) : prover derived_clause := do
st ← get,
put { passive := st.passive.erase id, ..st },
some cls ← pure (st.passive.find id) | fail "consume_passive: unknown id",
pure cls

meta def get_precedence : prover (list name) :=
prover_state.prec <$> get

meta def term_order := expr → expr → bool

meta def get_term_order : prover term_order :=
mk_lpo <$> get_precedence

private meta def set_precedence (new_prec : list name) : prover punit :=
modify $ λ st, { prec := new_prec, ..st }

-- TODO: rethink this
meta def register_consts_in_precedence (consts : list name) : prover unit := do
p ← get_precedence,
let p_set := rb_map.set_of_list p,
let new_syms := consts.filter (λ c, ¬ p_set.contains c),
set_precedence (new_syms ++ p)

meta def get_clause_count : prover ℕ :=
prover_state.clause_counter <$> get

meta def get_new_cls_id : prover clause_id := do
state ← get,
put { state with clause_counter := state.clause_counter + 1 },
return state.clause_counter

meta def add_passive (strat : literal_selection_strategy) (c : clause) : prover clause_id := do
c.check_if_debug,
id ← get_new_cls_id,
c_ty ← c.ty.to_expr,
register_consts_in_precedence (contained_funsyms c_ty).to_list, -- TODO: rethink this
dc ← strat { id := id, cls := c, selected := [] },
modify $ λ st, { passive := st.passive.insert id dc, ..st },
pure id

meta def remove_redundant (id : clause_id) : prover unit :=
modify $ λ st, { active := st.active.erase id, ..st }

meta def preprocessing_rule := list clause → prover (list clause)

meta def simplification_rule := clause → prover (option clause)

@[inline]
meta def simplification_rule.as_preprocessing_rule (r : simplification_rule) : preprocessing_rule :=
λ cs, list.join <$> cs.mmap (λ c, clause.check_results_if_debug $ option.to_list <$> r c)

meta def inference_rule := derived_clause → prover (list clause)

meta def retrieve {α} (p : prover α) : prover α :=
do s ← get, ↑(tactic.retrieve $ prod.fst <$> p.run s)

meta def retrieve_packed (ps : list (prover (list clause))) : prover (list clause) :=
(list.join <$> monad.sequence (do p ← ps, pure $ retrieve $ p >>= list.mmap (λ c, c.pack)))
  >>= list.mmap (λ c : packed_clause, clause.check_result_if_debug c.unpack)

private meta def unfold_head1 : expr → tactic expr
| (expr.const n ls) := do
  d ← get_decl n,
  some v ← pure $ d.instantiate_value_univ_params ls
    | fail "instantiate_value_univ_params",
  pure v
| (expr.app a b) := expr.app' <$> unfold_head1 a <*> pure b
| e := pure e

meta def intern (c : clause) : prover clause := do
i ← (λ st : prover_state, st.steps.length) <$> get,
new_prf ← c.mk_decl i,
let step := new_prf.get_app_fn,
step_repl ← unfold_head1 step,
modify $ λ st, { steps := st.steps ++ [(step, step_repl)], ..st },
pure { prf := new_prf, ..c }

meta def intern_sk_term (e : expr) : prover expr := do
i ← (λ st : prover_state, st.steps.length) <$> get,
ty ← infer_type e,
e' ← add_aux_decl ((`_super.sk).mk_numeral (unsigned.of_nat i)) ty e ff,
let step := e'.get_app_fn,
step_repl ← unfold_head1 step,
modify $ λ st, { steps := st.steps ++ [(step, step_repl)], ..st },
pure e'

meta def intern_derived (c : derived_clause) : prover derived_clause := do
cls ← intern c.cls,
pure { cls := cls, ..c }

private meta def abstract_super_steps : expr → state_t (rb_map expr expr) tactic expr
| fn@(expr.const (name.mk_numeral i (name.mk_string cat `_super)) _) := do
  lc ← flip rb_map.find fn <$> get,
  match lc with
  | some lc := pure lc
  | none := do
    ty ← state_t.lift $ infer_type fn,
    lc ← state_t.lift $
      mk_local' (cat ++ "_" ++ to_string i : string)
        binder_info.default ty,
    state_t.modify $ λ st, st.insert fn lc,
    pure lc
  end
| (expr.lam n bi a b) := expr.lam n bi <$> abstract_super_steps a <*> abstract_super_steps b
| (expr.pi n bi a b) := expr.pi n bi <$> abstract_super_steps a <*> abstract_super_steps b
| (expr.elet n a b c) := expr.elet n <$> abstract_super_steps a
  <*> abstract_super_steps b <*> abstract_super_steps c
| (expr.sort u) := pure $ expr.sort u
| e@(expr.const _ _) := pure e
| e@(expr.var _) := pure e
| e@(expr.local_const _ _ _ _) := pure e
| e@(expr.mvar _ _ _) := pure e
| (expr.macro md es) := expr.macro md <$> es.mmap abstract_super_steps
| (expr.app a b) := expr.app <$> abstract_super_steps a <*> abstract_super_steps b

private meta def unfold_defs_core : list (expr × expr) → expr → state_t (rb_map expr expr) tactic expr
| (⟨fn, repl⟩ :: steps) e := do
  e ← unfold_defs_core steps e,
  lcs ← rb_map.to_list <$> get,
  lcs.mfoldr (λ ⟨fn', lc⟩ e, do
      some repl' ← state_t.lift $ tactic.retrieve $ try_core $
            unify fn fn' >> instantiate_mvars repl
        | pure e,
      state_t.modify $ λ st, st.erase fn',
      repl' ← abstract_super_steps repl',
      ty' ← state_t.lift $ infer_type repl',
      pure $ expr.elet lc.local_pp_name ty' repl'
        (e.abstract_local lc.local_uniq_name))
    e
| [] e := abstract_super_steps e

meta def unfold_defs (e : expr) : prover expr := do
steps ← prover_state.steps <$> get,
(e', lcs) ← (unfold_defs_core steps e).run mk_rb_map,
0 ← pure lcs.size | fail "unfold_defs did not unfold all defs",
pure e'

end super
