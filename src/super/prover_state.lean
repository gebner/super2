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

end derived_clause

meta structure prover_state :=
(active : rb_map clause_id derived_clause)
(passive : rb_map clause_id derived_clause)
(prec : list name)
(clause_counter : ℕ)

meta def prover_state.initial : prover_state :=
{ active := mk_rb_map,
  passive := mk_rb_map,
  prec := [],
  clause_counter := 0 }

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
c.check,
id ← get_new_cls_id,
register_consts_in_precedence (contained_funsyms c.ty.to_expr).to_list, -- TODO: rethink this
dc ← strat { id := id, cls := c, selected := [] },
modify $ λ st, { passive := st.passive.insert id dc, ..st },
pure id

meta def preprocessing_rule := list clause → prover (list clause)

meta def simplification_rule := clause → prover (option clause)

meta def simplification_rule.as_preprocessing_rule (r : simplification_rule) : preprocessing_rule :=
λ cs, list.join <$> cs.mmap (λ c, option.to_list <$> r c)

meta def inference_rule := derived_clause → prover (list clause)

meta def retrieve {α} (p : prover α) : prover α :=
do s ← get, ↑(tactic.retrieve $ prod.fst <$> p.run s)

meta def retrieve_packed (ps : list (prover (list clause))) : prover (list clause) :=
(list.join <$> monad.sequence (do p ← ps, pure $ retrieve $ p >>= list.mmap (λ c, c.pack)))
>>= list.mmap (λ c : packed_clause, c.unpack)

end super