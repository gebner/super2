
meta def format.form (as : list format) : format :=
(format.join (as.intersperse format.line)).paren.group

open native

meta def expr.meta_vars (e : expr) : rb_set expr :=
e.fold mk_rb_set $ λ e i ms,
match e with
| expr.mvar _ _ _ := ms.insert e
| _ := ms
end

private meta def level.meta_vars_core : level → name_set → name_set
| level.zero := id
| (level.param _) := id
| (level.succ l) := l.meta_vars_core
| (level.mvar n) := λ ms, ms.insert n
| (level.max a b) := a.meta_vars_core ∘ b.meta_vars_core
| (level.imax a b) := a.meta_vars_core ∘ b.meta_vars_core

meta def level.meta_vars (l : level) : name_set :=
level.meta_vars_core l mk_name_set

meta def expr.univ_meta_vars (e : expr) : name_set :=
e.fold mk_name_set $ λ e i ms,
match e with
| expr.sort l := level.meta_vars_core l ms
| expr.const _ ls := ls.foldr level.meta_vars_core ms
| _ := ms
end

def list.index_of_core' {α} [decidable_eq α] (a : α) : ℕ → list α → option ℕ
| i [] := none
| i (x::xs) := if x = a then some i else xs.index_of_core' (i+1)

def list.index_of' {α} [decidable_eq α] (a : α) (xs : list α) : option ℕ :=
xs.index_of_core' a 0

meta def expr.abstract_mvars (e : expr) (mvars : list name) : expr :=
e.replace $ λ e i,
match e with
| e@(expr.mvar n _ _) :=
  (mvars.index_of' n).map (λ j, expr.var (i + j))
| e := none
end

meta def expr.meta_uniq_name : expr → name
| (expr.mvar n _ _) := n
| _ := name.anonymous

meta def expr.meta_type : expr → expr
| (expr.mvar _ _ t) := t
| _ := default _

meta def expr.abstract_mvars' (e : expr) (mvars : list expr) : expr :=
e.abstract_mvars (mvars.map expr.meta_uniq_name)

open tactic

private meta def sorted_mvars_core : list expr → list expr → tactic (list expr)
| (e@(expr.mvar n pp_n _)::es) ctx :=
  if ∃ m ∈ ctx, (m : expr).meta_uniq_name = e.meta_uniq_name then
    sorted_mvars_core es ctx
  else do
    t ← infer_type e,
    ctx ← sorted_mvars_core t.meta_vars.to_list ctx,
    sorted_mvars_core es (expr.mvar n pp_n (t.abstract_mvars' ctx) :: ctx)
| [] ctx := pure ctx
| (e::es) ctx := sorted_mvars_core (e.meta_vars.to_list ++ es) ctx

meta def expr.sorted_mvars' (es : list expr) : tactic (list expr) :=
sorted_mvars_core es []

meta def expr.sorted_mvars (e : expr) : tactic (list expr) :=
expr.sorted_mvars' [e]

/-- Runs a tactic for a result, reverting the state after completion -/
meta def tactic.retrieve {α} (tac : tactic α) : tactic α :=
λ s, result.cases_on (tac s)
  (λ a s', result.success a s)
  result.exception

meta def level.instantiate_univ_mvars (subst : rb_map name level) : level → level
| level.zero := level.zero
| (level.succ a) := a.instantiate_univ_mvars.succ
| (level.max a b) := level.max (a.instantiate_univ_mvars) (b.instantiate_univ_mvars)
| (level.imax a b) := level.imax (a.instantiate_univ_mvars) (b.instantiate_univ_mvars)
| l@(level.param _) := l
| l@(level.mvar n) := (subst.find n).get_or_else l

meta def expr.instantiate_univ_mvars (subst : rb_map name level) (e : expr) : expr :=
e.replace $ λ e i,
match e with
| (expr.const n ls) :=
  some $ expr.const n (ls.map (level.instantiate_univ_mvars subst))
| (expr.sort l) :=
  some $ expr.sort (l.instantiate_univ_mvars subst)
| _ := none
end
