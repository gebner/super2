import tactic.core

attribute [inline] or.decidable decidable.to_bool bool.decidable_eq and.decidable
  nat.decidable_eq ne.decidable decidable.false implies.decidable option.get_or_else
  option.map

meta def format.form (as : list format) : format :=
(format.join (as.intersperse format.line)).paren.group

open native

meta def expr.meta_vars (e : expr) : rb_set expr :=
e.fold mk_rb_set $ λ e i ms,
match e with
| expr.mvar _ _ _ := ms.insert e
| _ := ms
end

meta def list.dup_by_native {α β} [has_lt β] [decidable_rel ((<) : β → β → Prop)]
  (f : α → β) (xs : list α) : list α :=
rb_map.values $ xs.foldl (λ m x, m.insert (f x) x) mk_rb_map

meta def level.mvar_name : level → name
| (level.mvar n) := n
| _ := name.anonymous

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
    t ← infer_type e >>= instantiate_mvars,
    ctx ← sorted_mvars_core t.meta_vars.to_list ctx,
    sorted_mvars_core es (e :: ctx)
| [] ctx := pure ctx
| (e::es) ctx := sorted_mvars_core (e.meta_vars.to_list ++ es) ctx

meta def expr.sorted_mvars' (es : list expr) : tactic (list expr) :=
sorted_mvars_core es []

meta def expr.sorted_mvars (e : expr) : tactic (list expr) :=
expr.sorted_mvars' [e]

meta def abstract_mvar_telescope : list expr → tactic (list expr)
| [] := pure []
| (m :: ms) := do
  t ← infer_type m >>= instantiate_mvars,
  ms' ← abstract_mvar_telescope ms,
  pure $ t.abstract_mvars' ms :: ms'

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

meta def expr.mk_lambda (x e : expr) : expr :=
expr.lam x.local_pp_name x.local_binding_info x.local_type (e.abstract x)

meta def expr.mk_lambdas (xs : list expr) (e : expr) : expr :=
xs.foldr expr.mk_lambda e

meta def expr.mk_pi (x e : expr) : expr :=
expr.pi x.local_pp_name x.local_binding_info x.local_type (e.abstract x)

meta def expr.mk_pis (xs : list expr) (e : expr) : expr :=
xs.foldr expr.mk_pi e

meta def expr.app' : expr → expr → expr
| (expr.lam _ _ _ a) b := a.instantiate_var b
| a b := a b

lemma or_imp_congr {p p' q q'} (hp : p → p') (hq : q → q') : p ∨ q → p' ∨ q'
| (or.inl h) := or.inl (hp h)
| (or.inr h) := or.inr (hq h)

lemma or_imp_congr_left {p q r} (h : q → r) : q ∨ p → r ∨ p :=
or_imp_congr h id

lemma or_imp_congr_right {p q r} (h : q → r) : p ∨ q → p ∨ r :=
or_imp_congr id h

lemma or_imp_congr_right_strong {p q r} (h : ¬ p → q → r) : p ∨ q → p ∨ r :=
match classical.prop_decidable p with
| decidable.is_true hp := λ _, or.inl hp
| decidable.is_false hp := or_imp_congr_right (h hp)
end

lemma imp_iff_or_not {p q : Prop} : (p → q) ↔ (¬ p ∨ q) :=
by cases classical.prop_decidable p; simp *

lemma not_imp_iff_or {p q : Prop} : (¬ p → q) ↔ (p ∨ q) :=
by cases classical.prop_decidable p; simp *

theorem iff_imp {a b c} : ((a ↔ b) → c) ↔ ((a → b) → (b → a) → c) :=
iff.intro (λ h ha hb, h ⟨ha, hb⟩) (λ h ⟨ha, hb⟩, h ha hb)

lemma classical.forall_imp_iff_exists_not_or {α} {p : α → Prop} {q : Prop} :
  ((∀ x, p x) → q) ↔ ((∃ x, ¬ p x) ∨ q) :=
by simp [imp_iff_or_not, classical.not_forall]

def list.has_dups_core {α} [decidable_eq α] : list α → list α → bool
| (x::xs) ys := x ∈ ys ∨ xs.has_dups_core (x::ys)
| [] _ := ff

def list.has_dups {α} [decidable_eq α] (xs : list α) : bool :=
xs.has_dups_core []

def list.zip_with_index_core {α} : ℕ → list α → list (α × ℕ)
| _ [] := []
| i (x::xs) := (x,i) :: list.zip_with_index_core (i+1) xs

def list.zip_with_index {α} : list α → list (α × ℕ) :=
list.zip_with_index_core 0

def list.filter_maximal {α} (gt : α → α → bool) (l : list α) : list α :=
l.filter $ λ x, ∀ y ∈ l, ¬ gt y x

def list.m_any {α m} [monad m] (f : α → m bool) : list α → m bool
| [] := pure ff
| (x::xs) := do f_x ← f x, if f_x then pure tt else xs.m_any

meta def mk_metas_core : list expr → tactic (list expr)
| [] := pure []
| (t::ts) := do
  ms ← mk_metas_core ts,
  m ← mk_meta_var (t.instantiate_vars ms),
  pure (m::ms)

meta def expr.name_hint : expr → option name
| (expr.const n _) := n
| (expr.app a b) := a.name_hint <|> b.name_hint
| (expr.pi pp_n _ a b) := b.name_hint <|> a.name_hint <|> pp_n
| (expr.lam pp_n _ a b) := b.name_hint <|> pp_n
| (expr.sort _) := `type
| (expr.local_const _ pp_n _ _) := pp_n
| _ := name.anonymous

meta def expr.hyp_name_hint (e : expr) : name :=
match e.name_hint with
| some (name.mk_string s _) := ("h_" ++ s : string)
| _ := `h
end

meta def mk_locals_core : list expr → tactic (list expr)
| [] := pure []
| (t::ts) := do
  lcs ← mk_locals_core ts,
  lc ← mk_local' t.hyp_name_hint binder_info.default (t.instantiate_vars lcs),
  pure (lc :: lcs)

meta def expr.const_levels : expr → list level
| (expr.const n ls) := ls
| _ := []

@[inline] instance has_monad_lift.refl {m} [monad m] : has_monad_lift m m := ⟨λ _, id⟩

meta def tactic.unify_level (l1 l2 : level) : tactic unit :=
tactic.unify (expr.sort l1) (expr.sort l2)

namespace tactic

meta def unify_with_type (a b : expr) (trnsp := transparency.semireducible) (approx := ff) :
  tactic unit := do
ta ← infer_type a,
tb ← infer_type b,
unify ta tb trnsp approx,
unify a b trnsp approx

meta def minimal_tc_failure : expr → tactic expr | e := do
ff ← succeeds (type_check e),
match e with
| (expr.app a b) := minimal_tc_failure a <|> minimal_tc_failure b
| (expr.lam n bi a b) :=
  minimal_tc_failure a <|> (do
    l ← mk_local' n bi a,
    minimal_tc_failure (b.instantiate_var a))
| (expr.pi n bi a b) :=
  minimal_tc_failure a <|> (do
    l ← mk_local' n bi a,
    minimal_tc_failure (b.instantiate_var a))
| (expr.elet n t v b) :=
  minimal_tc_failure t <|> minimal_tc_failure v <|>
    minimal_tc_failure (b.instantiate_var v)
| e := pure e
end <|> pure e

end tactic

-- decidable instance for bounded existence is not short-circuiting?!?
def list.existsb {α} (p : α → bool) : list α → bool
| [] := ff
| (x :: xs) := if p x then tt else xs.existsb

meta def infer_univ (type : expr) : tactic level := do
sort_of_type ← infer_type type >>= whnf,
match sort_of_type with
| expr.sort lvl := pure lvl
| not_sort := do
  fmt ← pp not_sort,
  fail $ (to_fmt "cannot get universe level of sort:" ++ format.line ++ fmt).group.nest 1
end
