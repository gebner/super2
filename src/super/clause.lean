import super.utils super.debug

namespace super
open tactic native

@[derive decidable_eq]
meta inductive literal
| pos (a : expr)
| neg (a : expr)

namespace literal

protected meta def to_string : literal → string
| (pos a) := "pos " ++ a.to_string
| (neg a) := "neg " ++ a.to_string

meta instance : has_to_string literal := ⟨literal.to_string⟩
meta instance : has_repr literal := ⟨literal.to_string⟩

protected meta def to_tactic_fmt : literal → tactic format
| (pos a) := do a ← pp a, pure $ "pos " ++ a
| (neg a) := do a ← pp a, pure $ "neg " ++ a

meta instance : has_to_tactic_format literal := ⟨literal.to_tactic_fmt⟩

meta def is_pos : literal → bool
| (pos _) := tt
| (neg _) := ff

meta def is_neg : literal → bool
| (neg _) := tt
| (pos _) := ff

meta def formula : literal → expr
| (neg f) := f
| (pos f) := f

meta def instantiate_mvars : literal → tactic literal
| (neg f) := neg <$> tactic.instantiate_mvars f
| (pos f) := pos <$> tactic.instantiate_mvars f

end literal

@[derive decidable_eq]
meta inductive clause_type
| ff
| imp (a : expr) (b : clause_type)
| disj (is_or : bool) (a : clause_type) (b : clause_type)
| atom (a : expr)

namespace clause_type

protected meta def to_string : clause_type → string
| ff := "ff"
| (imp a b) := "(imp " ++ a.to_string ++ " " ++ b.to_string ++ ")"
| (disj io a b) := "(disj " ++ repr io ++ " " ++ a.to_string ++ " " ++ b.to_string ++ ")"
| (atom a) := "(atom " ++ a.to_string ++ ")"

meta instance : has_to_string clause_type := ⟨clause_type.to_string⟩
meta instance : has_repr clause_type := ⟨clause_type.to_string⟩

protected meta def to_tactic_fmt : clause_type → tactic format
| ff := pure "ff"
| (imp a b) := do a ← pp a, b ← b.to_tactic_fmt, pure $ format.form ["imp", a.paren, b]
| (disj io a b) := do a ← a.to_tactic_fmt, b ← b.to_tactic_fmt, pure $ format.form ["or", to_fmt io, a, b]
| (atom a) := do a ← pp a, pure $ format.form ["atom", a]

meta instance : has_to_tactic_format clause_type := ⟨clause_type.to_tactic_fmt⟩

meta def of_expr : expr → tactic clause_type
| `(%%a ∨ %%b) := disj tt <$> of_expr a <*> of_expr b
| `(false) := pure ff
| `(¬ %%a) := pure $ imp a ff
| `(psum %%a %%b) := disj bool.ff <$> of_expr a <*> of_expr b
| e@(expr.pi _ _ a b) :=
  if b.has_var then
    pure $ atom e
  else
    imp a <$> of_expr b
| e := pure $ atom e

meta def to_expr : clause_type → tactic expr
| ff := pure `(false)
| (disj tt a b) := do a ← a.to_expr, b ← b.to_expr, pure `(%%a ∨ %%b)
| (disj bool.ff a b) := do a ← a.to_expr, b ← b.to_expr, mk_mapp ``psum [a,b]
| (imp a ff) := do
  ip ← is_prop a,
  pure $ if ip then `(¬ %%a) else a.imp `(false)
| (imp a b) := a.imp <$> b.to_expr
| (atom a) := pure a

meta def to_expr_wrong : clause_type → expr
| ff := `(false)
| (disj tt a b) := `(%%a.to_expr_wrong ∨ %%b.to_expr_wrong)
| (disj bool.ff a b) := `(psum.{1 1} %%a.to_expr_wrong %%b.to_expr_wrong)
| (imp a ff) := `(¬ %%a)
| (imp a b) := `((%%a : Prop) → %%b.to_expr_wrong : Prop)
| (atom a) := a

meta def literals : clause_type → list literal
| ff := []
| (disj _ a b) := a.literals ++ b.literals
| (imp a b) := literal.neg a :: b.literals
| (atom a) := [literal.pos a]

meta def num_literals (ty : clause_type) : ℕ :=
ty.literals.length

meta def num_pos_literals : clause_type → ℕ
| ff := 0
| (disj _ a b) := a.num_pos_literals + b.num_pos_literals
| (imp a b) := b.num_pos_literals
| (atom a) := 1

meta def num_neg_literals : clause_type → ℕ
| ff := 0
| (disj _ a b) := a.num_neg_literals + b.num_neg_literals
| (imp a b) := b.num_neg_literals + 1
| (atom a) := 0

meta def instantiate_mvars : clause_type → tactic clause_type
| ff := pure ff
| (disj io a b) := disj io <$> instantiate_mvars a <*> instantiate_mvars b
| (imp a b) := imp <$> tactic.instantiate_mvars a <*> instantiate_mvars b
| (atom a) := atom <$> tactic.instantiate_mvars a

meta def abstract_mvars (mvars : list name) : clause_type → clause_type
| ff := ff
| (disj io a b) := disj io a.abstract_mvars b.abstract_mvars
| (imp a b) := imp (a.abstract_mvars mvars) b.abstract_mvars
| (atom a) := atom (a.abstract_mvars mvars)

meta def abstract_locals (locals : list name) : clause_type → clause_type
| ff := ff
| (disj io a b) := disj io a.abstract_locals b.abstract_locals
| (imp a b) := imp (a.abstract_locals locals) b.abstract_locals
| (atom a) := atom (a.abstract_locals locals)

meta def instantiate_vars (es : list expr) : clause_type → clause_type
| ff := ff
| (disj io a b) := disj io a.instantiate_vars b.instantiate_vars
| (imp a b) := imp (a.instantiate_vars es) b.instantiate_vars
| (atom a) := atom (a.instantiate_vars es)

meta def instantiate_univ_mvars (subst : rb_map name level) : clause_type → clause_type
| ff := ff
| (disj io a b) := disj io a.instantiate_univ_mvars b.instantiate_univ_mvars
| (imp a b) := imp (a.instantiate_univ_mvars subst) b.instantiate_univ_mvars
| (atom a) := atom (a.instantiate_univ_mvars subst)

meta def instantiate_univ_params (subst : list (name × level)) : clause_type → clause_type
| ff := ff
| (disj io a b) := disj io a.instantiate_univ_params b.instantiate_univ_params
| (imp a b) := imp (a.instantiate_univ_params subst) b.instantiate_univ_params
| (atom a) := atom (a.instantiate_univ_params subst)

meta def pos_lits (ty : clause_type) : list expr :=
do literal.pos l ← ty.literals | [], [l]

meta def neg_lits (ty : clause_type) : list expr :=
do literal.neg l ← ty.literals | [], [l]

meta def is_taut (ty : clause_type) : bool :=
ty.pos_lits ∩ ty.neg_lits ≠ []

end clause_type

@[derive decidable_eq]
meta structure clause :=
(ty : clause_type)
(prf : expr)

namespace clause

meta instance : has_to_string clause := ⟨λ c, c.ty.to_string⟩
meta instance : has_repr clause := ⟨to_string⟩
meta instance : has_to_tactic_format clause := ⟨λ c, pp c.ty.to_expr_wrong⟩

meta def of_type_and_proof : expr → expr → tactic clause
| ty@(expr.pi _ _ a b) prf :=
  if b.has_var then do
    m ← mk_meta_var a,
    of_type_and_proof (b.instantiate_var m) (prf.app' m)
  else do
    ty ← clause_type.of_expr ty,
    pure ⟨ty, prf⟩
| ty prf := do
  ty ← clause_type.of_expr ty,
  pure ⟨ty, prf⟩

meta def of_proof (prf : expr) : tactic clause := do
ty ← infer_type prf,
ty ← instantiate_mvars ty,
ty ← head_beta ty,
of_type_and_proof ty prf

meta def of_const (n : name) : tactic clause :=
mk_const n >>= of_proof

meta def literals (c : clause) : list literal :=
c.ty.literals

meta def num_literals (c : clause) : ℕ :=
c.ty.num_literals

meta def instantiate_mvars (cls : clause) : tactic clause :=
clause.mk <$> cls.ty.instantiate_mvars <*> tactic.instantiate_mvars cls.prf

meta def instantiate_univ_mvars (cls : clause) (subst : rb_map name level) : clause :=
⟨cls.ty.instantiate_univ_mvars subst, cls.prf.instantiate_univ_mvars subst⟩

meta def instantiate_univ_params (cls : clause) (subst : list (name × level)) : clause :=
⟨cls.ty.instantiate_univ_params subst, cls.prf.instantiate_univ_params subst⟩

meta def abstract_mvars (cls : clause) (mvars : list name) : clause :=
{ ty := cls.ty.abstract_mvars mvars, prf := cls.prf.abstract_mvars mvars }

meta def abstract_mvars' (cls : clause) (mvars : list expr) : clause :=
cls.abstract_mvars (mvars.map expr.meta_uniq_name)

meta def abstract_locals (cls : clause) (locals : list name) : clause :=
⟨cls.ty.abstract_locals locals, cls.prf.abstract_locals locals⟩

meta def instantiate_vars (cls : clause) (es : list expr) : clause :=
⟨cls.ty.instantiate_vars es, cls.prf.instantiate_vars es⟩

meta def is_taut (cls : clause) : bool :=
cls.ty.is_taut

meta def check (cls : clause) : tactic unit :=
on_exception (do trace "\n", trace cls.prf, trace cls.ty, trace_call_stack) $ do
when cls.prf.has_var (fail $ to_fmt "proof has de Bruijn variables"),
ty ← cls.ty.to_expr,
when ty.has_var (fail $ to_fmt "type has de Bruijn variables"),
type_check ty,
type_check cls.prf,
infer_type cls.prf >>= is_def_eq ty

@[inline]
meta def check_if_debug (cls : clause) : tactic unit :=
when_debug cls.check

@[inline]
meta def check_result_if_debug {m} [monad m] [has_monad_lift tactic m] : m clause → m clause :=
check_result_when_debug (monad_lift ∘ check)

@[inline]
meta def check_results_if_debug {m} [monad m] [has_monad_lift tactic m] :
  m (list clause) → m (list clause) :=
check_result_when_debug (λ cs, monad_lift $ cs.mmap' check)

end clause

@[derive decidable_eq]
meta structure packed_clause :=
(univ_mvars : list name)
(free_var_tys : list expr)
(cls : clause)

namespace packed_clause
open native

meta instance : has_to_string packed_clause := ⟨to_string ∘ packed_clause.cls⟩
meta instance : has_repr packed_clause := ⟨to_string⟩
meta instance : has_to_tactic_format packed_clause := ⟨tactic.pp ∘ packed_clause.cls⟩

meta def mk_metas (c : packed_clause) : tactic (list expr) :=
mk_metas_core c.free_var_tys

meta def mk_locals (c : packed_clause) : tactic (list expr) :=
mk_locals_core c.free_var_tys

meta def refresh_univ_mvars (c : packed_clause) : tactic packed_clause :=
if c.univ_mvars = [] then pure c else do
ls ← mk_num_meta_univs c.univ_mvars.length,
let ls_subst := rb_map.of_list (c.univ_mvars.zip ls),
pure {
  univ_mvars := ls.map level.mvar_name,
  free_var_tys := c.free_var_tys.map (λ t, t.instantiate_univ_mvars ls_subst),
  cls := c.cls.instantiate_univ_mvars ls_subst
}

meta def unpack (c : packed_clause) : tactic clause := do
c ← c.refresh_univ_mvars,
mvars ← c.mk_metas,
pure $ c.cls.instantiate_vars mvars

meta def unpack_quantified (c : packed_clause) : tactic clause := do
c ← c.refresh_univ_mvars,
ty ← c.cls.ty.to_expr,
let ty' := c.free_var_tys.foldl (λ e x, expr.pi x.hyp_name_hint binder_info.default x e) ty,
let prf' := c.free_var_tys.foldl (λ e x, expr.lam x.hyp_name_hint binder_info.default x e) c.cls.prf,
pure ⟨clause_type.atom ty', prf'⟩

meta def unpack_with_locals (c : packed_clause) : tactic clause := do
c ← c.refresh_univ_mvars,
lcs ← c.mk_locals,
pure $ c.cls.instantiate_vars lcs

end packed_clause

meta def clause.pack (c : clause) : tactic packed_clause := do
c ← c.instantiate_mvars,
mvars ← c.prf.sorted_mvars,
free_var_tys ← abstract_mvar_telescope mvars,
pure {
  univ_mvars := c.prf.univ_meta_vars.to_list,
  free_var_tys := free_var_tys,
  cls := c.abstract_mvars' mvars,
}

meta def clause.clone (c : clause) : tactic clause :=
pure c >>= clause.pack >>= packed_clause.unpack

meta def clause.with_locals (c : clause) : tactic clause :=
pure c >>= clause.pack >>= packed_clause.unpack_with_locals

meta def clause.with_locals_unsafe (c : clause) : tactic clause := do
mvars ← c.prf.sorted_mvars,
lcs ← abstract_mvar_telescope mvars >>= mk_locals_core,
(mvars.zip lcs).mmap' (λ x, unify x.1 x.2),
c.instantiate_mvars

namespace clause

meta def mk_decl (c : clause) (i : ℕ) : tactic expr := do
c ← c.instantiate_mvars,
mvars ← c.prf.sorted_mvars,
free_var_tys ← abstract_mvar_telescope mvars,
c_ty ← c.ty.to_expr,
let ty := free_var_tys.foldl (λ e x, expr.pi `x binder_info.default x e)
  (c_ty.abstract_mvars' mvars),
let prf := free_var_tys.foldl (λ e x, expr.lam `x binder_info.default x e)
  (c.prf.abstract_mvars' mvars),
ty_univ ← infer_univ ty,
c_ty_univ ← infer_univ c_ty,
new_prf ← add_aux_decl ((`_super.step).mk_numeral (unsigned.of_nat i))
  ty prf (ty_univ = level.zero),
let new_prf := new_prf.mk_app mvars.reverse,
clause.check_if_debug ⟨c.ty, new_prf⟩,
pure new_prf

end clause

end super
