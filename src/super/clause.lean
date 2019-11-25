import super.utils

namespace super
open tactic

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

end literal

@[derive decidable_eq]
meta inductive clause_type
| ff
| imp (a : expr) (b : clause_type)
| or (a : clause_type) (b : clause_type)
| atom (a : expr)

namespace clause_type

protected meta def to_string : clause_type → string
| ff := "ff"
| (imp a b) := "(imp " ++ a.to_string ++ " " ++ b.to_string ++ ")"
| (or a b) := "(or " ++ a.to_string ++ " " ++ b.to_string ++ ")"
| (atom a) := "(atom " ++ a.to_string ++ ")"

meta instance : has_to_string clause_type := ⟨clause_type.to_string⟩
meta instance : has_repr clause_type := ⟨clause_type.to_string⟩

protected meta def to_tactic_fmt : clause_type → tactic format
| ff := pure "ff"
| (imp a b) := do a ← pp a, b ← b.to_tactic_fmt, pure $ format.form ["imp", a.paren, b]
| (or a b) := do a ← a.to_tactic_fmt, b ← b.to_tactic_fmt, pure $ format.form ["or", a, b]
| (atom a) := do a ← pp a, pure $ format.form ["atom", a]

meta instance : has_to_tactic_format clause_type := ⟨clause_type.to_tactic_fmt⟩

meta def of_expr : expr → clause_type
| `(%%a ∨ %%b) := or (of_expr a) (of_expr b)
| `(false) := ff
| `(¬ %%a) := imp a ff
| e@(expr.pi _ _ a b) := if b.has_var then atom e else imp a (of_expr b)
| e := atom e

meta def to_expr : clause_type → expr
| ff := `(false)
| (or a b) := `(%%a.to_expr ∨ %%b.to_expr)
| (imp a b) := `((%%a : Prop) → (%%b.to_expr : Prop))
| (atom a) := a

meta def literals : clause_type → list literal
| ff := []
| (or a b) := a.literals ++ b.literals
| (imp a b) := literal.neg a :: b.literals
| (atom a) := [literal.pos a]

meta def instantiate_mvars : clause_type → tactic clause_type
| ff := pure ff
| (or a b) := or <$> instantiate_mvars a <*> instantiate_mvars b
| (imp a b) := imp <$> tactic.instantiate_mvars a <*> instantiate_mvars b
| (atom a) := atom <$> tactic.instantiate_mvars a

meta def abstract_mvars (mvars : list name) : clause_type → clause_type
| ff := ff
| (or a b) := or a.abstract_mvars b.abstract_mvars
| (imp a b) := imp (a.abstract_mvars mvars) b.abstract_mvars
| (atom a) := atom (a.abstract_mvars mvars)

meta def instantiate_vars (es : list expr) : clause_type → clause_type
| ff := ff
| (or a b) := or a.instantiate_vars b.instantiate_vars
| (imp a b) := imp (a.instantiate_vars es) b.instantiate_vars
| (atom a) := atom (a.instantiate_vars es)

end clause_type

@[derive decidable_eq]
meta structure clause :=
(ty : clause_type)
(prf : expr)

namespace clause

meta instance : has_to_string clause := ⟨λ c, c.ty.to_expr.to_string⟩
meta instance : has_repr clause := ⟨to_string⟩
meta instance : has_to_tactic_format clause := ⟨λ c, pp c.ty.to_expr⟩

meta def of_type_and_proof : expr → expr → tactic clause
| ty@(expr.pi _ _ a b) prf :=
  if b.has_var then do
    m ← mk_meta_var a,
    of_type_and_proof (b.instantiate_var m) (prf m)
  else
    pure { ty := clause_type.of_expr ty, prf := prf }
| ty prf := pure { ty := clause_type.of_expr ty, prf := prf }

meta def of_proof (prf : expr) : tactic clause := do
ty ← infer_type prf,
of_type_and_proof ty prf

meta def instantiate_mvars (cls : clause) : tactic clause :=
clause.mk <$> cls.ty.instantiate_mvars <*> tactic.instantiate_mvars cls.prf

meta def abstract_mvars (cls : clause) (mvars : list name) : clause :=
{ ty := cls.ty.abstract_mvars mvars, prf := cls.prf.abstract_mvars mvars }

meta def abstract_mvars' (cls : clause) (mvars : list expr) : clause :=
cls.abstract_mvars (mvars.map expr.meta_uniq_name)

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

private meta def unpack_mk_metas (ls_subst : rb_map name level) : list expr → tactic (list expr)
| [] := pure []
| (t::ts) := do
  ms ← unpack_mk_metas ts,
  m ← mk_meta_var ((t.instantiate_vars ms).instantiate_univ_mvars ls_subst),
  pure (m::ms)

meta def unpack (c : packed_clause) : tactic clause := do
ls ← mk_num_meta_univs c.univ_mvars.length,
let ls_subst := rb_map.of_list (c.univ_mvars.zip ls),
mvars ← unpack_mk_metas ls_subst c.free_var_tys,
pure { ty := c.cls.ty.instantiate_vars mvars, prf := c.cls.prf.instantiate_vars mvars }

end packed_clause

meta def clause.pack (c : clause) : tactic packed_clause := do
c ← c.instantiate_mvars,
mvars ← c.prf.sorted_mvars,
pure {
  univ_mvars := c.prf.univ_meta_vars.to_list,
  free_var_tys := mvars.map expr.meta_type,
  cls := c.abstract_mvars' mvars,
}

meta def clause.clone (c : clause) :=
pure c >>= clause.pack >>= packed_clause.unpack

end super
