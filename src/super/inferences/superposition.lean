import super.prover_state super.resolve

namespace super
open native tactic expr

meta def clause.flip (c : clause) (i : ℕ) : tactic clause :=
match c.literals.nth i with
| some (literal.pos e@(app (app (app (const ``eq [l]) ty) a) b)) :=
  clause.resolve c i ⟨clause_type.imp e (clause_type.atom (const ``eq [l] ty b a)),
    const ``eq.symm [l] ty a b⟩ 0
| some (literal.neg e@(app (app (app (const ``eq [l]) ty) a) b)) :=
  clause.resolve ⟨clause_type.imp (const ``eq [l] ty b a) (clause_type.atom e),
    const ``eq.symm [l] ty b a⟩ 1 c i
| _ := fail $ "clause_flip " ++ to_string c ++ " " ++ to_string i
end

meta def clause.rewrite_in_ctx (ctx : expr) (ltr : bool)
  (a : clause) (ai : ℕ) (b : clause) (bi : ℕ) : tactic clause := do
a ← if ltr then pure a else a.flip ai,
some (literal.pos eq_f@`(@eq %%ty %%l %%r)) ← pure $ a.literals.nth ai,
some t ← pure $ b.literals.nth bi,
let prf_subst :=
  let lvls := eq_f.get_app_fn.const_levels in
  if t.is_pos then
    expr.const ``eq.subst lvls ty ctx l r
  else
    expr.const ``eq.substr lvls ty ctx r l,
let (l',r') := if t.is_pos then (l, r) else (r, l),
let c_subst : clause :=
  ⟨clause_type.imp eq_f (clause_type.imp (ctx.app' l')
    (clause_type.atom (ctx.app' r'))),
   prf_subst⟩,
unify t.formula (ctx.app' l),
a' ← clause.resolve a ai c_subst 0,

-- huge hack: unify for some reason doesn't
-- seem to infer some type class instances...
ms ← l.sorted_mvars, ms.mmap' (λ m, do
  t ← infer_type m >>= instantiate_mvars,
  if t.has_meta_var then skip
  else try $ mk_instance t >>= unify m),

if t.is_pos then
  clause.resolve b bi a' ai
else
  clause.resolve a' (ai + 1) b bi

meta def clause.krewrite (ltr : bool)
  (a : clause) (ai : ℕ) (b : clause) (bi : ℕ) : tactic (option clause) := do
a ← if ltr then pure a else a.flip ai,
some (literal.pos `(@eq %%ty %%l %%r)) ← pure $ a.literals.nth ai,
some t ← pure $ b.literals.nth bi,
ctx ← kabstract t.formula l transparency.reducible ff,
if ¬ ctx.has_var then pure none else do
let ctx := expr.lam `x binder_info.default ty ctx,
some () ← try_core (type_check ctx) | pure none,
pure <$> a.rewrite_in_ctx ctx tt ai b bi

-- TODO: ignore at least dependent arguments
meta def closed_subterms (e : expr) : list expr :=
rb_set.to_list $ e.fold mk_rb_set $ λ e i s,
  match e with
  | (expr.mvar _ _ _) := s
  | _ := if e.has_var then s else s.insert e
  end

private meta def superposition_core (gt : term_order)
  (a : derived_clause) (b : derived_clause) :
  list (prover (list clause)) := do
(literal.pos `(@eq %%ty %%l %%r), ai) ← a.selected_lits | [],
(l,r, ltr) ← [(l,r,tt), (r,l,ff)],
guard $ ¬ gt r l,
(t, bi) ← b.selected_lits,
st ← closed_subterms t.formula,
pure $ do
some () ← try_core (unify l st transparency.reducible) | pure [],
st_ty ← infer_type st,
some () ← try_core (unify ty st_ty transparency.semireducible) | pure [],
l ← instantiate_mvars l,
r ← instantiate_mvars r,
tt ← pure (¬ gt r l : bool) | pure [],
a ← a.cls.instantiate_mvars,
b ← b.cls.instantiate_mvars,
option.to_list <$> a.krewrite ltr ai b bi

meta def inference.forward_superposition : inference_rule | given := do
gt ← get_term_order,
active ← get_active,
retrieve_packed $ do
act ← active.values,
superposition_core gt act given

meta def inference.backward_superposition : inference_rule | given := do
gt ← get_term_order,
active ← get_active,
retrieve_packed $ do
act ← active.values,
superposition_core gt given act

meta def inference.unify_eq : inference_rule | given :=
retrieve_packed $ do
(literal.neg `(%%l = %%r), i) ← given.cls.literals.zip_with_index | [],
pure $ do
some () ← try_core (unify l r) | pure [],
rfl_prf ← mk_eq_refl l,
pure <$> given.cls.propg_pos i rfl_prf

meta def simplification.pos_refl : simplification_rule | cls := do
is_redundant ← cls.literals.mfoldl (λ is_redundant l,
  match is_redundant, l with
  | tt, _ := pure tt
  | _, literal.pos `(%%a = %%b) :=
    succeeds (is_def_eq a b transparency.reducible)
  | ff, _ := pure ff
  end) ff,
if is_redundant then pure none else pure cls

meta def simplification.neg_refl : simplification_rule | cls :=
first (do
  (literal.neg `(%%a = %%b), i) ← cls.literals.zip_with_index | [],
  pure $ do
  is_def_eq a b,
  rfl_prf ← mk_eq_refl a,
  some <$> cls.propg_pos i rfl_prf)
<|> pure cls

meta def preprocessing.pos_refl : preprocessing_rule :=
simplification.pos_refl.as_preprocessing_rule

meta def preprocessing.neg_refl : preprocessing_rule :=
simplification.neg_refl.as_preprocessing_rule

open expr
meta def simplification.flip_eq : simplification_rule | c := do
gt ← get_term_order,
pure <$> c.literals.zip_with_index.mfoldl (λ c l,
  match l.1.formula with
  | e@(app (app (app (const ``eq [lvl]) ty) a) b) := do
    let e' := const ``eq [lvl] ty b a,
    if gt e e' then
      c.flip l.2
    else
      pure c
  | _ := pure c
  end) c

meta def preprocessing.flip_eq : preprocessing_rule :=
simplification.flip_eq.as_preprocessing_rule

end super
