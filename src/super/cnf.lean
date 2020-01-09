import super.clause super.distinct

namespace super

open clause_type tactic

meta def mk_local_hyp (type : expr) : tactic expr :=
mk_local' type.hyp_name_hint binder_info.default type

meta def mk_c (n : name) : expr :=
expr.const n []

private meta def congr (f : clause → tactic (list clause)) : clause → tactic (list clause)
| c@⟨atom _, _⟩ := pure [c]
| c@⟨ff, _⟩ := pure [c]
| ⟨or a b, prf⟩ := do
  pa ← mk_local_hyp a.to_expr,
  pb ← mk_local_hyp b.to_expr,
  csa ← f ⟨a, pa⟩,
  csb ← f ⟨b, pb⟩,
  pure $ do ⟨a', prfa'⟩ ← csa, ⟨b', prfb'⟩ ← csb, pure $
  ⟨or a' b', `(@or_imp_congr %%a.to_expr %%a'.to_expr %%b.to_expr %%b'.to_expr
    %%(pa.mk_lambda prfa') %%(pb.mk_lambda prfb') %%prf)⟩
| ⟨imp a b, prf⟩ := do
  pa ← mk_local_hyp a,
  cs ← f ⟨b, prf.app' pa⟩,
  pure $ cs.map $ λ ⟨b', prf'⟩, ⟨imp a b', pa.mk_lambda prf'⟩

private meta def clausify_core : clause → tactic (list clause)
| c := do c.check_if_debug, clause.check_results_if_debug $ match c with

| c@⟨atom `(%%a ∧ %%b), prf⟩ :=
  list.join <$> list.mmap clausify_core
  [⟨atom a, `(@and.left %%a %%b %%prf)⟩, ⟨atom b, `(@and.right %%a %%b %%prf)⟩]
| c@⟨atom `(%%a ↔ %%b), prf⟩ :=
  list.join <$> list.mmap clausify_core
  [⟨imp a (atom b), `(@iff.mp %%a %%b %%prf)⟩,
   ⟨imp b (atom a), `(@iff.mpr %%a %%b %%prf)⟩]
| c@⟨atom (expr.pi n bi t a), prf⟩ :=
  if a.has_var then do
    m ← mk_meta_var t,
    clausify_core ⟨atom (a.instantiate_var m), prf.app' m⟩
  else
    clausify_core ⟨imp t (atom a), prf⟩
| c@⟨atom `(%%a ∨ %%b), prf⟩ :=
  clausify_core ⟨or (atom a) (atom b), prf⟩
| c@⟨atom `(¬ %%a), prf⟩ :=
  clausify_core ⟨imp a ff, prf⟩
| c@⟨atom `(@Exists %%α %%p), prf⟩ := do
  nonempty_ty ← mk_mapp ``nonempty [α],
  nonempty_inst ← mk_instance nonempty_ty <|> mk_meta_var nonempty_ty,
  sk_term ← mk_mapp ``classical.epsilon [α, nonempty_inst, p],
  prf' ← mk_mapp ``classical.epsilon_spec_aux [α, nonempty_inst, p, prf],
  clausify_core ⟨atom (p.app' sk_term), prf'⟩
| c@⟨atom `(@eq Prop %%a %%b), prf⟩ := do
  prf' ← mk_mapp ``eq.to_iff [a, b, prf],
  clausify_core ⟨atom `(%%a ↔ %%b), prf'⟩
| ⟨atom (expr.app (expr.app (expr.app (expr.const ``ne [l]) ty) a) b), prf⟩ :=
  clausify_core ⟨imp (expr.const' ``eq [l] ty a b) ff, prf⟩
| ⟨atom `(false), prf⟩ := pure [⟨ff, prf⟩]
| ⟨atom `(true), prf⟩ := pure []

| c@⟨imp `(%%a ∧ %%b) d, prf⟩ :=
  clausify_core ⟨imp a (imp b d), `((@and_imp %%a %%b %%d.to_expr).mp %%prf)⟩
| c@⟨imp `(%%a ∨ %%b) d, prf⟩ := do
  prf_ad ← mk_mapp ``function.comp [none, none, none, prf, mk_c ``or.inl a b],
  prf_bd ← mk_mapp ``function.comp [none, none, none, prf, mk_c ``or.inr a b],
  list.join <$> list.mmap clausify_core [⟨imp a d, prf_ad⟩, ⟨imp b d, prf_bd⟩]
| c@⟨imp a@`(@Exists %%α %%p) b, prf⟩ := do
  witness ← mk_meta_var α,
  ex_prf ← mk_mapp ``Exists.intro [α, p, witness],
  prf' ← mk_mapp ``function.comp [none, none, none, prf, ex_prf],
  clausify_core ⟨imp (p.app' witness) b, prf'⟩
| c@⟨imp (expr.pi n bi a b) d, prf⟩ := do
  a_prop ← is_prop a,
  ha ← mk_local_hyp a,
  b_prop ← is_prop (b.instantiate_var ha),
  if b.has_var ∧ b_prop then do
    m ← mk_meta_var a,
    let p := expr.lam n bi a b,
    x ← mk_local' `x binder_info.default a,
    b' ← mk_mapp ``Exists [a, x.mk_lambda `(¬ %%(p.app' x))],
    prf' ← mk_mapp ``classical.forall_imp_iff_exists_not_or [a, p, d.to_expr],
    prf' ← mk_mapp ``iff.mp [none, none, prf', prf],
    clausify_core ⟨or (atom b') d, prf'⟩
  else if ¬ b.has_var ∧ a_prop ∧ b_prop then do
    let prf_or_not_imp := `((@imp_iff_or_not %%a %%b).mpr),
    prf' ← mk_mapp ``function.comp [none, none, none, prf, prf_or_not_imp],
    clausify_core ⟨imp `(¬ %%a ∨ %%b) d, prf'⟩
  else
    congr clausify_core c
| c@⟨imp `(¬ %%a) b, prf⟩ := do
  b_prop ← is_prop b.to_expr,
  if b_prop then
    clausify_core ⟨or (atom a) b, `((@not_imp_iff_or %%a %%b.to_expr).mp %%prf)⟩
  else
    congr clausify_core c
| ⟨imp `(false) b, prf⟩ := pure []
| ⟨imp `(true) b, prf⟩ := clausify_core ⟨b, prf.app' `(true.intro)⟩
| ⟨imp `(@eq Prop %%a %%b) c, prf⟩ := do
  prf' ← mk_mapp ``propext [a, b],
  prf' ← mk_mapp ``function.comp [none, none, none, prf, prf'],
  clausify_core ⟨imp `(%%a ↔ %%b) c, prf'⟩
| ⟨imp (expr.app (expr.app (expr.app (expr.const ``ne [l]) ty) a) b) c, prf⟩ :=
  clausify_core ⟨imp ((expr.const' ``eq [l] ty a b).imp `(false)) c, prf⟩
| ⟨imp `(%%a ↔ %%b) c, prf⟩ :=
  clausify_core ⟨imp (a.imp b) (imp (b.imp a) c),
    `((@iff_imp %%a %%b %%c.to_expr).mp %%prf)⟩

| c := congr clausify_core c
end

meta def clause.clausify (c : clause) : tactic (list clause) := do
cs ← clausify_core c,
let cs := cs.filter (λ c, ¬ c.is_taut),
let cs := cs.map clause.distinct,
let cs := cs.dup_by_native (λ c, c.ty.to_expr),
pure cs

meta def clause_type.is_clausified : clause_type → bool
| (atom `(%%a ∧ %%b)) := ff
| (atom `(%%a ↔ %%b)) := ff
| (atom (expr.pi n bi t a)) := ff
| (atom `(%%a ∨ %%b)) := ff
| (atom `(¬ %%a)) := ff
| (atom `(@Exists %%α %%p)) := ff
| (atom `(false)) := ff
| (atom `(true)) := ff
| (atom `(@eq Prop %%_ %%_)) := ff
| (atom `(_ ≠ _)) := ff

| (imp `(%%a ∧ %%b) d) := ff
| (imp `(%%a ∨ %%b) d) := ff
| (imp a@`(@Exists %%α %%p) b) := ff
| (imp (expr.pi n bi a b) d) := ff
| (imp `(¬ %%a) b) := ff
| (imp `(false) b) := ff
| (imp `(true) b) := ff
| (imp `(@eq Prop %%_ %%_) b) := ff
| (imp `(%%a ↔ %%b) c) := ff
| (imp `(_ ≠ _) _) := ff

| (atom _) := tt
| (imp a b) := b.is_clausified
| (or a b) := a.is_clausified ∧ b.is_clausified
| ff := tt

meta def clause.is_clausified (c : clause) : bool :=
c.ty.is_clausified

end super
