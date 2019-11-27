import super.clause super.distinct

namespace super

open clause_type tactic

meta def mk_local_hyp (type : expr) : tactic expr :=
mk_local' `h binder_info.default type

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
  cs ← f ⟨b, prf pa⟩,
  pure $ cs.map $ λ ⟨b', prf'⟩, ⟨imp a b', pa.mk_lambda prf'⟩

private meta def chk (f : clause → tactic (list clause)) (cls : clause) : tactic (list clause) :=
trace cls.ty >>
trace cls.prf >>
cls.check >> f cls

private meta def clausify_core : clause → tactic (list clause)
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
    clausify_core ⟨atom a, prf m⟩
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
  prf' ← mk_mapp ``classical.epsilon_spec [α, p, prf],
  clausify_core ⟨atom (p.app' sk_term), prf'⟩

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
  b_prop ← is_prop b,
  if b.has_var ∧ b_prop then do
    m ← mk_meta_var a,
    let p := expr.lam n bi a b,
    b' ← mk_mapp ``Exists [a, p],
    prf' ← mk_mapp ``classical.forall_imp_iff_exists_not_or [a, p, d.to_expr],
    prf' ← mk_mapp ``iff.mp [none, none, prf', prf],
    clausify_core ⟨or (imp b' ff) d, prf'⟩
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

| c := congr clausify_core c

meta def clause.clausify (c : clause) : tactic (list clause) := do
cs ← clausify_core c,
let cs := cs.map clause.dedup,
let cs := cs.filter (λ c, ¬ c.is_taut),
let cs := cs.dup_by_native (λ c, c.ty.to_expr),
pure cs

-- set_option trace.check true
-- set_option trace.app_builder true
-- example (a b c) (h : b ∨ a → a ∨ a → (∃ m, m > 10 → c) → a ∧ b ∧ ∃ n, n > 0) : true := by do
-- h ← get_local `h,
-- c ← clause.of_proof h,
-- trace c,
-- cs ← c.clausify,
-- trace cs,
-- trace $ cs.map (λ c, c.prf),
-- cs.mmap $ λ c, c.check,
-- triv

end super
