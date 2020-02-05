import super.clause super.distinct
universes u v

#print or.rec
#print Exists.rec
#print nat.less_than_or_equal.rec
#print eq.rec
#print trivial
#print true
#print default.sizeof
#print cond
#print measure

namespace classical

noncomputable def not_not' {α : Sort u} (h : (α → false) → false) : α :=
match type_decidable α with
| (psum.inl a) := a
| (psum.inr not_a) := (h not_a).elim
end

variables {α : Sort u} [nonempty α] (p : α → Sort v)

noncomputable def iota : α :=
epsilon (λ x, p x → false)

noncomputable def epsilon' : α :=
iota (λ x, p x → false)

variables {p}

noncomputable def iota_spec (h : p (iota p)) : ∀ x, p x :=
λ x, not_not' $ λ not_px, epsilon_spec ⟨x, not_px⟩ h

noncomputable def epsilon'_spec (x : α) (h : p x) : p (epsilon' p) :=
not_not' $ λ not_p_eps : (λ x, p x → false) _, iota_spec not_p_eps x h

lemma epsilon_spec' {p : α → Prop} (h : ∃ x, p x) : p (epsilon p) :=
epsilon_spec h

end classical

namespace Exists

noncomputable def witness {α} {p : α → Prop} (h : ∃ x, p x) : α :=
classical.some h

end Exists

section
open_locale classical

lemma nonempty_or_nonempty_pi {α : Sort u} {β : α → Sort v} :
  nonempty α ∨ nonempty (∀ x, β x) :=
if h : nonempty α then
  or.inl h
else
  or.inr ⟨λ x, (h ⟨x⟩).elim⟩

lemma nonempty_or_nonempty_fun {α : Sort u} {β : Sort v} :
  nonempty α ∨ nonempty (α → β) :=
nonempty_or_nonempty_pi

lemma or_imp {p q : Prop} : p ∨ (p → q) :=
by by_cases p; simp *

end

namespace super

open clause_type tactic

variable (wrap_sk_term : expr → tactic expr)

private meta def clausify_neg : expr → tactic (option (list clause))
| `(false) := pure (some [])
| `(true) := pure (some [⟨clause_type.atom `(true), `(true.intro)⟩])
| ab@`(%%a ∧ %%b) :=
  pure $ some [⟨((clause_type.atom ab).imp b).imp a, `(@and.intro %%a %%b)⟩]
| ab@`(%%a ∨ %%b) :=
  pure $ some [
    ⟨(clause_type.atom ab).imp a, `(@or.inl %%a %%b)⟩,
    ⟨(clause_type.atom ab).imp b, `(@or.inr %%a %%b)⟩
  ]
| a@`(@Exists %%α %%p) := do
  m ← mk_meta_var α,
  prf ← mk_mapp ``exists.intro [α, p, m],
  pure $ some [⟨(clause_type.atom a).imp (p.app' m), prf⟩]
| not_a@`(¬ %%a) := do
  prf ← mk_mapp ``classical.or_not [a],
  pure $ some [⟨clause_type.disj tt (clause_type.atom a) (clause_type.atom not_a), prf⟩]
| ab@`(%%a ↔ %%b) :=
  pure $ some [⟨((clause_type.atom ab).imp (b.imp a)).imp (a.imp b),
    `(@iff.intro %%a %%b)⟩]
| ab@`(%%a ≠ %%b) := do
  e ← mk_mapp ``eq [none, a, b],
  pure $ some [⟨(clause_type.atom e).or (clause_type.atom ab),
    `(@classical.or_not %%e)⟩]
| ab@(expr.pi n bi a b) := do
  if b.has_var then do
    nonempty_ty ← mk_mapp ``_root_.nonempty [a],
    nonempty_inst ← mk_instance nonempty_ty <|> mk_meta_var nonempty_ty,
    let p := expr.lam n bi a b,
    sk_term ← mk_mapp ``classical.iota [a, nonempty_inst, p],
    sk_term ← wrap_sk_term sk_term,
    prf ← mk_mapp ``classical.iota_spec [a, nonempty_inst, p],
    pure $ some [⟨clause_type.imp (p.app' sk_term) (clause_type.atom ab), prf⟩]
  else do
    prf ← mk_mapp ``nonempty_or_nonempty_fun [a, b],
    pure $ some [
      ⟨(clause_type.atom ab).imp b,
        expr.lam `_ binder_info.default b $
          expr.lam n binder_info.default a $ expr.var 1⟩,
      ⟨clause_type.disj tt (clause_type.nonempty $ clause_type.atom a)
                      (clause_type.nonempty $ clause_type.atom ab),
        prf⟩
    ]
| ab@`(@eq Prop %%a %%b) :=
  pure $ some [
    ⟨clause_type.imp `(%%a ↔ %%b) (clause_type.atom ab),
      `(@propext %%a %%b)⟩
  ]
| c := pure none

private meta def clausify_pos : expr → tactic (option (list clause))
| `(false) := pure (some [⟨clause_type.ff.imp `(false), `(@id false)⟩])
| `(true) := pure (some [])
| ab@`(%%a ∧ %%b) :=
  pure $ some [
    ⟨(clause_type.atom a).imp ab, `(@and.left %%a %%b)⟩,
    ⟨(clause_type.atom b).imp ab, `(@and.right %%a %%b)⟩
  ]
| ab@`(%%a ∨ %%b) :=
  pure $ some [⟨(clause_type.disj tt (clause_type.atom a) (clause_type.atom b)).imp ab,
    `(@id.{0} %%ab)⟩]
| ab@`(_root_.nonempty %%a) :=
  pure $ some [⟨(clause_type.nonempty (clause_type.atom a)).imp ab, `(@id.{0} %%ab)⟩]
| ab@`(%%a ↔ %%b) :=
  pure $ some [
    ⟨((clause_type.atom b).imp a).imp ab, `(@iff.mp %%a %%b)⟩,
    ⟨((clause_type.atom a).imp b).imp ab, `(@iff.mpr %%a %%b)⟩
  ]
| ab@`(%%a ≠ %%b) := do
  e ← mk_mapp ``eq [none, a, b],
  pure $ some [⟨(clause_type.ff.imp e).imp ab, `(@id.{0} %%ab)⟩]
| not_a@`(¬ %%a) := do
  pure $ some [⟨clause_type.imp not_a (clause_type.imp a clause_type.ff),
    `(@id.{0} %%not_a)⟩]
| ab@`(@Exists %%a %%p) := do
  prf1 ← mk_mapp ``nonempty_of_exists [a, p],
  nonempty_ty ← mk_mapp ``_root_.nonempty [a],
  nonempty_inst ← mk_instance nonempty_ty <|> mk_meta_var nonempty_ty,
  sk_term ← mk_mapp ``classical.epsilon [a, nonempty_inst, p],
  sk_term ← wrap_sk_term sk_term,
  prf2 ← mk_mapp ``classical.epsilon_spec' [a, nonempty_inst, p],
  pure $ some [
    ⟨clause_type.imp ab (clause_type.nonempty $ clause_type.atom a), prf1⟩,
    ⟨clause_type.imp ab (clause_type.atom (p.app' sk_term)), prf2⟩
  ]
| ab@(expr.pi n bi a b) :=
  if b.has_var then do
    m ← mk_meta_var a,
    pure $ some [⟨clause_type.imp ab (clause_type.atom $ b.instantiate_var m),
      expr.lam `h binder_info.default ab $ expr.app (expr.var 0) m⟩]
  else do
    prf ← mk_mapp ``id [some ab],
    pure $ some [⟨clause_type.imp ab (clause_type.imp a (clause_type.atom b)), prf⟩]
| ab@`(@eq Prop %%a %%b) :=
  pure $ some [
    ⟨clause_type.imp ab (clause_type.atom `(%%a ↔ %%b)),
      `(@iff_of_eq %%a %%b)⟩
  ]
| _ := pure none

meta def clausify_idx (c : clause) (l : literal) (i : ℕ) : tactic (option (list clause)) :=
match l with
| literal.pos l := do
  some ds ← clausify_pos wrap_sk_term l | pure none,
  option.some <$> ds.mmap (λ d, clause.resolve c i d 0)
| literal.neg l := do
  some ds ← clausify_neg wrap_sk_term l | pure none,
  option.some <$> ds.mmap (λ d,
   clause.resolve d (d.num_literals - 1) c i)
end

meta def clausify_core : clause → tactic (option (list clause)) | c := do
some cs ← c.literals.zip_with_index.mfoldl (λ acc ⟨l, i⟩,
  match (acc : option (list clause)) with
  | some cs := pure (some cs)
  | none := clausify_idx wrap_sk_term c l i
  end) none | pure none,
(some ∘ list.join) <$>
  cs.mmap (λ c, do
    some cs ← clausify_core c | pure [c],
    pure cs)

meta def clause.clausify (c : clause) : tactic (list clause) := do
some cs ← clausify_core wrap_sk_term c |
  pure (if c.is_taut then [] else [c]),
let cs := cs.filter (λ c, ¬ c.is_taut),
cs ← cs.mmap clause.distinct,
-- TODO
-- let cs := cs.dup_by_native (λ c, c.ty.to_expr),
pure cs

end super
