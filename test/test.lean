import super

set_option trace.super true
set_option profiler true

lemma foo (p : ℕ → Prop) (h1 : ∀ x, ¬ p x) : ∃ x, ¬ p (x + 1) :=
by super *

lemma bar (p : ℕ → Prop) : p 0 → (∀ x, p x → p (x + 1)) → p 10 :=
by super

lemma baz (a b c : ℕ) : a + (b + c) = (a + b) + c :=
by tactic.try_for 40000 `[super [add_assoc, add_zero, add_comm]]

#print baz
