import super

set_option trace.super true
set_option profiler true

lemma foo (p : ℕ → Prop) (h1 : ∀ x, ¬ p x) : ∃ x, ¬ p (x + 1) :=
by super *

lemma bar (p : ℕ → Prop) : p 0 → (∀ x, p x → p (x + 1)) → p 10 :=
by super

lemma exst {α} (h : ∃ x : α, x = x) : true :=
by super *

lemma and_false' (h : ∃ w : ℕ, ∀ x : ℕ, w = x ∧ false) : false :=
by super *

lemma baz (a b c : ℕ) : a + (b + c) = (a + b) + c :=
by super [add_assoc, add_zero, add_comm]

#print baz
