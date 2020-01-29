import super
open tactic

set_option trace.super true
set_option profiler true

def prime (n : ℕ) := ∀ d, d ∣ n → d = 1 ∨ d = n

set_option trace.check true

lemma nat_mul_cancel_one {m n : ℕ} : m ≠ 0 → m * n = m → n = 1 :=
by cases m; super [gt, nat.zero_lt_succ,
nat.eq_of_mul_eq_mul_left, mul_one, zero_mul, nat.not_lt_zero]

lemma not_prime_zero : ¬ prime 0 :=
by intro h; cases h 2 ⟨0, by simp⟩; cases h_1

example {m n : ℕ} : prime (m * n) → m = 1 ∨ n = 1 :=
by super [prime, dvd_refl, dvd_mul_right, dvd_mul_left,
nat_mul_cancel_one, not_prime_zero, mul_zero, zero_mul]

example : nat.zero ≠ nat.succ nat.zero := by super [nat.zero_lt_succ, ne_of_lt]
example (x y : ℕ) : nat.succ x = nat.succ y → x = y := by super [nat.succ_inj]
example (i) (a b c : i) : [a,b,c] = [b,c,a] -> a = b ∧ b = c := by super [list.cons.inj]

definition is_positive (n : ℕ) := n > 0
example (n : ℕ) : n > 0 ↔ is_positive n := by super [is_positive]

example (m n : ℕ) : 0 + m = 0 + n → m = n :=
by super [zero_add]

example : ∀x y : ℕ, x + y = y + x :=
begin intros, have h : nat.zero = 0 := rfl, induction x,
      super [add_zero, zero_add],
      super [*, nat.add_succ, nat.succ_add] end

example (i) [inhabited i] : nonempty i := by super *
example (i) [nonempty i] : ¬(inhabited i → false) :=
by super [classical.inhabited_of_nonempty]

example : nonempty ℕ := by super
example : ¬(inhabited ℕ → false) := by super

example {a b} : ¬(b ∨ ¬a) ∨ (a → b) := by super
example {a} : a ∨ ¬a := by super
example {a} : (a ∧ a) ∨ (¬a ∧ ¬a) := by super
example {a} : ¬a → (¬a ∧ ¬a) := by super
example {a} : a ∨ a → a := by super
example (i) (c : i) (p : i → Prop) (f : i → i) :
  p c → (∀x, p x → p (f x)) → p (f (f (f c))) := by super

example (i : Type) (p : i → Prop) : ∀x, p x → ∃x, p x := by super

example (i) [nonempty i] (p : i → i → Prop) : (∀x y, p x y) → ∃x, ∀z, p x z :=
by super

example (i) [nonempty i] (p : i → Prop) : (∀x, p x) → ¬¬∀x, p x := by super *

-- Requires non-empty domain.
example {i} [nonempty i] (p : i → Prop) :
  (∀x y, p x ∨ p y) → ∃x y, p x ∧ p y := by super *

example (i) (a b : i) (p : i → Prop) (H : a = b) : p b → p a :=
by super *

example (i) (a b : i) (p : i → Prop) (H : a = b) : p a → p b :=
by super *

example (i) (a b : i) (p : i → Prop) (H : a = b) : p b = p a :=
by super *

example (i) (c : i) (p : i → Prop) (f g : i → i) :
p c → (∀x, p x → p (f x)) → (∀x, p x → f x = g x) → f (f c) = g (g c) :=
by super

-- This example from Davis-Putnam actually requires a non-empty domain

example (i) [nonempty i] (f g : i → i → Prop) :
  ∃x y, ∀z, (f x y → f y z ∧ f z z) ∧ (f x y ∧ g x y → g x z ∧ g z z) :=
by super

example (person) [nonempty person] (drinks : person → Prop) :
  ∃canary, drinks canary → ∀other, drinks other := by super

example {p q : ℕ → Prop} {r} : (∀x y, p x ∧ q y ∧ r) -> ∀x, (p x ∧ r ∧ q x) :=
by super

example {α} [add_group α] (x : α) : 0 + 0 + x + 0 + 0 + 0 = x :=
by super [add_zero, zero_add]
