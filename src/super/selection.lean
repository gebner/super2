/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import super.prover_state

open native

namespace super

meta def simple_selection_strategy (f : term_order → clause → list ℕ)
  : literal_selection_strategy | dc := do
gt ← get_term_order, pure $
  if dc.selected.empty ∧ dc.cls.num_literals > 0
  then { selected := f gt dc.cls, ..dc }
  else dc

meta def dumb_selection : literal_selection_strategy :=
simple_selection_strategy $ λ gt c,
match c.literals.zip_with_index.filter (λ l : literal × ℕ, l.1.is_neg) with
| [] := list.range c.num_literals
| neg_lit :: _ := [neg_lit.2]
end

meta def selection21 : literal_selection_strategy :=
simple_selection_strategy $ λ gt c, list.map prod.snd $
let lits := c.literals.zip_with_index in
let maximal_lits := lits.filter_maximal $ λ i j : literal × ℕ, gt i.1.formula j.1.formula in
if maximal_lits.length = 1 then maximal_lits else
let neg_lits := lits.filter $ λ i : literal × ℕ, i.1.is_neg,
    maximal_neg_lits := neg_lits.filter_maximal $
      λ i j : literal × ℕ, gt i.1.formula j.1.formula in
if ¬ maximal_neg_lits.empty then
  maximal_neg_lits.take 1
else
  maximal_lits

meta def selection22 : literal_selection_strategy :=
simple_selection_strategy $ λ gt c, list.map prod.snd $
let lits := c.literals.zip_with_index in
let maximal_lits := lits.filter_maximal $ λ i j : literal × ℕ, gt i.1.formula j.1.formula,
  maximal_lits_neg := maximal_lits.filter $ λ i : literal × ℕ, i.1.is_neg in
if ¬ maximal_lits_neg.empty then
  list.take 1 maximal_lits_neg
else
  maximal_lits

def sum {α} [has_zero α] [has_add α] : list α → α
| [] := 0
| (x::xs) := x + sum xs

section
open expr
meta def expr_size : expr → nat
| (var _) := 1
| (sort _) := 1
| (const _ _) := 1
| (mvar n pp_n t) := 1
| (local_const _ _ _ _) := 1
| (app a b) := expr_size a + expr_size b
| (lam _ _ d b) := 1 + expr_size b
| (pi _ _ d b) := 1 + expr_size b
| (elet _ t v b) := 1 + expr_size v + expr_size b
| (macro _ _) := 1
end

meta def clause_weight (c : derived_clause) : nat :=
sum (c.cls.literals.map (λ l : literal, expr_size l.formula + if l.is_pos then 10 else 1))

def find_minimal_by_core {α β} [has_lt β] [decidable_rel ((<) : β → β → Prop)]
    (f : α → β) : list α → option α → option α
| [] min := min
| (x::xs) none := find_minimal_by_core xs x
| (x::xs) (some y) := find_minimal_by_core xs $ if f x < f y then x else y

def find_minimal_by {α β} [has_lt β] [decidable_rel ((<) : β → β → Prop)]
    (xs : list α) (f : α → β) : option α :=
find_minimal_by_core f xs none

meta def age_of_clause_id : name → ℕ
| (name.mk_numeral i _) := unsigned.to_nat i
| _ := 0

local attribute [instance] def prod.has_lt {α β} [has_lt α] [has_lt β] : has_lt (α × β) :=
⟨λ s t, s.1 < t.1 ∨ (s.1 = t.1 ∧ s.2 < t.2)⟩

local attribute [instance]
def prod_has_decidable_lt {α β}
         [has_lt α] [has_lt β]
         [decidable_eq α] [decidable_eq β]
         [decidable_rel ((<) : α → α → Prop)]
         [decidable_rel ((<) : β → β → Prop)] : Π s t : α × β, decidable (s < t) :=
λ t s, or.decidable

meta def find_minimal_weight (passive : rb_map clause_id derived_clause) : clause_id :=
(derived_clause.id <$> find_minimal_by passive.values (λ c, (clause_weight c, c.id)))
  .get_or_else undefined

meta def find_minimal_age (passive : rb_map clause_id derived_clause) : clause_id :=
(derived_clause.id <$> find_minimal_by passive.values (λ c, c.id))
  .get_or_else undefined

meta def weight_clause_selection : clause_selection_strategy | iter :=
do state ← get, return $ find_minimal_weight state.passive

meta def oldest_clause_selection : clause_selection_strategy | iter :=
do state ← get, return $ find_minimal_age state.passive

meta def age_weight_clause_selection (thr mod : ℕ) : clause_selection_strategy | iter :=
if iter % mod < thr then
  weight_clause_selection iter
else
  oldest_clause_selection iter

end super
