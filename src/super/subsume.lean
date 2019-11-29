import super.clause

namespace super
open tactic

private meta def unify_lit (a b : literal) : tactic unit := do
guard $ a.is_pos = b.is_pos,
unify a.formula b.formula transparency.none

private meta def try_subsume_core : list literal → list literal → tactic unit
| [] _ := skip
| (head :: small) large := first $
  large.zip_with_index.map $ λ j, do
    unify_lit head j.1,
    try_subsume_core small (large.remove_nth j.2)

private meta def try_subsume (small large : clause) : tactic unit := do
guard $
  (small.literals.filter (λ l : literal, l.is_pos)).length ≤
  (large.literals.filter (λ l : literal, l.is_pos)).length,
guard $
  (small.literals.filter (λ l : literal, l.is_neg)).length ≤
  (large.literals.filter (λ l : literal, l.is_neg)).length,
let large0 := large,
large ← large.with_locals_unsafe,
try_subsume_core small.literals large.literals,
small_mvars ← small.prf.sorted_mvars,
large_mvars ← large0.prf.sorted_mvars,
small_mvars.mmap' $ λ sm, first $
  do lm ← large_mvars, pure $ unify sm lm transparency.reducible

meta def does_subsume_pure (s : tactic_state) (small large : clause) : bool :=
match try_subsume small large s with
| result.success _ _ := tt
| result.exception _ _ _ := ff
end

meta def does_subsume (small large : clause) : tactic bool :=
do s ← read, pure $ does_subsume_pure s small large

end super
