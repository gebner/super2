import super.lpo
open tactic expr super

example (x : ℕ) : true := by do
x ← get_local `x,
let gt := mk_lpo [``eq,
  x.local_uniq_name, ``has_add.add, ``has_zero.zero],
let d (x y : pexpr) := (do
  x ← to_expr x,
  y ← to_expr y,
  trace (x,y,gt x y)),
d ```(x + x) ```(x),
d ```(x + 0) ```(x),
d ```(x) ```(x + 0),
d ```(x = x + 0) ```(x + 0 = x),
m ← mk_meta_var `(ℕ),
d ```(%%m + 0 = %%m) ```(%%m = %%m + 0),
d ```(%%m + 0) ```(%%m),
unify m `(0),
triv
