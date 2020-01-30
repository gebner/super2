import super.prover_state super.cnf

namespace super

meta def clause.clausify' (c : clause) : prover (list clause) := do
s ← state_t.get,
(s, cs) ← state_t.lift $ tactic.using_new_ref s (λ r, do
  cs ← c.clausify (λ e, do
    s ← tactic.read_ref r,
    (e', s) ← (intern_sk_term e).run s,
    tactic.write_ref r s,
    pure e'),
  s ← tactic.read_ref r,
  pure (s, cs)),
state_t.put s,
pure cs

meta def preprocessing.clausify : preprocessing_rule | cs :=
list.join <$> cs.mmap (λ c : clause, do
  cs ← c.clausify',
  if cs.length > 1 then
    cs.mmap $ λ c, c.clone
  else
    pure cs)

end super
