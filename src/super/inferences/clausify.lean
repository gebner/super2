import super.prover_state super.cnf

namespace super

meta def clausify1 (c : clause) : prover (list clause) := do
cs ← c.clausify,
clause.check_results_if_debug $
  cs.mmap (λ c, c.clone)

meta def preprocessing.clausify : preprocessing_rule | cs :=
list.join <$> cs.mmap (λ c : clause,
  if c.is_clausified then pure [c] else clausify1 c)

end super
