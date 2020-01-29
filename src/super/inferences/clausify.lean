import super.prover_state super.cnf

namespace super

meta def preprocessing.clausify : preprocessing_rule | cs :=
list.join <$> cs.mmap (λ c : clause, do
  cs ← c.clausify,
  if cs.length > 1 then
    cs.mmap $ λ c, c.clone
  else
    pure cs)

end super
