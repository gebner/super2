import super.prover_state super.inferences.clausify

namespace super

meta def simplification.empty_clause : simplification_rule | c :=
if c.ty.literals ≠ [] then pure (some c) else do
c ← c.pack,
c ← c.unpack_quantified,
some <$> clause.check_result_if_debug (pure c)

meta def preprocessing.empty_clause : preprocessing_rule | cs :=
simplification.empty_clause.as_preprocessing_rule cs >>=
  preprocessing.clausify

end super
