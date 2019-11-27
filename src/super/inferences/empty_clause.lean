import super.prover_state super.inferences.clausify

namespace super

meta def simplification.empty_clause : simplification_rule | c :=
if c.ty.literals ≠ [] then pure (some c) else do
c ← c.pack,
some <$> c.unpack_quantified

meta def preprocessing.empty_clause : preprocessing_rule :=
simplification.empty_clause.as_preprocessing_rule

end super
