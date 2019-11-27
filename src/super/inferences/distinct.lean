import super.distinct super.prover_state

namespace super

meta def simplification.distinct : simplification_rule | cls :=
if cls.is_taut then
  pure none
else
  pure $ some cls.distinct

meta def preprocessing.distinct : preprocessing_rule :=
simplification.distinct.as_preprocessing_rule

end super
