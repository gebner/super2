import super tactic.core

open tactic expr super

set_option pp.all true
set_option trace.check true
-- set_option trace.type_context.is_def_eq true
-- set_option trace.type_context.is_def_eq_detail true

#eval do
e ← get_env,
e.get_trusted_decls.mmap' $ λ d,
on_exception (trace d.to_name) $ do
(prf, ty) ← decl_mk_const d,
cls ← clause.of_type_and_proof ty prf,
cls.check
