import super.utils

namespace super

def debugging_enabled : bool :=
tt

open tactic
@[inline] def if_debug {α} (debug no_debug : α) :=
by do to_expr ```(if debugging_enabled then debug else no_debug) >>= whnf >>= exact

@[inline] def when_debug {m} [monad m] (tac : m unit) : m unit :=
if_debug tac (pure ())

@[inline] def check_result_when_debug {m} [monad m] {α} (tac : α → m unit) (wrapped : m α) : m α :=
if_debug (do res ← wrapped, monad_lift (tac res), pure res) wrapped

end super
