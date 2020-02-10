/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

-- Polytime version of lexicographic path order as described in:
-- Things to know when implementing LPO, Bernd Löchner, ESFOR 2004
import super.utils

namespace super
open expr decidable monad native

def lex {T} [decidable_eq T] (gt : T → T → bool) : list T → list T → bool
| (s::ss) (t::ts) := if s = t then lex ss ts else gt s t
| _ _ := ff

def majo {T} (gt : T → T → bool) (s : T) : list T → bool
| [] := tt
| (t::ts) := gt s t && majo ts

meta def alpha (lpo : expr → expr → bool) : list expr → expr → bool
| [] _ := ff
| (s::ss) t := (s = t) || lpo s t || alpha ss t

meta def lex_ma (lpo : expr → expr → bool) (s t : expr) : list expr → list expr → bool
| (si::ss) (ti::ts) :=
  if si = ti then lex_ma ss ts
  else if lpo si ti then majo lpo s ts
  else alpha lpo (si::ss) t
| _ _ := ff

meta def lpo (prec_gt : expr → expr → bool) : expr → expr → bool | s t :=
if prec_gt (get_app_fn s) (get_app_fn t) then majo lpo s (get_app_args t)
else if get_app_fn s = get_app_fn t then
  lex_ma lpo s t (get_app_args s).reverse (get_app_args t).reverse
else alpha lpo (get_app_args s) t

meta def name_of_funsym : expr → name
| (local_const uniq _ _ _) := uniq
| (const n _) := n
| _ := name.anonymous

private meta def contained_funsyms' : expr → name_set → name_set
| (var _) m := m
| (sort _) m := m
| (const n ls) m := m.insert n
| (mvar _ _ t) m := contained_funsyms' t m
| (local_const uniq pp bi t) m := m.insert uniq
| (app a b) m := contained_funsyms' a (contained_funsyms' b m)
| (lam _ _ d b) m := contained_funsyms' d (contained_funsyms' b m)
| (pi _ _ d b) m := contained_funsyms' d (contained_funsyms' b m)
| (elet _ t v b) m := contained_funsyms' t (contained_funsyms' v (contained_funsyms' b m))
| (macro _ _) m := m

meta def contained_funsyms (e : expr) : name_set :=
contained_funsyms' e mk_name_set

meta def prec_gt_of_name_list (ns : list name) : expr → expr → bool :=
let nis := rb_map.of_list ns.zip_with_index in
λ s t, match (nis.find (name_of_funsym s), nis.find (name_of_funsym t)) with
| (some si, some ti) := si > ti
| _ := ff
end

meta def mk_lpo (ns : list name) : expr → expr → bool :=
let prec_gt := prec_gt_of_name_list ns in
lpo (prec_gt_of_name_list ns)

end super
