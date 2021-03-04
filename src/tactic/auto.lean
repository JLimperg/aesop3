/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.core

/-!
# `auto`, a general-purpose proof search tactic
-/

/-
Initial 'MVP': backtracking depth-first search with a database of backwards
lemmas.

TODO:

- Metavariables need to be reset when we switch between branches of the search
  tree. Currently, mvars may leak freely between branches. Maybe the best
  solution here is to disallow proof rules from introducing new metas, except
  for those which represent goals. auto could check this at runtime, or elide
  the check for efficiency unless a 'debug mode' is toggled.
- Search tree representation. Currently, the search tree is entirely implicit.
  If we want best-first or breadth-first search, we instead need to represent
  the search tree explicitly. Goals can be represented by metas, per usual. But
  what about the mvar context?
- Rule indexing. Currently, we iterate through the list of rules one-by-one,
  which is a tiny bit inefficient.
-/

namespace tactic
namespace auto

open expr
open tactic.unsafe

/-!
## Utility stuff
-/

meta def mvar_context (e : expr) : tactic (list expr) :=
local_context.to_list <$> type_context.run type_context.get_local_context

/-!
## Rules
-/

meta structure rule :=
(tac : tactic unit)

namespace rule

meta def make_apply (e : expr) : tactic rule :=
pure { tac := trace! "apply {e}" >> apply e >> pure () }

meta def make_const_apply (n : name) : tactic rule :=
pure { tac := trace! "apply {n}" >> mk_const n >>= apply >> pure () }

meta def apply (r : rule) : tactic unit := do
  trace "---",
  trace_state,
  r ← try_core r.tac,
  match r with
  | none := trace "(failed)" >> failed
  | (some _) := trace_state
  end
end rule

/-!
## Rule Set
-/

meta structure rule_set :=
(rules : list rule)

namespace rule_set

meta def empty : rule_set :=
⟨[]⟩

meta def add (r : rule) (rs : rule_set) : rule_set :=
⟨r :: rs.rules⟩

meta def fold {α} (rs : rule_set) (init : α) (f : α → rule → tactic α) : tactic α :=
rs.rules.mfoldl f init

meta def first {α} (rs : rule_set) (f : rule → tactic α) : tactic α :=
rs.rules.mfirst f

meta def merge (rs₁ rs₂ : rule_set) : rule_set :=
⟨rs₁.rules ++ rs₂.rules⟩

meta def from_list (rs : list rule) : rule_set :=
⟨rs⟩

end rule_set

/-!
## Attribute
-/

namespace attr

meta def declaration_to_rule (decl : name) : tactic rule :=
rule.make_const_apply decl

@[user_attribute]
meta def attr : user_attribute rule_set unit :=
{ name := `auto,
  descr := "Registers a definition as a rule for the auto tactic.",
  cache_cfg := {
    mk_cache := λ decls, rule_set.from_list <$> decls.mmap declaration_to_rule,
    dependencies := []
  },
}

end attr

/-!
## Search
-/

meta def dfs (rs : rule_set) : tactic unit := do
  attr_rules ← attr.attr.get_cache,
  let rs := rs.merge attr_rules,
  trace "===",
  trace_state,
  focus1 $ rs.first $ λ rule, do
    rule.apply,
    all_goals' dfs

end auto
end tactic

/-!
## Tests
-/

open tactic.auto

inductive Even : ℕ → Prop
| zero : Even 0
| plus_two {n} : Even n → Even (n + 2)

attribute [auto] Even.zero Even.plus_two

example : Even 6 := by dfs rule_set.empty
