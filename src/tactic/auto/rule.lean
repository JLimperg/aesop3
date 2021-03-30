/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.auto.util

/-!
## Rules
-/

namespace tactic
namespace auto

meta structure rule :=
(penalty : ℕ)
(tac : tactic unit)
(description : format)

namespace rule

protected meta def to_fmt (r : rule) : format :=
format.sbracket (_root_.to_fmt r.penalty) ++ format.space ++ r.description

meta instance : has_to_format rule :=
⟨rule.to_fmt⟩

meta def make_apply (e : expr) (penalty : ℕ) : tactic rule :=
pure
  { tac := apply e >> skip,
    penalty := penalty,
    description := format! "apply {e}" }

meta def make_const_apply (n : name) (penalty : ℕ) : tactic rule := do
  n ← resolve_constant n,
  pure
    { tac := mk_const n >>= apply >> skip,
      penalty := penalty,
      description := format! "apply {n}" }

protected meta def lt (r s : rule) : bool :=
r.penalty < s.penalty

end rule

/-!
## Rule Set
-/

meta structure rule_set :=
(rules : list rule)

namespace rule_set

protected meta def to_fmt (rs : rule_set) : format :=
format.unlines $ rs.rules.map rule.to_fmt

meta instance : has_to_format rule_set :=
⟨rule_set.to_fmt⟩

meta def empty : rule_set :=
⟨[]⟩

meta def add (r : rule) (rs : rule_set) : rule_set :=
⟨r :: rs.rules⟩

meta def mfold {α} (rs : rule_set) (init : α) (f : α → rule → tactic α) : tactic α :=
rs.rules.mfoldl f init

meta def first {α} (rs : rule_set) (f : rule → tactic α) : tactic α :=
rs.rules.mfirst f

meta def merge (rs₁ rs₂ : rule_set) : rule_set :=
⟨rs₁.rules ++ rs₂.rules⟩

meta def from_list (rs : list rule) : rule_set :=
⟨rs⟩

meta def applicable_rules (rs : rule_set) : tactic (list rule) :=
pure rs.rules

end rule_set

end auto
end tactic
