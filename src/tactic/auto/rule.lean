/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import data.int.basic
import tactic.auto.util
import tactic.auto.percent
import tactic.core

variables {α : Type}

/-!
## Rules
-/

namespace tactic
namespace auto

open native

/-! ## Rule Indexing Modes -/

meta inductive indexing_mode : Type
| unindexed
| index_target_head (hd : name)

export indexing_mode (unindexed index_target_head)

/-! ## Rules -/

meta structure rule (α : Type) :=
(penalty : α)
(tac : tactic unit)
(description : format)

namespace rule

private meta def int_to_format (n : int) : format :=
to_string n

protected meta def to_fmt [has_to_format α] (r : rule α) : format :=
format! "[{r.penalty}] {r.description}"

meta instance [has_to_format α] : has_to_format (rule α) :=
⟨rule.to_fmt⟩

protected meta def lt [has_lt α] (r s : rule α) : Prop :=
r.penalty < s.penalty

meta instance [has_lt α] : has_lt (rule α) :=
⟨rule.lt⟩

meta instance [has_lt α] [decidable_rel ((<) : α → α → Prop)] :
  decidable_rel ((<) : rule α → rule α → Prop) :=
λ r s, (infer_instance : decidable (r.penalty < s.penalty))

end rule

@[reducible] meta def normalization_rule := rule ℤ

@[reducible] meta def regular_rule := rule percent

/-! ## Rule Indices -/

meta structure rule_index (α : Type) :=
(by_target_head : rb_lmap name (rule α))
(unindexed : list (rule α))

namespace rule_index

protected meta def to_fmt [has_to_format α] (rs : rule_index α) : format :=
format.join
  [ "rules indexed by target head:",
    format.nested 2 $ format.unlines $ rs.by_target_head.to_list.map $
      λ ⟨hd, rules⟩,
        let rules := format.unlines $ rules.map _root_.to_fmt in
        format! "{hd}:{format.nested 2 rules}",
    "unindexed rules:",
    format.nested 2 $ format.unlines $ rs.unindexed.map _root_.to_fmt ]

meta instance [has_to_format α] : has_to_format (rule_index α) :=
⟨rule_index.to_fmt⟩

meta def empty : rule_index α :=
⟨rb_lmap.mk _ _, []⟩

meta def add (r : rule α) : indexing_mode → rule_index α → rule_index α
| (index_target_head hd) rs :=
  { by_target_head := rs.by_target_head.insert hd r, ..rs }
| unindexed rs :=
  { unindexed := r :: rs.unindexed, ..rs }

meta def from_list (rs : list (rule α × indexing_mode)) : rule_index α :=
rs.foldl (λ rs ⟨r, imode⟩, rs.add r imode) empty

meta def applicable_target_head_indexed_rules (rs : rule_index α) :
  tactic (list (rule α)) := do
  tgt ← target >>= whnf, -- TODO same question as above: do we want to WHNF here?
  let head := tgt.get_app_fn,
  if ¬ head.is_constant
    then pure []
    else pure $ rs.by_target_head.find head.const_name

meta def applicable_rules (rs : rule_index α) : tactic (list (rule α)) := do
  rs₁ ← applicable_target_head_indexed_rules rs,
  let rs₂ := rs.unindexed,
  pure $ rs₁ ++ rs₂

end rule_index

/-! ## The Rule Set -/

meta structure rule_set :=
(normalization_rules : rule_index ℤ)
(regular_rules : rule_index percent)

namespace rule_set

protected meta def to_fmt (rs : rule_set) : format :=
format.join
  [ "normalization rules:",
    format.nested 2 $ rs.normalization_rules.to_fmt,
    format.line,
    "regular rules:",
    format.nested 2 $ rs.regular_rules.to_fmt ]

meta instance : has_to_format rule_set :=
⟨rule_set.to_fmt⟩

meta def empty : rule_set :=
{ normalization_rules := rule_index.empty,
  regular_rules := rule_index.empty }

meta def add_normalization_rule (r : normalization_rule) (imode : indexing_mode)
  (rs : rule_set) : rule_set :=
{ normalization_rules := rs.normalization_rules.add r imode, ..rs }

meta def add_regular_rule (r : regular_rule) (imode : indexing_mode)
  (rs : rule_set) : rule_set :=
{ regular_rules := rs.regular_rules.add r imode, ..rs }

meta def from_list
  (rs : list ((normalization_rule ⊕ regular_rule) × indexing_mode)) : rule_set :=
rs.foldl
  (λ rs ⟨r, imode⟩,
    match r with
    | sum.inl r := rs.add_normalization_rule r imode
    | sum.inr r := rs.add_regular_rule r imode
    end)
  empty

meta def first_applicable_normalization_rule (rs : rule_set) :
  tactic (option normalization_rule) :=
list.minimum' <$> rs.normalization_rules.applicable_rules
-- TODO more efficient impl: move minimisation into rule_index

meta def applicable_regular_rules (rs : rule_set) : tactic (list regular_rule) :=
rs.regular_rules.applicable_rules

end rule_set

/-! ## Specific Rules -/

namespace rule

/-! ### Apply -/

meta def conclusion_head_constant (e : expr) (md : transparency) :
  tactic (option name) := do
  (_, conclusion) ← open_pis_whnf e md,
  -- TODO Do we actually want to normalise here? Maybe we want to take the type
  -- exactly as the user wrote it (or rather, exactly as Lean elaborated it).
  try_core $ get_app_fn_const_whnf conclusion md

meta def apply_indexing_mode (type : expr) : tactic indexing_mode := do
  head_constant ← conclusion_head_constant type semireducible,
  pure $
    match head_constant with
    | some c := index_target_head c
    | none := unindexed
    end

/- Note: `e` may not be valid for the context in which this rule is going to be
applied. Probably better to take a pexpr here. -/
meta def apply (e : expr) (success_probability : percent) :
  tactic (regular_rule × indexing_mode) := do
  type ← infer_type e,
  imode ← apply_indexing_mode type,
  let r : rule percent :=
    { tac := tactic.apply e >> skip,
      penalty := success_probability,
      description := format! "apply {e}" },
  pure (r, imode)

meta def apply_const (n : name) (success_probability : percent) :
  tactic (regular_rule × indexing_mode) := do
  n ← resolve_constant n,
  env ← get_env,
  d ← env.get n,
  imode ← apply_indexing_mode d.type,
  let r : rule percent :=
    { tac := mk_const n >>= tactic.apply >> skip,
      penalty := success_probability,
      description := format! "apply {n}" },
  pure (r, imode)

end rule
end auto
end tactic
