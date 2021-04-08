/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import data.int.basic
import data.list.sort
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

meta structure rule :=
(tac : tactic unit)
(description : format)

namespace rule

protected meta def to_fmt (r : rule) : format :=
r.description

meta instance : has_to_format rule :=
⟨rule.to_fmt⟩

end rule

meta structure normalization_rule extends rule :=
(penalty : ℤ)

namespace normalization_rule

meta def to_fmt (r : normalization_rule) : format :=
format! "[{r.penalty}] {r.to_rule}"

meta instance : has_to_format normalization_rule :=
⟨normalization_rule.to_fmt⟩

meta def lt (r s : normalization_rule) : Prop :=
r.penalty < s.penalty

meta instance : has_lt normalization_rule :=
⟨normalization_rule.lt⟩

meta instance :
  decidable_rel ((<) : normalization_rule → normalization_rule → Prop) :=
λ r s, (infer_instance : decidable (r.penalty < s.penalty))

end normalization_rule

meta structure regular_rule extends rule :=
(success_probability : percent)

namespace regular_rule

meta def to_fmt (r : regular_rule) : format :=
format! "[{r.success_probability}] {r.to_rule}"

meta instance : has_to_format regular_rule :=
⟨regular_rule.to_fmt⟩

meta def lt (r s : regular_rule) : Prop :=
r.success_probability < s.success_probability

meta instance : has_lt regular_rule :=
⟨regular_rule.lt⟩

meta instance :
  decidable_rel ((<) : regular_rule → regular_rule → Prop) :=
λ r s, (infer_instance : decidable (r.success_probability < s.success_probability))

end regular_rule

/-! ## Rule Indices -/

meta structure rule_index (α : Type) :=
(by_target_head : rb_lmap name α)
(unindexed : list α)

namespace rule_index

protected meta def to_fmt [has_to_format α] (rs : rule_index α) : format :=
format.join
  [ "rules indexed by target head:",
    format.nested 2 $ format.unlines $ rs.by_target_head.to_list.map $
      λ ⟨hd, rules⟩,
        let rules := format.unlines $ rules.map _root_.to_fmt in
        format! "{hd}:{format.nested 2 rules}",
    format.line,
    "unindexed rules:",
    format.nested 2 $ format.unlines $ rs.unindexed.map _root_.to_fmt ]

meta instance [has_to_format α] : has_to_format (rule_index α) :=
⟨rule_index.to_fmt⟩

meta def empty : rule_index α :=
⟨rb_lmap.mk _ _, []⟩

meta def add (r : α) : indexing_mode → rule_index α → rule_index α
| (index_target_head hd) rs :=
  { by_target_head := rs.by_target_head.insert hd r, ..rs }
| unindexed rs :=
  { unindexed := r :: rs.unindexed, ..rs }

meta def from_list (rs : list (α × indexing_mode)) : rule_index α :=
rs.foldl (λ rs ⟨r, imode⟩, rs.add r imode) empty

meta def applicable_target_head_indexed_rules (rs : rule_index α) :
  tactic (list α) := do
  tgt ← target,
  let head := tgt.get_app_fn,
  if ¬ head.is_constant
    then pure []
    else pure $ rs.by_target_head.find head.const_name

meta def applicable_rules [has_lt α] [decidable_rel ((<) : α → α → Prop)]
  (rs : rule_index α) : tactic (list α) := do
  rs₁ ← applicable_target_head_indexed_rules rs,
  let rs₂ := rs.unindexed,
  pure $ (rs₁ ++ rs₂).qsort (λ r s, r < s)

end rule_index

/-! ## Rule Set Members -/

meta inductive rule_set_member
| normalization_rule (r : normalization_rule) (imode : indexing_mode)
| normalization_simp_lemmas (s : simp_lemmas)
| regular_rule (r : regular_rule) (imode : indexing_mode)

/-! ## The Rule Set -/

meta structure rule_set :=
(normalization_rules : rule_index normalization_rule)
(normalization_simp_lemmas : simp_lemmas)
(regular_rules : rule_index regular_rule)

namespace rule_set

protected meta def to_tactic_format (rs : rule_set) : tactic format := do
  simp_lemmas_fmt ← pp rs.normalization_simp_lemmas,
  pure $ format.unlines
    [ format! "normalization rules:{format.nested 2 $ rs.normalization_rules.to_fmt}",
      format! "normalization simp lemmas:{format.nested 2 simp_lemmas_fmt}",
      format! "regular rules:{format.nested 2 $ rs.regular_rules.to_fmt}" ]

meta instance : has_to_tactic_format rule_set :=
⟨rule_set.to_tactic_format⟩

meta def empty : rule_set :=
{ normalization_rules := rule_index.empty,
  normalization_simp_lemmas := simp_lemmas.mk,
  regular_rules := rule_index.empty }

meta def add_normalization_rule (r : normalization_rule) (imode : indexing_mode)
  (rs : rule_set) : rule_set :=
{ normalization_rules := rs.normalization_rules.add r imode, ..rs }

meta def add_normalization_simp_lemmas (s : simp_lemmas) (rs : rule_set) :
  rule_set :=
{ normalization_simp_lemmas := rs.normalization_simp_lemmas.join s, ..rs }

meta def add_regular_rule (r : regular_rule) (imode : indexing_mode)
  (rs : rule_set) : rule_set :=
{ regular_rules := rs.regular_rules.add r imode, ..rs }

meta def add_rule_set_member : rule_set_member → rule_set → rule_set
| (rule_set_member.normalization_rule r imode) rs :=
  rs.add_normalization_rule r imode
| (rule_set_member.normalization_simp_lemmas s) rs :=
  rs.add_normalization_simp_lemmas s
| (rule_set_member.regular_rule r imode) rs :=
  rs.add_regular_rule r imode

meta def from_list (rs : list rule_set_member) : rule_set :=
rs.foldl (λ rs r, rs.add_rule_set_member r) empty

meta def applicable_normalization_rules (rs : rule_set) :
  tactic (list normalization_rule) :=
rs.normalization_rules.applicable_rules

meta def applicable_regular_rules (rs : rule_set) : tactic (list regular_rule) :=
rs.regular_rules.applicable_rules

end rule_set

/-! ## Specific Rules -/

namespace rule

/-! ### Apply -/

meta def conclusion_head_constant (e : expr) :
  tactic (option name) := do
  (_, conclusion) ← open_pis e,
  let f := conclusion.get_app_fn,
  pure $ if f.is_constant then some f.const_name else none

meta def apply_indexing_mode (type : expr) : tactic indexing_mode := do
  head_constant ← conclusion_head_constant type,
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
  let r : regular_rule :=
    { tac := tactic.apply e >> skip,
      success_probability := success_probability,
      description := format! "apply {e}" },
  pure (r, imode)

meta def apply_const (n : name) (success_probability : percent) :
  tactic (regular_rule × indexing_mode) := do
  n ← resolve_constant n,
  env ← get_env,
  d ← env.get n,
  imode ← apply_indexing_mode d.type,
  let r : regular_rule :=
    { tac := mk_const n >>= tactic.apply >> skip,
      success_probability := success_probability,
      description := format! "apply {n}" },
  pure (r, imode)

end rule
end auto
end tactic
