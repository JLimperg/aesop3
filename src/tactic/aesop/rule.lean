/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import data.int.basic
import data.list.sort
import tactic.aesop.util
import tactic.aesop.percent
import tactic.core

variables {α : Type}

/-!
## Rules
-/

namespace tactic
namespace aesop

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

protected meta def to_fmt (r : normalization_rule) : format :=
format! "[{r.penalty}] {r.to_rule}"

meta instance : has_to_format normalization_rule :=
⟨normalization_rule.to_fmt⟩

protected meta def lt (r s : normalization_rule) : Prop :=
r.penalty < s.penalty

meta instance : has_lt normalization_rule :=
⟨normalization_rule.lt⟩

meta instance :
  decidable_rel ((<) : normalization_rule → normalization_rule → Prop) :=
λ r s, (infer_instance : decidable (r.penalty < s.penalty))

protected meta def ltb (r s : normalization_rule) : bool :=
r < s

end normalization_rule

@[derive has_reflect, derive decidable_eq]
inductive safety
| safe
| almost_safe

namespace safety

protected meta def to_fmt : safety → format
| safe := "safe"
| almost_safe := "almost_safe"

meta instance : has_to_format safety :=
⟨safety.to_fmt⟩

protected meta def parser : lean.parser safety :=
interactive.with_desc "safe | almost_safe" $ do
  i ← lean.parser.ident,
  match i with
  | `safe := pure safe
  | `almost_safe := pure almost_safe
  | _ := failed
  end

end safety

meta structure safe_rule extends rule :=
(penalty : ℤ)
(safety : safety)

namespace safe_rule

protected meta def to_fmt (r : safe_rule) : format :=
format! "[{r.penalty}] {r.to_rule}"

meta instance : has_to_format safe_rule :=
⟨safe_rule.to_fmt⟩

protected meta def lt (r s : safe_rule) : Prop :=
r.penalty < s.penalty

meta instance : has_lt safe_rule :=
⟨safe_rule.lt⟩

meta instance :
  decidable_rel ((<) : safe_rule → safe_rule → Prop) :=
λ r s, (infer_instance : decidable (r.penalty < s.penalty))

protected meta def ltb (r s : safe_rule) : bool :=
r < s

end safe_rule

meta structure unsafe_rule extends rule :=
(success_probability : percent)

namespace unsafe_rule

protected meta def to_fmt (r : unsafe_rule) : format :=
format! "[{r.success_probability}] {r.to_rule}"

meta instance : has_to_format unsafe_rule :=
⟨unsafe_rule.to_fmt⟩

protected meta def lt (r s : unsafe_rule) : Prop :=
r.success_probability > s.success_probability

meta instance : has_lt unsafe_rule :=
⟨unsafe_rule.lt⟩

meta instance :
  decidable_rel ((<) : unsafe_rule → unsafe_rule → Prop) :=
λ r s, (infer_instance : decidable (r.success_probability > s.success_probability))

protected meta def ltb (r s : unsafe_rule) : bool :=
r < s

end unsafe_rule

meta inductive regular_rule
| safe (r : safe_rule)
| unsafe (r : unsafe_rule)

namespace regular_rule

protected meta def to_fmt : regular_rule → format
| (safe r) := "[safe] " ++ r.to_fmt
| (unsafe r) := "[unsafe] " ++ r.to_fmt

meta instance : has_to_format regular_rule :=
⟨regular_rule.to_fmt⟩

meta def to_rule : regular_rule → rule
| (safe r) := r.to_rule
| (unsafe r) := r.to_rule

meta def success_probability : regular_rule → percent
| (safe r) := ⟨100⟩
| (unsafe r) := r.success_probability

meta def is_safe : regular_rule → bool
| (safe _) := tt
| (unsafe _) := ff

meta def is_unsafe : regular_rule → bool
| (safe _) := ff
| (unsafe _) := tt

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

meta def merge (rs₁ rs₂ : rule_index α) : rule_index α :=
{ by_target_head := rs₁.by_target_head ++ rs₂.by_target_head,
  unindexed := rs₁.unindexed ++ rs₂.unindexed }

meta instance {α} : has_append (rule_index α) :=
⟨merge⟩

meta def from_list (rs : list (α × indexing_mode)) : rule_index α :=
rs.foldl (λ rs ⟨r, imode⟩, rs.add r imode) empty

meta def applicable_target_head_indexed_rules (rs : rule_index α) :
  tactic (list α) := do
  tgt ← target,
  let head := tgt.get_app_fn,
  if ¬ head.is_constant
    then pure []
    else pure $ rs.by_target_head.find head.const_name

meta def applicable_rules (lt : α → α → bool) (rs : rule_index α) :
  tactic (list α) := do
  rs₁ ← applicable_target_head_indexed_rules rs,
  let rs₂ := rs.unindexed,
  pure $ (rs₁ ++ rs₂).qsort lt

end rule_index

/-! ## Rule Set Members -/

meta inductive rule_set_member
| normalization_rule (r : normalization_rule) (imode : indexing_mode)
| normalization_simp_lemmas (s : simp_lemmas)
| unsafe_rule (r : unsafe_rule) (imode : indexing_mode)
| safe_rule (r : safe_rule) (imode : indexing_mode)

/-! ## The Rule Set -/

meta structure rule_set :=
(normalization_rules : rule_index normalization_rule)
(normalization_simp_lemmas : simp_lemmas)
(unsafe_rules : rule_index unsafe_rule)
(safe_rules : rule_index safe_rule)

namespace rule_set

protected meta def to_tactic_format (rs : rule_set) : tactic format := do
  simp_lemmas_fmt ← pp rs.normalization_simp_lemmas,
  pure $ format.unlines
    [ format! "normalization rules:{format.nested 2 $ rs.normalization_rules.to_fmt}",
      format! "normalization simp lemmas:{format.nested 2 simp_lemmas_fmt}",
      format! "safe rules:{format.nested 2 $ rs.safe_rules.to_fmt}",
      format! "unsafe rules:{format.nested 2 $ rs.unsafe_rules.to_fmt}" ]

meta instance : has_to_tactic_format rule_set :=
⟨rule_set.to_tactic_format⟩

meta def empty : rule_set :=
{ normalization_rules := rule_index.empty,
  normalization_simp_lemmas := simp_lemmas.mk,
  unsafe_rules := rule_index.empty,
  safe_rules := rule_index.empty }

meta def add_normalization_rule (r : normalization_rule) (imode : indexing_mode)
  (rs : rule_set) : rule_set :=
{ normalization_rules := rs.normalization_rules.add r imode, ..rs }

meta def add_normalization_simp_lemmas (s : simp_lemmas) (rs : rule_set) :
  rule_set :=
{ normalization_simp_lemmas := rs.normalization_simp_lemmas.join s, ..rs }

meta def add_unsafe_rule (r : unsafe_rule) (imode : indexing_mode)
  (rs : rule_set) : rule_set :=
{ unsafe_rules := rs.unsafe_rules.add r imode, ..rs }

meta def add_safe_rule (r : safe_rule) (imode : indexing_mode) (rs : rule_set) :
  rule_set :=
{ safe_rules := rs.safe_rules.add r imode, ..rs }

meta def add_rule_set_member : rule_set_member → rule_set → rule_set
| (rule_set_member.normalization_rule r imode) rs :=
  rs.add_normalization_rule r imode
| (rule_set_member.normalization_simp_lemmas s) rs :=
  rs.add_normalization_simp_lemmas s
| (rule_set_member.unsafe_rule r imode) rs :=
  rs.add_unsafe_rule r imode
| (rule_set_member.safe_rule r imode) rs :=
  rs.add_safe_rule r imode

meta def merge (rs₁ rs₂ : rule_set) : rule_set :=
{ unsafe_rules := rs₁.unsafe_rules ++ rs₂.unsafe_rules,
  normalization_rules := rs₁.normalization_rules ++ rs₂.normalization_rules,
  normalization_simp_lemmas :=
    rs₁.normalization_simp_lemmas.join rs₂.normalization_simp_lemmas,
  safe_rules := rs₁.safe_rules ++ rs₂.safe_rules }

meta instance : has_append rule_set :=
⟨merge⟩

meta def from_list (rs : list rule_set_member) : rule_set :=
rs.foldl (λ rs r, rs.add_rule_set_member r) empty

meta def applicable_normalization_rules (rs : rule_set) :
  tactic (list normalization_rule) :=
rs.normalization_rules.applicable_rules normalization_rule.ltb

meta def applicable_unsafe_rules (rs : rule_set) : tactic (list unsafe_rule) :=
rs.unsafe_rules.applicable_rules unsafe_rule.ltb

meta def applicable_safe_rules (rs : rule_set) : tactic (list safe_rule) :=
rs.safe_rules.applicable_rules safe_rule.ltb

end rule_set
end aesop
end tactic
