/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.auto.util
import tactic.core

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
(penalty : ℤ)
(tac : tactic unit)
(description : format)

namespace rule

private meta def int_to_format (n : int) : format :=
to_string n

protected meta def to_fmt (r : rule) : format :=
format! "[{int_to_format r.penalty}] {r.description}"

meta instance : has_to_format rule :=
⟨rule.to_fmt⟩

protected meta def lt (r s : rule) : bool :=
r.penalty < s.penalty

meta instance : has_lt rule :=
⟨λ r s, rule.lt r s = true⟩

end rule

/-! ## Rule Types -/

/-
- Normalization rules are applied first and may generate only one subgoal. They
  are applied without backtracking, so if multiple rules are applicable, the
  lowest-penalty one is applied without considering the others.
  TODO maybe apply them in a fixed-point loop?
- Regular rules are applied once no normalisation rules are applicable anymore,
  with backtracking.
-/
meta inductive rule_type
| normalization
| regular

/-! ## Rule Indices -/

meta structure rule_index :=
(by_target_head : rb_lmap name rule)
(unindexed : list rule)

namespace rule_index

protected meta def to_fmt (rs : rule_index) : format :=
format.join
  [ "rules indexed by target head:",
    format.nested 2 $ format.unlines $ rs.by_target_head.to_list.map $
      λ ⟨hd, rules⟩,
        let rules := format.unlines $ rules.map _root_.to_fmt in
        format! "{hd}:{format.nested 2 rules}",
    "unindexed rules:",
    format.nested 2 $ format.unlines $ rs.unindexed.map _root_.to_fmt ]

meta instance : has_to_format rule_index :=
⟨rule_index.to_fmt⟩

meta def empty : rule_index :=
⟨rb_lmap.mk _ _, []⟩

meta def add (r : rule) : indexing_mode → rule_index → rule_index
| (index_target_head hd) rs :=
  { by_target_head := rs.by_target_head.insert hd r, ..rs }
| unindexed rs :=
  { unindexed := r :: rs.unindexed, ..rs }

meta def from_list (rs : list (rule × indexing_mode)) : rule_index :=
rs.foldl (λ rs ⟨r, imode⟩, rs.add r imode) empty

meta def applicable_target_head_indexed_rules (rs : rule_index) :
  tactic (list rule) := do
  tgt ← target >>= whnf, -- TODO same question as above: do we want to WHNF here?
  let head := tgt.get_app_fn,
  if ¬ head.is_constant
    then pure []
    else pure $ rs.by_target_head.find head.const_name

meta def applicable_rules (rs : rule_index) : tactic (list rule) := do
  rs₁ ← applicable_target_head_indexed_rules rs,
  let rs₂ := rs.unindexed,
  pure $ list.join [rs₁, rs₂]

end rule_index

/-! ## The Rule Set -/

meta structure rule_set :=
(normalization_rules : rule_index)
(regular_rules : rule_index)

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

meta def add (r : rule) : rule_type → indexing_mode → rule_set → rule_set
| rule_type.normalization imode rs :=
  { normalization_rules := rs.normalization_rules.add r imode, ..rs }
| rule_type.regular imode rs :=
  { regular_rules := rs.regular_rules.add r imode, ..rs }

meta def from_list (rs : list (rule × rule_type × indexing_mode)) : rule_set :=
rs.foldl (λ rs ⟨r, type, imode⟩, rs.add r type imode) empty

meta def first_applicable_normalization_rule (rs : rule_set) :
  tactic (option rule) :=
list.minimum' <$> rs.normalization_rules.applicable_rules
-- TODO more efficient impl: move minimisation into rule_index

meta def applicable_regular_rules (rs : rule_set) : tactic (list rule) :=
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
applied. -/
meta def apply (e : expr) (penalty : ℤ) : tactic (rule × indexing_mode) := do
  type ← infer_type e,
  imode ← apply_indexing_mode type,
  let r : rule :=
    { tac := tactic.apply e >> skip,
      penalty := penalty,
      description := format! "apply {e}" },
  pure (r, imode)

meta def apply_const (n : name) (penalty : ℤ) : tactic (rule × indexing_mode) := do
  n ← resolve_constant n,
  env ← get_env,
  d ← env.get n,
  imode ← apply_indexing_mode d.type,
  let r : rule :=
    { tac := mk_const n >>= tactic.apply >> skip,
      penalty := penalty,
      description := format! "apply {n}" },
  pure (r, imode)

end rule
end auto
end tactic
