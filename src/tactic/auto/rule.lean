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

/-! ## Indexing Modes -/

meta inductive indexing_mode : Type
| unindexed
| index_target_head (hd : name)

export indexing_mode (unindexed index_target_head)

/-! ## Rules -/

meta structure rule :=
(penalty : ℕ)
(tac : tactic unit)
(description : format)

namespace rule

protected meta def to_fmt (r : rule) : format :=
format.sbracket (_root_.to_fmt r.penalty) ++ format.space ++ r.description

meta instance : has_to_format rule :=
⟨rule.to_fmt⟩

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
meta def make_apply (e : expr) (penalty : ℕ) : tactic (rule × indexing_mode) := do
  type ← infer_type e,
  imode ← apply_indexing_mode type,
  let r : rule :=
    { tac := apply e >> skip,
      penalty := penalty,
      description := format! "apply {e}" },
  pure (r, imode)

meta def make_const_apply (n : name) (penalty : ℕ) :
  tactic (rule × indexing_mode) := do
  n ← resolve_constant n,
  env ← get_env,
  d ← env.get n,
  imode ← apply_indexing_mode d.type,
  let r : rule :=
    { tac := mk_const n >>= apply >> skip,
      penalty := penalty,
      description := format! "apply {n}" },
  pure (r, imode)

protected meta def lt (r s : rule) : bool :=
r.penalty < s.penalty

end rule

/-! ## The Rule Set -/

meta structure rule_set :=
(target_head_indexed : rb_lmap name rule)
(unindexed : list rule)

namespace rule_set

protected meta def to_fmt (rs : rule_set) : format :=
format.join
  [ "rules indexed by target head:",
    format.nested 2 $ format.unlines $ rs.target_head_indexed.to_list.map $
      λ (x : name × list rule),
        let hd := x.fst in
        let rules := format.unlines $ x.snd.map _root_.to_fmt in
        format! "{hd}:{format.nested 2 rules}",
    "unindexed rules:",
    format.nested 2 $ format.unlines $ rs.unindexed.map _root_.to_fmt ]

meta instance : has_to_format rule_set :=
⟨rule_set.to_fmt⟩

meta def empty : rule_set :=
⟨rb_lmap.mk _ _, []⟩

meta def add (r : rule) : indexing_mode → rule_set → rule_set
| (index_target_head hd) rs :=
  { target_head_indexed := rs.target_head_indexed.insert hd r, ..rs }
| unindexed rs :=
  { unindexed := r :: rs.unindexed, ..rs }

meta def from_list (rs : list (rule × indexing_mode)) : rule_set :=
rs.foldl (λ rs ⟨r, imode⟩, rs.add r imode) empty

meta def applicable_target_head_indexed_rules (rs : rule_set) :
  tactic (list rule) := do
  tgt ← target >>= whnf,
  let head := tgt.get_app_fn,
  if ¬ head.is_constant
    then pure []
    else pure $ rs.target_head_indexed.find head.const_name

meta def applicable_rules (rs : rule_set) : tactic (list rule) := do
  rs₁ ← applicable_target_head_indexed_rules rs,
  let rs₂ := rs.unindexed,
  pure $ list.join [rs₁, rs₂]

end rule_set

end auto
end tactic
