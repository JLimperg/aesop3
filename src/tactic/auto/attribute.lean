/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.auto.rule
import data.int.basic

namespace tactic
namespace auto

open lean.parser

@[user_attribute]
meta def attr : user_attribute name_set percent :=
{ name := `auto,
  descr := "Registers a definition as a rule for the auto tactic.",
  cache_cfg := {
    mk_cache := pure ∘ name_set.of_list,
    dependencies := [] },
  parser := percent.parser }

namespace attr

meta def declaration_to_rule (decl : name) (success_probability : percent) :
  tactic ((normalization_rule ⊕ regular_rule) × indexing_mode) := do
  (r, imode) ← rule.apply_const decl success_probability,
  pure (sum.inr r, imode)

-- TODO move somewhere more appropriate
meta def simp_all_with_default_lemmas : tactic unit := do
  s ← simp_lemmas.mk_default,
  simp_all s [] { fail_if_unchanged := ff },
  pure ()

meta def declarations_to_rule_set (decls : name_set) : tactic rule_set := do
  regular_rules ← decls.to_list.mmap $ λ decl, do {
    success_probability ← attr.get_param decl,
    declaration_to_rule decl success_probability },
  let simp_rule : normalization_rule :=
    { penalty := 0,
      tac := simp_all_with_default_lemmas,
      description := "simp at *" },
  let normalization_rules :
    list ((normalization_rule ⊕ regular_rule) × indexing_mode) :=
    [(sum.inl simp_rule, indexing_mode.unindexed)],
  pure $ rule_set.from_list $ regular_rules ++ normalization_rules

meta def registered_rule_set : tactic rule_set :=
attr.get_cache >>= declarations_to_rule_set

end attr
end auto
end tactic
