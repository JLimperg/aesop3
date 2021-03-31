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
meta def attr : user_attribute name_set ℤ :=
{ name := `auto,
  descr := "Registers a definition as a rule for the auto tactic.",
  cache_cfg := {
    mk_cache := pure ∘ name_set.of_list,
    dependencies := [] },
  parser := small_int }

namespace attr

meta def declaration_to_rule (decl : name) (penalty : ℤ) :
  tactic (rule × indexing_mode) :=
rule.apply_const decl (priority.regular penalty)

meta def declarations_to_rule_set (decls : name_set) : tactic rule_set :=
rule_set.from_list <$> decls.to_list.mmap (λ decl, do
  penalty ← attr.get_param decl,
  declaration_to_rule decl penalty)

meta def registered_rule_set : tactic rule_set :=
attr.get_cache >>= declarations_to_rule_set

end attr
end auto
end tactic
