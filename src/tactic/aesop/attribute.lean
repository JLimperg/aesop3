/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.aesop.rule
import data.int.basic

namespace tactic
namespace aesop

open lean
open lean.parser

@[derive has_reflect]
structure normalization_attr_config :=
(penalty : option ℤ)

namespace normalization_attr_config

meta def parser : lean.parser normalization_attr_config := do
  penalty ← optional small_int,
  pure ⟨penalty⟩

end normalization_attr_config

@[derive has_reflect]
structure regular_attr_config :=
(success_probability : percent)

namespace regular_attr_config

meta def parser : lean.parser regular_attr_config := do
  success_probability ← percent.parser,
  pure ⟨success_probability⟩

end regular_attr_config

@[derive has_reflect]
meta inductive attr_config : Type
| normalization (c : normalization_attr_config) : attr_config
| regular (c : regular_attr_config) : attr_config

namespace attr_config

meta def parser : lean.parser attr_config := do
  rule_type ← optional ident,
  match rule_type with
  | some `norm := normalization <$> normalization_attr_config.parser
  | none := regular <$> regular_attr_config.parser
  | some n := fail $ format! "Unknown aesop attribute type: {n}"
  end

end attr_config

@[user_attribute]
meta def attr : user_attribute name_set attr_config :=
{ name := `aesop,
  descr := "Registers a definition as a rule for the aesop tactic.",
  cache_cfg := {
    mk_cache := pure ∘ name_set.of_list,
    dependencies := [] },
  parser := attr_config.parser }

namespace attr

meta def normalization_declaration_to_rule (decl : name) (c : normalization_attr_config) :
  tactic rule_set_member := do
  env ← get_env,
  d ← env.get decl,
  match d.type with
  | `(tactic unit) := do
    tac ← eval_expr (tactic unit) d.value,
    pure $ rule_set_member.normalization_rule
      { tac := tac,
        description := decl.to_string,
        penalty := c.penalty.get_or_else 1 }
      indexing_mode.unindexed
  | _ := do
    s ← simp_lemmas.mk.add_simp decl <|> fail!
      "Cannot add {decl} as a norm rule for aesop. It must be a (conditional) equation or a tactic.",
    when c.penalty.is_some $ fail!
      "Penalty annotation is not allowed for aesop norm equations (only for norm tactics).",
    pure $ rule_set_member.normalization_simp_lemmas s
  end

meta def regular_declaration_to_rule (decl : name) (c : regular_attr_config) :
  tactic rule_set_member := do
  env ← get_env,
  d ← env.get decl,
  match d.type with
  | `(tactic unit) := do
    tac ← eval_expr (tactic unit) d.value,
    pure $ rule_set_member.regular_rule
      { tac := tac,
        description := decl.to_string,
        success_probability := c.success_probability }
      indexing_mode.unindexed
  | _ := do
    (r, imode) ← rule.apply_const decl c.success_probability,
    pure $ rule_set_member.regular_rule r imode
  end

meta def declaration_to_rule (decl : name) :
  attr_config → tactic rule_set_member
| (attr_config.normalization c) := normalization_declaration_to_rule decl c
| (attr_config.regular c) := regular_declaration_to_rule decl c

meta def declarations_to_rule_set (decls : name_set) : tactic rule_set := do
  rs ← decls.to_list.mmap $ λ decl, do {
    success_probability ← attr.get_param decl,
    declaration_to_rule decl success_probability },
  let rs := rule_set.from_list rs,
  default_simp_lemmas ← simp_lemmas.mk_default,
  let rs :=
    { normalization_simp_lemmas :=
        rs.normalization_simp_lemmas.join default_simp_lemmas,
      ..rs },
  pure rs

meta def registered_rule_set : tactic rule_set :=
attr.get_cache >>= declarations_to_rule_set

end attr
end aesop
end tactic
