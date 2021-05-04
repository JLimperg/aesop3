/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import data.int.basic
import tactic.aesop.percent
import tactic.aesop.rule
import tactic.aesop.rule_builder
import tactic.aesop.util

namespace tactic
namespace aesop

open lean
open lean.parser
open interactive (with_desc)
open interactive.types (list_of)

@[derive has_reflect]
structure normalization_rule_config :=
(penalty : option ℤ)

namespace normalization_rule_config

meta def parser : lean.parser normalization_rule_config := do
  penalty ← optional small_int,
  pure ⟨penalty⟩

end normalization_rule_config

meta def normalization_declaration_to_rule (decl : name) (c : normalization_rule_config) :
  tactic rule_set_member := do
  env ← get_env,
  d ← env.get decl,
  r ← rule_builder.normalization_default d,
  match r with
  | rule_builder_output.rule r imode :=
    pure $ rule_set_member.normalization_rule
      { penalty := c.penalty.get_or_else 0, ..r }
      imode
  | rule_builder_output.simp_lemmas s := do
    when c.penalty.is_some $ fail!
      "Penalty annotation is not allowed for norm equations (only for norm tactics).",
    pure $ rule_set_member.normalization_simp_lemmas s
  end

@[derive has_reflect]
meta structure safe_rule_config :=
(penalty : option ℤ)
(safety : option safety)

namespace safe_rule_config

meta def parser : lean.parser safe_rule_config := do
  penalty ← optional small_int,
  safety ← optional safety.parser,
  pure { penalty := penalty, safety := safety }

end safe_rule_config

meta def safe_declaration_to_rule (decl : name) (c : safe_rule_config) :
  tactic rule_set_member := do
  env ← get_env,
  d ← env.get decl,
  let penalty := c.penalty.get_or_else 0,
  let safety := c.safety.get_or_else safety.safe,
  r ← rule_builder.safe_default d,
  match r with
  | rule_builder_output.rule r imode :=
    pure $ rule_set_member.safe_rule
      { penalty := penalty,
        safety := safety,
        ..r }
      imode
  | rule_builder_output.simp_lemmas _ :=
    fail! "aesop/safe_declaration_to_rule: internal error: unexpected rule builder output"
  end

@[derive has_reflect]
structure unsafe_rule_config :=
(success_probability : percent)

namespace unsafe_rule_config

meta def parser : lean.parser unsafe_rule_config := do
  success_probability ← percent.parser,
  pure ⟨success_probability⟩

end unsafe_rule_config

meta def unsafe_declaration_to_rule (decl : name) (c : unsafe_rule_config) :
  tactic rule_set_member := do
  env ← get_env,
  d ← env.get decl,
  r ← rule_builder.unsafe_default d,
  match r with
  | rule_builder_output.rule r imode :=
    pure $ rule_set_member.unsafe_rule
      { success_probability := c.success_probability, ..r }
      imode
  | rule_builder_output.simp_lemmas _ :=
    fail! "aesop/unsafe_declaration_to_rule: internal error: unexpected rule builder output"
  end

/-! ## Attribute -/

@[derive has_reflect]
meta inductive rule_config : Type
| normalization (c : normalization_rule_config)
| unsafe (c : unsafe_rule_config)
| safe (c : safe_rule_config)

meta def declaration_to_rule (decl : name) :
  rule_config → tactic rule_set_member
| (rule_config.normalization c) := normalization_declaration_to_rule decl c
| (rule_config.unsafe c) := unsafe_declaration_to_rule decl c
| (rule_config.safe c) := safe_declaration_to_rule decl c

meta def declarations_to_rule_set (decls : list (name × rule_config)) :
  tactic rule_set := do
  rs ← rule_set.from_list <$> decls.mmap (function.uncurry declaration_to_rule),
  default_simp_lemmas ← simp_lemmas.mk_default,
  let rs :=
    { normalization_simp_lemmas :=
        rs.normalization_simp_lemmas.join default_simp_lemmas,
      ..rs },
  pure rs

meta def attr_config_parser : lean.parser rule_config := do
  rule_type ← optional ident,
  match rule_type with
  | some `norm := rule_config.normalization <$> normalization_rule_config.parser
  | some `safe := rule_config.safe <$> safe_rule_config.parser
  | none := rule_config.unsafe <$> unsafe_rule_config.parser
  | some n := fail $ format! "Unknown aesop attribute type: {n}"
  end

@[user_attribute]
meta def attr : user_attribute name_set rule_config :=
{ name := `aesop,
  descr := "Registers a definition as a rule for the aesop tactic.",
  cache_cfg := {
    mk_cache := pure ∘ name_set.of_list,
    dependencies := [] },
  parser := attr_config_parser }

meta def attr_declarations_to_rule_set (decls : name_set) : tactic rule_set := do
  rs ← decls.to_list.mmap $ λ decl, do {
    config ← attr.get_param decl,
    pure (decl, config) },
  declarations_to_rule_set rs

meta def registered_rule_set : tactic rule_set :=
attr.get_cache >>= attr_declarations_to_rule_set

/-! ## Tactic Configuration -/

@[derive has_reflect]
meta inductive config_clause
| additional_rules (rs : list (name × rule_config))

namespace config_clause

meta def rule_parser {α} (p : lean.parser α) : lean.parser (name × α) :=
prod.mk <$> ident <*> p

meta def rules_parser {α} (p : lean.parser α) : lean.parser (list (name × α)) :=
list_of (rule_parser p)

meta def parser : lean.parser config_clause :=
interactive.with_desc
  "(unsafe_rules: [id probability, ...] | safe_rules: [id penalty, ...] | norm_rules: [id penalty, ...])" $ do
  type ← ident,
  tk ":",
  match type with
  | `unsafe_rules :=
    additional_rules <$>
      rules_parser (rule_config.unsafe <$> unsafe_rule_config.parser)
  | `safe_rules :=
    additional_rules <$>
      rules_parser (rule_config.safe <$> safe_rule_config.parser)
  | `norm_rules :=
    additional_rules <$>
      rules_parser (rule_config.normalization <$> normalization_rule_config.parser)
  | _ :=
    fail $ format! "Unknown Aesop clause: {type}"
  end

end config_clause

@[derive has_reflect]
meta structure config :=
(additional_rules : list (name × rule_config))

namespace config

meta def empty : config :=
{ additional_rules := [] }

meta def add_clause (conf : config) : config_clause → config
| (config_clause.additional_rules rs) :=
  { additional_rules := conf.additional_rules ++ rs ..conf }

meta def of_config_clauses (clauses : list config_clause) : config :=
clauses.foldl add_clause empty

meta def parser : lean.parser config :=
of_config_clauses <$> sep_by (tk ",") config_clause.parser

meta def rule_set (conf : config) : tactic rule_set := do
  default_rules ← registered_rule_set,
  additional_rules ← declarations_to_rule_set conf.additional_rules,
  pure $ default_rules.merge additional_rules

end config

end aesop
end tactic
