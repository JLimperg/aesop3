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
open interactive.types (list_of brackets)

@[derive has_reflect]
inductive builder_clause
| apply
| simp_lemma
| tactic

namespace builder_clause

meta def args_parser : lean.parser builder_clause :=
with_desc "apply | simp_lemma | tactic" $ do
  i ← ident,
  match i with
  | `apply := pure builder_clause.apply
  | `simp_lemma := pure builder_clause.simp_lemma
  | `tactic := pure builder_clause.tactic
  | _ := fail $ format! "Unknown builder: {i}"
  end

meta def to_rule_builder : builder_clause → rule_builder
| apply := rule_builder.apply
| simp_lemma := rule_builder.normalization_simp_lemma
| tactic := rule_builder.tac

end builder_clause

@[derive has_reflect]
structure safety_clause :=
(to_safety : safety)

namespace safety_clause

protected meta def safe_args_parser : lean.parser safety_clause :=
pure ⟨safety.safe⟩

protected meta def almost_safe_args_parser : lean.parser safety_clause :=
pure ⟨safety.almost_safe⟩

end safety_clause

@[derive has_reflect]
inductive rule_clause
| builder (c : builder_clause)
| safety (c : safety_clause)

meta def clause_parser {α}
  (simple_clauses : name_map α)
  (clauses : name_map (lean.parser α)) :
  lean.parser α :=
with_desc "clause" $
(do
  i ← ident,
  match simple_clauses.find i with
  | some v := pure v
  | none := failed
  end)
<|>
(brackets "(" ")" $ do
  i ← ident,
  match clauses.find i with
  | some arg_parser := arg_parser
  | none := fail $ format! "Unknown clause: {i}"
  end)

meta def simple_rule_clauses : name_map rule_clause :=
native.rb_map.of_list
  [ (`safe, rule_clause.safety ⟨safety.safe⟩),
    (`almost_safe, rule_clause.safety ⟨safety.almost_safe⟩) ]

meta def rule_clauses : name_map (lean.parser rule_clause) :=
native.rb_map.of_list
  [ (`builder, rule_clause.builder <$> builder_clause.args_parser),
    (`safe, rule_clause.safety <$> safety_clause.safe_args_parser),
    (`almost_safe, rule_clause.safety <$> safety_clause.almost_safe_args_parser) ]

namespace rule_clause

meta def parser : lean.parser rule_clause :=
clause_parser simple_rule_clauses rule_clauses

end rule_clause

@[derive has_reflect]
structure normalization_rule_config :=
(penalty : option ℤ := none)
(builder : option builder_clause := none)

namespace normalization_rule_config

meta def add_clause (conf : normalization_rule_config) :
  rule_clause → exceptional normalization_rule_config
| (rule_clause.builder c) :=
  if conf.builder.is_some
    then exceptional.fail "Duplicate builder clause not allowed."
    else pure { builder := some c, ..conf }
| (rule_clause.safety c) := exceptional.fail
  "Safety clause not allowed for normalization rules."

meta def add_clauses (clauses : list rule_clause)
  (conf : normalization_rule_config) : exceptional normalization_rule_config :=
clauses.mfoldl add_clause conf

meta def parser : lean.parser normalization_rule_config :=
with_desc "penalty (clause)..." $ do
  penalty ← optional small_int,
  clauses ← many rule_clause.parser,
  let init : normalization_rule_config := { penalty := penalty },
  init.add_clauses clauses

end normalization_rule_config

meta def normalization_declaration_to_rule (decl : name)
  (conf : normalization_rule_config) : tactic rule_set_member := do
  env ← get_env,
  d ← env.get decl,
  let builder :=
    (builder_clause.to_rule_builder <$> conf.builder).get_or_else
      rule_builder.normalization_default,
  r ← builder d,
  match r with
  | rule_builder_output.rule r imode :=
    pure $ rule_set_member.normalization_rule
      { penalty := conf.penalty.get_or_else 0, ..r }
      imode
  | rule_builder_output.simp_lemmas s := do
    when conf.penalty.is_some $ fail!
      "Penalty annotation is not allowed for norm equations (only for norm tactics).",
    pure $ rule_set_member.normalization_simp_lemmas s
  end

@[derive has_reflect]
structure safe_rule_config :=
(penalty : option ℤ := none)
(builder : option builder_clause := none)
(safety : option safety_clause := none)

namespace safe_rule_config

meta def add_clause (conf : safe_rule_config) :
  rule_clause → exceptional safe_rule_config
| (rule_clause.builder c) :=
  if conf.builder.is_some
    then exceptional.fail "Duplicate builder clause not allowed."
    else pure { builder := c, ..conf }
| (rule_clause.safety c) :=
  if conf.safety.is_some
    then exceptional.fail "Duplicate safety clause not allowed."
    else pure { safety := c, ..conf }

meta def add_clauses (clauses : list rule_clause)
  (conf : safe_rule_config) : exceptional safe_rule_config :=
clauses.mfoldl add_clause conf

meta def parser : lean.parser safe_rule_config :=
with_desc "penalty (clause)..." $ do
  penalty ← optional small_int,
  clauses ← many rule_clause.parser,
  let init : safe_rule_config := { penalty := penalty },
  init.add_clauses clauses

end safe_rule_config

meta def safe_declaration_to_rule (decl : name) (conf : safe_rule_config) :
  tactic rule_set_member := do
  env ← get_env,
  d ← env.get decl,
  let penalty := conf.penalty.get_or_else 0,
  let safety :=
    (safety_clause.to_safety <$> conf.safety).get_or_else safety.safe,
  let builder :=
    (builder_clause.to_rule_builder <$> conf.builder).get_or_else
      rule_builder.safe_default,
  r ← builder d,
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
(builder : option builder_clause := none)

namespace unsafe_rule_config

meta def add_clause (conf : unsafe_rule_config) :
  rule_clause → exceptional unsafe_rule_config
| (rule_clause.builder c) :=
  if conf.builder.is_some
    then exceptional.fail "Duplicate builder clause not allowed."
    else pure { builder := some c, ..conf }
| (rule_clause.safety c) := exceptional.fail
  "Safety clause not allowed for unsafe rules."

meta def add_clauses (clauses : list rule_clause)
  (conf : unsafe_rule_config) : exceptional unsafe_rule_config :=
clauses.mfoldl add_clause conf

meta def parser : lean.parser unsafe_rule_config :=
with_desc "probability (clause)..." $ do
  success_probability ← percent.parser,
  clauses ← many rule_clause.parser,
  let init : unsafe_rule_config := { success_probability := success_probability },
  init.add_clauses clauses

end unsafe_rule_config

meta def unsafe_declaration_to_rule (decl : name) (conf : unsafe_rule_config) :
  tactic rule_set_member := do
  env ← get_env,
  d ← env.get decl,
  let builder :=
    (builder_clause.to_rule_builder <$> conf.builder).get_or_else
      rule_builder.unsafe_default,
  r ← builder d,
  match r with
  | rule_builder_output.rule r imode :=
    pure $ rule_set_member.unsafe_rule
      { success_probability := conf.success_probability, ..r }
      imode
  | rule_builder_output.simp_lemmas _ :=
    fail! "aesop/unsafe_declaration_to_rule: internal error: unexpected rule builder output"
  end

/-! ## Attribute -/

@[derive has_reflect]
inductive rule_config : Type
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

meta def attr_config_parser : lean.parser rule_config :=
with_desc "[norm | safe | unsafe] rule_config" $ do
  rule_type ← optional ident,
  match rule_type with
  | some `norm   := rule_config.normalization <$> normalization_rule_config.parser
  | some `safe   := rule_config.safe <$> safe_rule_config.parser
  | some `unsafe := rule_config.unsafe <$> unsafe_rule_config.parser
  | none         := rule_config.unsafe <$> unsafe_rule_config.parser
  | some n       := fail $ format! "Unknown aesop attribute type: {n}"
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
inductive config_clause
| additional_rules (rs : list (name × rule_config))

meta def rule_parser {α} (p : lean.parser α) : lean.parser (name × α) :=
prod.mk <$> ident <*> p

meta def rules_parser {α} (p : lean.parser α) : lean.parser (list (name × α)) :=
list_of (rule_parser p)

meta def simple_config_clauses : name_map config_clause :=
native.rb_map.mk _ _

meta def config_clauses : name_map (lean.parser config_clause) :=
native.rb_map.of_list
  [ (`unsafe,
      config_clause.additional_rules <$>
        rules_parser (rule_config.unsafe <$> unsafe_rule_config.parser)),
    (`safe,
      config_clause.additional_rules <$>
        rules_parser (rule_config.safe <$> safe_rule_config.parser)),
    (`norm,
      config_clause.additional_rules <$>
        rules_parser (rule_config.normalization <$> normalization_rule_config.parser)) ]

namespace config_clause

meta def parser : lean.parser config_clause :=
with_desc
  "((unsafe [id probability clause*, ...]) | (safe [id penalty clause*, ...]) | (norm [id penalty clause*, ...]))" $
  clause_parser simple_config_clauses config_clauses

end config_clause

@[derive has_reflect]
meta structure config :=
(additional_rules : list (name × rule_config) := [])

namespace config

meta def add_clause (conf : config) : config_clause → config
| (config_clause.additional_rules rs) :=
  { additional_rules := conf.additional_rules ++ rs ..conf }

meta def of_config_clauses (clauses : list config_clause) : config :=
clauses.foldl add_clause {}

meta def parser : lean.parser config :=
of_config_clauses <$> many config_clause.parser

meta def rule_set (conf : config) : tactic rule_set := do
  default_rules ← registered_rule_set,
  additional_rules ← declarations_to_rule_set conf.additional_rules,
  pure $ default_rules.merge additional_rules

end config

end aesop
end tactic
