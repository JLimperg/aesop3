/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.aesop.rule

namespace tactic
namespace aesop

meta inductive rule_builder_output
| rule (r : rule) (imode : indexing_mode)
| simp_lemmas (s : simp_lemmas)

meta def rule_builder := declaration → tactic rule_builder_output

namespace rule_builder

meta def tac : rule_builder := λ d,
match d.type with
| `(tactic unit) := do
  t ← eval_expr (tactic unit) d.value,
  pure $ rule_builder_output.rule
    { tac := t,
      description := to_fmt d.to_name }
    indexing_mode.unindexed
| _ := fail! "Expected {d.to_name} to have type `tactic unit`."
end

meta def apply_indexing_mode (type : expr) : tactic indexing_mode := do
  head_constant ← type.conclusion_head_constant,
  pure $
    match head_constant with
    | some c := index_target_head c
    | none := unindexed
    end

meta def apply : rule_builder := λ d, do
  imode ← apply_indexing_mode d.type,
  let n := d.to_name,
  pure $ rule_builder_output.rule
    { tac := mk_const n >>= tactic.apply >> skip,
      description := format! "apply {n}"}
    imode

meta def normalization_simp_lemma : rule_builder := λ d, do
  let n := d.to_name,
  s ← simp_lemmas.mk.add_simp n <|> fail!
    "Expected {n} to be a (conditional) equation that can be used as a simp lemma.",
  pure $ rule_builder_output.simp_lemmas s

meta def no_tactic (d : declaration) : tactic unit :=
match d.type with
| `(tactic _) := fail! "To register a tactic as an Aesop rule, it must have type `tactic unit`, but {d.to_name} has type `{d.type}`."
| _ := pure ()
end

meta def normalization_default : rule_builder := λ d,
tac d <|> normalization_simp_lemma d <|>
  fail! "Expected {d.to_name} to have type `tactic unit` or to be suitable as a simp lemma."

meta def safe_default : rule_builder := λ d,
tac d <|> (no_tactic d >> apply d)

meta def unsafe_default : rule_builder :=
safe_default

end rule_builder
end aesop
end tactic
