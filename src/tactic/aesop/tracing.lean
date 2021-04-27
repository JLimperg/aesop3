/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.aesop.tree

declare_trace aesop.steps
declare_trace aesop.tree
declare_trace aesop.rule_set

variables {α β : Type} [has_to_tactic_format α] [has_to_tactic_format β]

namespace tactic

meta def trace_tagged (n : name) (tag : string) (msg : α) : tactic unit :=
when_tracing n $ trace! "[{tag}] {msg}"

meta def trace_nested (n : name) (tag : string) (header : α) (body : β) :
  tactic unit :=
when_tracing n $ trace! "[{tag}] {header}{format.nested 2 <$> pp body}"

namespace aesop

meta def trace : α → tactic unit :=
trace_tagged `aesop.steps "aesop"

meta def trace_nested : α → β → tactic unit :=
tactic.trace_nested `aesop.steps "aesop"

meta def trace_separator : tactic unit :=
trace "================================================================================"

meta def trace_tree (t : tree) : tactic unit :=
tactic.trace_nested `aesop.tree "aesop" "search tree" t

meta def trace_rule_set (rs : rule_set) : tactic unit :=
tactic.trace_nested `aesop.rule_set "aesop" "rule set" rs

end aesop
end tactic
