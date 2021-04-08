/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.auto.tree

declare_trace auto.steps
declare_trace auto.tree
declare_trace auto.rule_set

variables {α β : Type} [has_to_tactic_format α] [has_to_tactic_format β]

namespace tactic

meta def trace_tagged (n : name) (tag : string) (msg : α) : tactic unit :=
when_tracing n $ trace! "[{tag}] {msg}"

meta def trace_nested (n : name) (tag : string) (header : α) (body : β) :
  tactic unit :=
when_tracing n $ trace! "[{tag}] {header}{format.nested 2 <$> pp body}"

namespace auto

meta def trace : α → tactic unit :=
trace_tagged `auto.steps "auto"

meta def trace_nested : α → β → tactic unit :=
tactic.trace_nested `auto.steps "auto"

meta def trace_separator : tactic unit :=
trace "================================================================================"

meta def trace_tree (t : tree) : tactic unit :=
tactic.trace_nested `auto.tree "auto" "search tree" t

meta def trace_rule_set (rs : rule_set) : tactic unit :=
tactic.trace_nested `auto.rule_set "auto" "rule set" rs

end auto
end tactic
