/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.auto.attribute
import tactic.auto.priority_queue
import tactic.auto.tree

/-!
# `auto`, a general-purpose proof search tactic
-/

/-
TODO:

- Metavariables need to be reset when we switch between branches of the search
  tree. Currently, mvars may leak freely between branches. Maybe the best
  solution here is to disallow proof rules from introducing new metas, except
  for those which represent goals. auto could check this at runtime, or elide
  the check for efficiency unless a 'debug mode' is toggled.
-/

namespace tactic
namespace auto

/-! ## Unexpanded Rule Applications -/

meta structure unexpanded_rapp :=
(parent : node_id)
(rule : rule)

namespace unexpanded_rapp

protected meta def lt (n m : unexpanded_rapp) : bool :=
rule.lt n.rule m.rule

meta instance : has_lt unexpanded_rapp :=
⟨λ r s, unexpanded_rapp.lt r s = tt⟩

protected meta def to_fmt (n : unexpanded_rapp) : format :=
"for node " ++ n.parent.to_fmt ++ ": " ++ n.rule.to_fmt

meta instance : has_to_format unexpanded_rapp :=
⟨unexpanded_rapp.to_fmt⟩

end unexpanded_rapp

/-! ## Search State -/

meta structure state :=
(search_tree : tree)
(unexpanded_rapps : priority_queue unexpanded_rapp unexpanded_rapp.lt)

namespace state

protected meta def to_tactic_format (s : state) : tactic format := do
  t ← pp s.search_tree,
  let unexpanded :=
    format.unlines $ s.unexpanded_rapps.to_list.map unexpanded_rapp.to_fmt,
  pure $ format.join
    [ "search tree:"
    , format.nested 2 t
    , format.line
    , "unexpanded nodes:"
    , format.nested 2 unexpanded
    ]

meta instance : has_to_tactic_format state :=
⟨state.to_tactic_format⟩

meta def empty : state :=
{ search_tree := tree.empty,
  unexpanded_rapps := priority_queue.empty }

end state

/-! ## Best-First Search -/

meta def select_rules (rs : rule_set) (id : node_id) (goal : expr) :
  tactic (list unexpanded_rapp) := do
  rules ← with_local_goals' [goal] $ rs.applicable_regular_rules,
  pure $ rules.map $ λ r, { parent := id, rule := r }

meta def add_node (rs : rule_set) (s : state) (goal : expr)
  (parent : option rapp_id) : tactic (node_id × state) := do
  let id := s.search_tree.next_node_id,
  -- TODO useless?
  let goal := goal.set_pretty_name $ mk_simple_name ("n" ++ id.to_fmt.to_string),
  unexpanded_rapps ← select_rules rs id goal,
  let n : node :=
    { parent := parent,
      goal := goal,
      num_rules_todo := unexpanded_rapps.length,
      rapps := [],
      failed_rapps := [],
      is_proven := ff,
      is_unprovable := ff,
      is_irrelevant := ff },
  let (_, t) := s.search_tree.insert_node n,
  let s : state :=
    { unexpanded_rapps := s.unexpanded_rapps.insert_list unexpanded_rapps,
      search_tree := t },
  pure (id, s)

meta def add_nodes (rs : rule_set) (s : state) (goals : list expr)
  (parent : rapp_id) : tactic (list node_id × state) :=
goals.mfoldl
  (λ ⟨ids, s⟩ goal, do
    (id, s) ← add_node rs s goal parent,
    pure (id :: ids, s))
  ([], s)

meta def initial_state (rs : rule_set) : tactic state := do
  goal ← get_goal,
  prod.snd <$> add_node rs state.empty goal none

meta def run_rule (goal : expr) (r : rule) : tactic (option (expr × list expr)) :=
with_local_goals' [goal] $ do
  tgt ← target,
  goal' ← mk_meta_var tgt,
  -- TODO useless?
  let goal' :=
    match goal.match_mvar with
    | some (_, n, _) := goal'.set_pretty_name n
    | none := goal'
    end,
  set_goals [goal'],
  try_core $ do
    r.tac,
    subgoals ← get_goals,
    pure (goal', subgoals)

meta def expand_rapp (rs : rule_set) (s : state) (n : unexpanded_rapp) :
  tactic state := do
  let parent_id := n.parent,
  let rule := n.rule,
  let t := s.search_tree.modify_node parent_id $ λ parent,
    { num_rules_todo := parent.num_rules_todo - 1, ..parent },
  rule_result ← do {
    parent ← t.get_node' parent_id "auto/expand/rapp: internal error: ",
    run_rule parent.goal rule },
  s ← match rule_result with
      | some (prf, []) := do
          -- Rule succeeded and did not generate subgoals, meaning the parent
          -- node is proven.
          -- 1. Record the rule application.
          let r : rapp :=
            { applied_rule := rule,
              proof := prf,
              subgoals := [],
              parent := parent_id,
              is_proven := tt,
              is_unprovable := ff,
              is_irrelevant := ff },
          let (rid, t) := t.insert_rapp r,
          -- 2. Mark parent node, and potentially ancestors, as proven.
          let t := t.set_node_proven parent_id,
          pure { search_tree := t, ..s }
      | some (prf, subgoals) := do
          -- Rule succeeded and generated subgoals.
          -- 1. Record the rule application.
          let r : rapp :=
            { applied_rule := rule,
              proof := prf,
              subgoals := [],
              parent := parent_id,
              is_proven := ff,
              is_unprovable := ff,
              is_irrelevant := ff },
          let (rid, t) := t.insert_rapp r,
          let s := { search_tree := t, ..s },
          -- 2. Record the subgoals.
          (_, s) ← add_nodes rs s subgoals rid,
          pure s
      | none := do
          -- Rule did not succeed.
          -- 1. Record rule failure.
          let t := t.modify_node parent_id $ λ parent,
            { failed_rapps := rule :: parent.failed_rapps, ..parent },
          -- 2. Potentially mark parent node (and ancestors) as unprovable.
          let t := t.set_node_unprovable parent_id,
          pure { search_tree := t, ..s }
      end,
  trace "---------------------------------------------------------------------",
  trace s,
  pure s

meta def expand (rs : rule_set) (s : state) : tactic (option state) := do
  trace "=====================================================================",
  trace s,
  some (to_expand, unexpanded_rapps) ← pure s.unexpanded_rapps.pop_min
    | pure none,
  trace "---------------------------------------------------------------------",
  trace! "expanding for node {to_expand.parent}: {to_expand.rule}",
  let s := { unexpanded_rapps := unexpanded_rapps, ..s },
  parent ← s.search_tree.get_node' to_expand.parent
    "auto/expand: internal error: ",
  if parent.is_proven ∨ parent.is_unprovable ∨ parent.is_irrelevant
    then pure (some s)
    else some <$> expand_rapp rs s to_expand

meta def finish_if_proven (s : state) : tactic bool := do
  tt ← pure $ s.search_tree.root_node_is_proven
    | pure ff,
  s.search_tree.link_proofs,
  prf ← s.search_tree.extract_proof,
  exact prf,
  pure tt

private meta def search_loop (rs : rule_set) : state → tactic unit := λ s, do
  ff ← pure $ s.search_tree.root_node_is_unprovable
    | fail "auto: failed to prove the goal",
  done ← finish_if_proven s,
  when ¬ done $ do
    (some s) ← expand rs s
      | fail "auto: internal error: no more rules to apply but root node is not marked as unprovable",
    search_loop s

meta def search (rs : rule_set) : tactic unit :=
initial_state rs >>= search_loop rs

meta def auto : tactic unit :=
attr.registered_rule_set >>= search

end auto

meta def auto : tactic unit :=
tactic.auto.auto

meta def interactive.auto : tactic unit :=
tactic.auto.auto

end tactic

/-!
## Tests
-/

inductive Even : ℕ → Prop
| zero : Even 0
| plus_two {n} : Even n → Even (n + 2)

inductive Odd : ℕ → Prop
| one : Odd 1
| plus_two {n} : Odd n → Odd (n + 2)

inductive EvenOrOdd : ℕ → Prop
| even {n} : Even n → EvenOrOdd n
| odd {n} : Odd n → EvenOrOdd n

attribute [auto 10] EvenOrOdd.odd EvenOrOdd.even
attribute [auto  1] Even.zero Even.plus_two
attribute [auto  0] Odd.one Odd.plus_two

example : EvenOrOdd 3 := by auto
