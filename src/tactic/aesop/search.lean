/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import data.list.sort
import tactic.aesop.config
import tactic.aesop.percent
import tactic.aesop.priority_queue
import tactic.aesop.tracing
import tactic.aesop.tree

/-
TODO:

- Metavariables need to be reset when we switch between branches of the search
  tree. Currently, mvars may leak freely between branches. Maybe the best
  solution here is to disallow proof rules from introducing new metas, except
  for those which represent goals. Aesop could check this at runtime, or elide
  the check for efficiency unless a 'debug mode' is toggled.

- I'd like the goal mvars to have names that reflect the node they belong to,
  e.g. `n0` for the mvar of node 0. I made an attempt to do this earlier, but
  it seemed like the printing functions don't actually use the pretty mvar names
  at all.
-/

namespace tactic
namespace aesop

/-! ## Unexpanded Rule Applications -/

meta structure active_node :=
(cumulative_success_probability : percent)
(node : node_id)

namespace active_node

protected meta def lt (r s : active_node) : Prop :=
r.cumulative_success_probability < s.cumulative_success_probability

meta instance : has_lt active_node :=
⟨active_node.lt⟩

meta instance : decidable_rel ((<) : active_node → active_node → Prop) :=
λ r s,
  (infer_instance : decidable
    (r.cumulative_success_probability < s.cumulative_success_probability))

protected meta def to_fmt (n : active_node) : format :=
format! "[{n.cumulative_success_probability}] node {n.node}"

meta instance : has_to_format active_node :=
⟨active_node.to_fmt⟩

end active_node

/-! ## Search State -/

meta structure state :=
(search_tree : tree)
(active_nodes : priority_queue active_node (λ r s, r > s))

namespace state

protected meta def to_tactic_format (s : state) : tactic format := do
  t ← pp s.search_tree,
  let active_nodes :=
    format.unlines $ s.active_nodes.to_list.map active_node.to_fmt,
  pure $ format.join
    [ "search tree:"
    , format.nested 2 t
    , format.line
    , "active nodes:"
    , format.nested 2 active_nodes
    ]

meta instance : has_to_tactic_format state :=
⟨state.to_tactic_format⟩

meta def empty : state :=
{ search_tree := tree.empty,
  active_nodes := priority_queue.empty }

meta def modify_search_tree (f : tree → tree) (s : state) : state :=
{ search_tree := f s.search_tree, ..s }

meta def modify_active_nodes
  (f : priority_queue active_node (λ r s, r > s)
     → priority_queue active_node (λ r s, r > s))
  (s : state) : state :=
{ active_nodes := f s.active_nodes, ..s }

end state

/-! ## Best-First Search -/

meta def add_node (s : state) (goal : expr) (success_probability : percent)
  (parent : option rapp_id) : tactic (node_id × state) := do
  let n : node :=
    { parent := parent,
      goal := goal,
      cumulative_success_probability := success_probability,
      rapps := [],
      failed_rapps := [],
      unsafe_queue := none,
      is_normal := ff,
      is_proven := ff,
      is_unprovable := ff,
      is_irrelevant := ff },
  let (id, t) := s.search_tree.insert_node n,
  trace $ pformat! "adding node {id}:{format.nested 2 <$> pp n}",
  let an : active_node :=
    { node := id,
      cumulative_success_probability := success_probability },
  let s : state :=
    { active_nodes := s.active_nodes.insert an,
      search_tree := t },
  pure (id, s)

meta def add_nodes (s : state) (goals : list expr)
  (success_probability : percent) (parent : rapp_id) :
  tactic (list node_id × state) :=
goals.mfoldl
  (λ ⟨ids, s⟩ goal, do
    (id, s) ← add_node s goal success_probability parent,
    pure (id :: ids, s))
  ([], s)

meta def initial_state : tactic state := do
  trace "setting up initial state",
  tgt ← target,
  goal ← mk_meta_var tgt,
  prod.snd <$> add_node state.empty goal ⟨100⟩ none

meta def run_rule (goal : expr) (r : tactic unit) :
  tactic (option (expr × list expr)) :=
with_local_goals' [goal] $ do
  tgt ← target,
  goal' ← mk_meta_var tgt,
  set_goals [goal'],
  try_core $ do
    r,
    subgoals ← get_goals,
    pure (goal', subgoals)

meta inductive rule_result
| solved
| failed
| succeeded

meta def apply_regular_rule (s : state) (parent_id : node_id)
  (rule : regular_rule) : tactic (state × rule_result) := do
  let t := s.search_tree,
  parent ← t.get_node' parent_id "aesop/expand_rapp: internal error: ",
  result ← run_rule parent.goal rule.to_rule.tac,
  let success_probability :=
    parent.cumulative_success_probability * rule.success_probability,
  match result with
    | some (prf, []) := do
        -- Rule succeeded and did not generate subgoals, meaning the parent
        -- node is proven.
        trace "rule solved the goal",
        -- 1. Record the rule application.
        let r : rapp :=
          { applied_rule := rule,
            cumulative_success_probability := success_probability,
            proof := prf,
            subgoals := [],
            parent := parent_id,
            is_proven := tt,
            is_unprovable := ff,
            is_irrelevant := ff },
        trace $ pformat! "adding new rule application:{format.nested 2 <$> pp r}",
        let (rid, t) := t.insert_rapp r,
        -- 2. Mark parent node, and potentially ancestors, as proven.
        let t := t.set_node_proven parent_id,
        pure ({ search_tree := t, ..s }, rule_result.solved)
    | some (prf, subgoals) := do
        -- Rule succeeded and generated subgoals.
        trace "rule applied successfully",
        -- 1. Record the rule application.
        let r : rapp :=
          { applied_rule := rule,
            cumulative_success_probability := success_probability,
            proof := prf,
            subgoals := [],
            parent := parent_id,
            is_proven := ff,
            is_unprovable := ff,
            is_irrelevant := ff },
        r_fmt ← pp r,
        trace $ format! "recording new rapp:{format.nested 2 r_fmt}",
        let (rid, t) := t.insert_rapp r,
        let s := { search_tree := t, ..s },
        -- 2. Record the subgoals.
        (_, s) ← add_nodes s subgoals success_probability rid,
        pure (s, rule_result.succeeded)
    | none := do
        -- Rule did not succeed.
        trace "rule failed",
        -- 1. Record rule failure.
        let t := t.modify_node parent_id $ λ parent,
          { failed_rapps := rule :: parent.failed_rapps, ..parent },
        -- 2. Potentially mark parent node (and ancestors) as unprovable.
        let t := t.set_node_unprovable parent_id,
        pure ({ search_tree := t, ..s }, rule_result.failed)
    end

meta def run_normalization_rule (r : normalization_rule) : tactic unit := do
  g ← get_goal,
  let fail_with_context : format → tactic unit := λ err, do {
    ctx ← pformat! "rule: {r}\ngoal:{format.nested 2 <$> g.format_goal}",
    fail $ err ++ format.nested 2 ctx
  },
  r.tac <|>
    fail_with_context "aesop: normalization rule failed",
  [_] ← get_goals |
    fail_with_context "aesop: normalization rule did not produce exactly one goal",
  pure ()

meta def run_normalization_simp (s : simp_lemmas) : tactic unit := do
  g ← get_goal,
  simp_all s [] { fail_if_unchanged := ff },
    -- TODO discharger should be nested aesop
  gs ← get_goals,
  -- TODO allow normalization to solve the goal
  match gs with
  | [_] := pure ()
  | _ := do
    initial_goal ← g.format_goal,
    gs ← format.unlines <$> gs.mmap format.of_goal,
    fail $
      ("aesop: normalization simp rule did not produce exactly one goal" : format) ++
      format.nested 2
        (format! "initial goal:{format.nested 2 initial_goal}" ++
         format! "goals produced by simp:{format.nested 2 gs}")
  end

meta def normalize_goal (rs : rule_set) (goal : expr) : tactic expr :=
with_local_goals' [goal] $ do
  trace $ pformat!
    "goal before normalization:{format.nested 2 <$> goal.format_goal}",
  rules ← rs.applicable_normalization_rules,
  let (pre_simp_rules, post_simp_rules) := rules.partition
    (λ (r : normalization_rule), r.penalty < 0),
  pre_simp_rules.mmap' run_normalization_rule,
  run_normalization_simp rs.normalization_simp_lemmas,
  post_simp_rules.mmap' run_normalization_rule,
  goal ← get_goal,
  trace $ pformat!
    "goal after normalization:{format.nested 2 <$> goal.format_goal}",
  pure goal

meta def normalize_node_if_necessary (rs : rule_set) (s : state) (id : node_id)
  (n : node) : tactic node := do
  ff ← pure n.is_normal | pure n,
  trace $ format! "normalizing node {id}",
  goal ← normalize_goal rs n.goal,
  pure { goal := goal, ..n }

meta def select_rules_if_necessary (rs : rule_set) (s : state) (n : node) :
  tactic node := do
  none ← pure n.unsafe_queue | pure n,
  rules ← with_local_goals' [n.goal] rs.applicable_unsafe_rules,
  trace $ format!
    "applicable unsafe rules:{format.nested 2 $ format.unlines $ rules.map to_fmt}",
  pure { unsafe_queue := rules, ..n }

meta def apply_first_safe_rule_aux (id : node_id) :
  state → list safe_rule → tactic (state × rule_result)
| s [] := do
  pure (s, rule_result.failed)
| s (r :: rs) := do
  trace $ format! "applying rule: {r}",
  (s, result) ← apply_regular_rule s id (regular_rule.safe r),
  match result with
  | rule_result.failed := apply_first_safe_rule_aux s rs
  | _ := pure (s, result)
  end

meta def apply_first_safe_rule (rs : rule_set) (s : state) (id : node_id) :
  tactic (state × rule_result) := do
  n ← s.search_tree.get_node' id "aesop/expand_node: internal error: ",
  rules ← with_local_goals' [n.goal] rs.applicable_safe_rules,
  trace $ format!
    "applicable safe rules:{format.nested 2 $ format.unlines $ rules.map to_fmt}",
  apply_first_safe_rule_aux id s rules

-- TODO loop if rule failed instead of going back to main loop
meta def apply_first_unsafe_rule (s : state) (id : node_id) :
  tactic state := do
  n ← s.search_tree.get_node' id "aesop/expand_node: internal error: ",
  some (rule :: rules) ← pure n.unsafe_queue
    | pure $ s.modify_search_tree $ λ t, t.set_node_unprovable id,
  trace $ format! "applying rule: {rule}",
  let s := s.modify_search_tree $ λ t,
    t.replace_node id { unsafe_queue := rules, ..n },
  (s, _) ← apply_regular_rule s id (regular_rule.unsafe rule),
  pure $
    if rules.empty
      then s
      else s.modify_active_nodes $ λ q, q.insert
        { node := id,
          cumulative_success_probability := n.cumulative_success_probability }

meta def expand_node (rs : rule_set) (s : state) (id : node_id) :
  tactic state := do
  n ← s.search_tree.get_node' id "aesop/expand_node: internal error: ",
  n ← normalize_node_if_necessary rs s id n,
  let s := s.modify_search_tree $ λ t, t.replace_node id n,
  (s, result) ← apply_first_safe_rule rs s id,
  match result with
  | rule_result.failed := do
    n ← select_rules_if_necessary rs s n,
    let s := s.modify_search_tree $ λ t, t.replace_node id n,
    apply_first_unsafe_rule s id
  | _ := pure s
  end

meta def expand (rs : rule_set) (s : state) : tactic state := do
  trace "=====================================================================",
  trace_tree s.search_tree,
  some (active_node, active_nodes) ← pure s.active_nodes.pop_min
    | fail "aesop/expand: internal error: no more rules to apply",
  let id := active_node.node,
  let s := { active_nodes := active_nodes, ..s },
  n ← s.search_tree.get_node' id "aesop/expand: internal error: ",
  trace $ pformat!
    "expanding node {id} ({active_node.cumulative_success_probability}):{format.nested 2 <$> pp n}",
  if n.is_proven ∨ n.is_unprovable ∨ n.is_irrelevant
    then trace "node is proven/unprovable/irrelevant, skipping" >> pure s
    else expand_node rs s id

meta def finish_if_proven (s : state) : tactic bool := do
  tt ← pure $ s.search_tree.root_node_is_proven
    | pure ff,
  trace "=====================================================================",
  trace "root node is proven, extracting proof",
  trace_tree s.search_tree,
  s.search_tree.link_proofs,
  prf ← s.search_tree.extract_proof,
  exact prf,
  pure tt

private meta def search_loop (rs : rule_set) : state → tactic unit := λ s, do
  ff ← pure $ s.search_tree.root_node_is_unprovable
    | trace_tree s.search_tree >> fail "aesop: failed to prove the goal",
  done ← finish_if_proven s,
  when ¬ done $ expand rs s >>= search_loop

meta def search (rs : rule_set) : tactic unit := do
  trace_rule_set rs,
  s ← initial_state,
  search_loop rs s

meta def aesop (c : config) : tactic unit :=
c.rule_set >>= search

end aesop
end tactic
