/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import data.list.sort
import tactic.auto.attribute
import tactic.auto.percent
import tactic.auto.priority_queue
import tactic.auto.tracing
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

- I'd like the goal mvars to have names that reflect the node they belong to,
  e.g. `n0` for the mvar of node 0. The code contains an attempt to do this, but
  it seems like the printing functions don't actually use the pretty mvar names
  at all.
-/

namespace tactic
namespace auto

/-! ## Unexpanded Rule Applications -/

meta structure unexpanded_rapp :=
(cumulative_success_probability : percent)
(parent : node_id)
(rule : regular_rule)

namespace unexpanded_rapp

protected meta def lt (n m : unexpanded_rapp) : bool :=
n.cumulative_success_probability < m.cumulative_success_probability

meta instance : has_lt unexpanded_rapp :=
⟨λ r s, unexpanded_rapp.lt r s = tt⟩

protected meta def to_fmt (n : unexpanded_rapp) : format :=
format! "[{n.cumulative_success_probability}] for node {n.parent}: {n.rule}"

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

meta def select_rules (rs : rule_set) (id : node_id)
  (goal : expr) (node_success_probability : percent) :
  tactic (list unexpanded_rapp) := do
  rules ← with_local_goals' [goal] $ rs.applicable_regular_rules,
  pure $ rules.map $ λ r,
    let p := node_success_probability * r.success_probability in
    { parent := id, rule := r, cumulative_success_probability := p }

meta def run_normalization_rule (r : normalization_rule) : tactic unit := do
  g ← get_goal,
  let fail_with_context : format → tactic unit := λ err, do {
    ctx ← pformat! "rule: {r}\ngoal:{format.nested 2 <$> g.format_goal}",
    fail $ err ++ format.nested 2 ctx
  },
  r.tac <|>
    fail_with_context "auto: normalization rule failed",
  [_] ← get_goals |
    fail_with_context "auto: normalization rule did not produce exactly one goal",
  pure ()

meta def run_normalization_simp (s : simp_lemmas) : tactic unit := do
  g ← get_goal,
  simp_all s [] { fail_if_unchanged := ff },
    -- TODO discharger should be nested auto
  gs ← get_goals,
  match gs with
  | [_] := pure ()
  | _ := do
    trace "wtf",
    initial_goal ← g.format_goal,
    gs ← format.unlines <$> gs.mmap format.of_goal,
    fail $
      ("auto: normalization simp rule produced more than one goal" : format) ++
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

meta def add_node (rs : rule_set) (s : state) (goal : expr)
  (success_probability : percent) (parent : option rapp_id) :
  tactic (node_id × state) := do
  trace $ format! "adding subgoal of rapp {parent}",
  goal ← normalize_goal rs goal,
  let id := s.search_tree.next_node_id,
  -- TODO useless?
  let goal := goal.set_pretty_name $ mk_simple_name ("n" ++ id.to_fmt.to_string),
  unexpanded_rapps ← select_rules rs id goal success_probability,
  trace $ format!
    "adding unexpanded rapps:{format.nested 2 $ format.unlines $ unexpanded_rapps.map to_fmt}",
  let n : node :=
    { parent := parent,
      goal := goal,
      num_rules_todo := unexpanded_rapps.length,
      cumulative_success_probability := success_probability,
      rapps := [],
      failed_rapps := [],
      is_proven := ff,
      is_unprovable := ff,
      is_irrelevant := ff },
  trace $ pformat! "adding node:{format.nested 2 <$> pp n}",
  let (_, t) := s.search_tree.insert_node n,
  let s : state :=
    { unexpanded_rapps := s.unexpanded_rapps.insert_list unexpanded_rapps,
      search_tree := t },
  pure (id, s)

meta def add_nodes (rs : rule_set) (s : state) (goals : list expr)
  (success_probability : percent) (parent : rapp_id) :
  tactic (list node_id × state) :=
goals.mfoldl
  (λ ⟨ids, s⟩ goal, do
    (id, s) ← add_node rs s goal success_probability parent,
    pure (id :: ids, s))
  ([], s)

meta def initial_state (rs : rule_set) : tactic state := do
  trace "setting up initial state",
  tgt ← target,
  goal ← mk_meta_var tgt,
  prod.snd <$> add_node rs state.empty goal ⟨100⟩ none

meta def run_rule (goal : expr) (r : regular_rule) : tactic (option (expr × list expr)) :=
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
  parent ← t.get_node' parent_id "auto/expand_rapp: internal error: ",
  trace $ pformat! "parent node:{format.nested 2 <$> pp parent}",
  rule_result ← run_rule parent.goal rule,
  let success_probability :=
    parent.cumulative_success_probability * rule.success_probability,
  s ← match rule_result with
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
          r_fmt ← pp r,
          trace $ format! "recording new rapp:{format.nested 2 r_fmt}",
          let (rid, t) := t.insert_rapp r,
          -- 2. Mark parent node, and potentially ancestors, as proven.
          let t := t.set_node_proven parent_id,
          pure { search_tree := t, ..s }
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
          (_, s) ← add_nodes rs s subgoals success_probability rid,
          pure s
      | none := do
          -- Rule did not succeed.
          trace "rule failed",
          -- 1. Record rule failure.
          let t := t.modify_node parent_id $ λ parent,
            { failed_rapps := rule :: parent.failed_rapps, ..parent },
          -- 2. Potentially mark parent node (and ancestors) as unprovable.
          let t := t.set_node_unprovable parent_id,
          pure { search_tree := t, ..s }
      end,
  pure s

meta def expand (rs : rule_set) (s : state) : tactic (option state) := do
  trace "=====================================================================",
  trace_tree s.search_tree,
  some (to_expand, unexpanded_rapps) ← pure s.unexpanded_rapps.pop_min
    | pure none,
  trace $ format! "expanding {to_expand}",
  let s := { unexpanded_rapps := unexpanded_rapps, ..s },
  parent ← s.search_tree.get_node' to_expand.parent
    "auto/expand: internal error: ",
  if parent.is_proven ∨ parent.is_unprovable ∨ parent.is_irrelevant
    then do
      trace "rapp is irrelevant, skipping",
      pure (some s)
    else some <$> expand_rapp rs s to_expand

meta def finish_if_proven (s : state) : tactic bool := do
  tt ← pure $ s.search_tree.root_node_is_proven
    | pure ff,
  trace "=====================================================================",
  trace "root node is proven, extracting proof",
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
      | fail "auto/search_loop: internal error: no more rules to apply but root node is not marked as unprovable",
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

attribute [auto  50] EvenOrOdd.odd EvenOrOdd.even
attribute [auto 100] Even.zero Even.plus_two Odd.one

def even_or_odd (n : ℕ) : Prop := EvenOrOdd n

lemma even_or_odd_def {n} : even_or_odd n = EvenOrOdd n := rfl

@[auto norm 50]
meta def test_norm_tactic : tactic unit := `[try { simp [even_or_odd_def] at * }]

@[auto 50]
meta def test_regular_tactic : tactic unit := `[apply Odd.plus_two]

set_option trace.auto.steps true

example : even_or_odd 3 := by auto
