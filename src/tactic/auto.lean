/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.core

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
- Search tree representation. Currently, the search tree is entirely implicit.
  If we want best-first or breadth-first search, we instead need to represent
  the search tree explicitly. Goals can be represented by metas, per usual. But
  what about the mvar context?
- Rule indexing. Currently, we iterate through the list of rules one-by-one,
  which is a tiny bit inefficient.
-/

universes u v w

/-!
## Utility stuff
-/

namespace list

def find_and_remove {α} (p : α → Prop) [decidable_pred p] :
  list α → option (α × list α)
| [] := none
| (a :: as) :=
  if p a
    then some (a, as)
    else do
      (x, as) ← find_and_remove as,
      pure (x, a :: as)

end list

namespace native.rb_lmap

open native

meta def insert_list {α β} (m : rb_lmap α β) (a : α) (bs : list β) : rb_lmap α β :=
match rb_map.find m a with
| none := rb_map.insert m a bs
| some bs' := rb_map.insert m a (bs ++ bs')
end

end native.rb_lmap

namespace tactic

meta def duplicate_main_goal_mvar : tactic expr := do
  tgt ← target,
  mk_meta_var tgt

/-
`on_duplicated_goals t` runs the tactic `t` on a copy of the current goals. This
makes sure that `t` does not assign the goal metavariables.
-/
meta def on_duplicated_goals {α} (t : tactic α) : tactic α := do
  gs ← get_goals,
  gs' ← gs.mmap mk_meta_var,
  set_goals gs',
  finally t (set_goals gs)

end tactic

namespace format

open tactic

meta def unlines : list format → format :=
intercalate line

meta def nested (n : ℕ) (f : format) : format :=
if f.is_nil
  then nil
  else nest n $ format.line ++ f

meta def of_goal (e : expr) : tactic format :=
if e.is_mvar
  then with_local_goals' [e] $ read >>= pp
  else pp e

end format

namespace tactic
namespace auto

open expr
open native

/-!
## Mock implementation of prio queues
-/

structure priority_queue (α : Type u) (lt : α → α → bool) :=
(queue : list α)

namespace priority_queue

variables {α : Type u} {lt : α → α → bool}

def empty : priority_queue α lt :=
⟨[]⟩

def singleton (a : α) : priority_queue α lt :=
⟨[a]⟩

def from_list (as : list α) : priority_queue α lt :=
⟨list.qsort lt as⟩

def is_empty (q : priority_queue α lt) : bool :=
q.queue.empty

def insert (a : α) (q : priority_queue α lt) : priority_queue α lt :=
⟨list.qsort lt $ a :: q.queue⟩

def insert_list (as : list α) (q : priority_queue α lt) : priority_queue α lt :=
⟨list.qsort lt $ as ++ q.queue⟩

def pop_min (q : priority_queue α lt) : option (α × priority_queue α lt) :=
match q.queue with
| [] := none
| (a :: as) := some (a, ⟨as⟩)
end

def filter (p : α → Prop) [decidable_pred p] (q : priority_queue α lt) :
  priority_queue α lt :=
⟨q.queue.filter p⟩

def to_list (q : priority_queue α lt) : list α :=
q.queue

end priority_queue

/-!
## Rules
-/

meta structure rule :=
(penalty : ℕ)
(tac : tactic unit)
(description : format)

namespace rule

protected meta def to_fmt (r : rule) : format :=
format.sbracket (_root_.to_fmt r.penalty) ++ format.space ++ r.description

meta instance : has_to_format rule :=
⟨rule.to_fmt⟩

meta def make_apply (e : expr) : tactic rule :=
pure
  { tac := apply e >> skip,
    penalty := 0,
    description := format! "apply {e}" }

meta def make_const_apply (n : name) : tactic rule := do
  n ← resolve_constant n,
  pure
    { tac := mk_const n >>= apply >> skip,
      penalty := 0,
      description := format! "apply {n}" }

protected meta def lt (r s : rule) : bool :=
r.penalty < s.penalty

end rule

/-!
## Rule Set
-/

meta structure rule_set :=
(rules : list rule)

namespace rule_set

protected meta def to_fmt (rs : rule_set) : format :=
format.unlines $ rs.rules.map rule.to_fmt

meta instance : has_to_format rule_set :=
⟨rule_set.to_fmt⟩

meta def empty : rule_set :=
⟨[]⟩

meta def add (r : rule) (rs : rule_set) : rule_set :=
⟨r :: rs.rules⟩

meta def mfold {α} (rs : rule_set) (init : α) (f : α → rule → tactic α) : tactic α :=
rs.rules.mfoldl f init

meta def first {α} (rs : rule_set) (f : rule → tactic α) : tactic α :=
rs.rules.mfirst f

meta def merge (rs₁ rs₂ : rule_set) : rule_set :=
⟨rs₁.rules ++ rs₂.rules⟩

meta def from_list (rs : list rule) : rule_set :=
⟨rs⟩

meta def applicable_rules (rs : rule_set) : tactic (list rule) :=
pure rs.rules

end rule_set

/-!
## Attribute
-/

namespace attr

meta def declaration_to_rule (decl : name) : tactic rule :=
rule.make_const_apply decl

meta def declarations_to_rule_set (decls : list name) : tactic rule_set :=
rule_set.from_list <$> decls.mmap declaration_to_rule

@[user_attribute]
meta def attr : user_attribute rule_set unit :=
{ name := `auto,
  descr := "Registers a definition as a rule for the auto tactic.",
  cache_cfg := {
    mk_cache := declarations_to_rule_set,
    dependencies := [] } }

meta def registered_rule_set : tactic rule_set :=
attr.get_cache

end attr

/-!
## Search
-/

@[derive decidable_eq]
meta structure node_id :=
(to_nat : ℕ)

namespace node_id

protected meta def zero : node_id :=
⟨0⟩

protected meta def succ : node_id → node_id
| ⟨n⟩ := ⟨n + 1⟩

protected meta def one : node_id :=
⟨1⟩

protected meta def lt (n m : node_id) : Prop :=
n.to_nat < m.to_nat

meta instance : has_lt node_id :=
⟨node_id.lt⟩

-- Surely there's a less annoying way to write this.
meta instance : decidable_rel ((<) : node_id → node_id → Prop) :=
λ n m, (infer_instance : decidable (n.to_nat < m.to_nat))

protected meta def to_fmt (id : node_id) : format :=
_root_.to_fmt id.to_nat

meta instance : has_to_format node_id :=
⟨node_id.to_fmt⟩

end node_id

meta structure rule_application :=
(applied_rule : rule)
(proof : expr)
(subgoals : list node_id)

namespace rule_application

protected meta def to_tactic_format (r : rule_application) : tactic format := do
  proof ← pp r.proof,
  pure $ r.applied_rule.to_fmt ++ format.nested 2 (format.join
    [ "proof:",
      format.nested 2 proof,
      format.line,
      "subgoal nodes: " ++ to_fmt r.subgoals ])

meta instance : has_to_tactic_format rule_application :=
⟨rule_application.to_tactic_format⟩

end rule_application

meta structure node :=
(goal : expr)
(num_rules_todo : ℕ)
(active : list rule_application)
(proof : option rule_application)
(unprovable : list rule_application)
(failed : list rule)

namespace node

protected meta def to_tactic_format (n : node) : tactic format := do
  goal ← format.of_goal n.goal,
  active ← format.unlines <$> n.active.mmap pp,
  unprovable ← format.unlines <$> n.unprovable.mmap pp,
  proof ←
    match n.proof with
    | none := pure ("none" : format)
    | some p := pp p
    end,
  pure $ format.join
    [ "goal:",
      format.nested 2 goal,
      format.line,
      "number of rules to expand: " ++ to_fmt n.num_rules_todo,
      format.line,
      "active rules:",
      format.nested 2 active,
      format.line,
      "proof:",
      format.nested 2 proof,
      format.line,
      "unprovable rules:",
      format.nested 2 unprovable,
      format.line,
      "failed rules:",
      format.nested 2 $ format.unlines (n.failed.map to_fmt)
    ]

meta instance : has_to_tactic_format node :=
⟨node.to_tactic_format⟩

meta def initial (goal : expr) (num_rules_todo : ℕ) : node :=
{ goal := goal,
  num_rules_todo := num_rules_todo,
  failed := [],
  active := [],
  unprovable := [],
  proof := none }

meta def is_proven (n : node) : bool :=
n.proof.is_some

meta def is_unprovable (n : node) : bool :=
n.proof.is_none ∧ n.num_rules_todo = 0 ∧ n.active.is_nil

meta def is_unknown (n : node) : bool :=
n.proof.is_none ∧ (n.num_rules_todo > 0 ∨ ¬ n.active.is_nil)

meta def set_proof (proof : rule_application) (n : node) : node :=
{ proof := some proof, num_rules_todo := 0, ..n }

end node

/-
Invariant: All the `node_id`s in `children` and `parents` appear in `nodes`.
Invariant: The root node has ID `node_id.zero`.
-/
meta structure tree :=
(nodes : rb_map node_id node)
(parents : rb_map node_id node_id)

namespace tree

meta def singleton (n : node) : tree :=
{ nodes := rb_map.of_list [(node_id.zero, n)],
  parents := rb_map.mk _ _ }

meta def contains (id : node_id) (t : tree) : bool :=
t.nodes.contains id

meta def get (id : node_id) (t : tree) : option node :=
t.nodes.find id

meta def get' (id : node_id) (err_prefix : format) (t : tree) : tactic node :=
match t.get id with
| some n := pure n
| none := fail $ err_prefix ++ format! "node {id} not found"
end

meta def get_parent_id (id : node_id) (t : tree) : option node_id :=
t.parents.find id

meta def get_parent (id : node_id) (t : tree) : option (node_id × node) := do
  pid ← t.get_parent_id id,
  p ← t.get pid,
  pure (pid, p)

meta def get_ancestor_ids : node_id → tree → list node_id := λ id t,
match t.get_parent_id id with
| none := []
| some parent := parent :: get_ancestor_ids parent t
end

meta def get_ancestors : node_id → tree → list (node_id × node) := λ id t,
match t.get_parent id with
| none := []
| some p@(parent_id, _) := p :: get_ancestors parent_id t
end

meta def insert (id : node_id) (n : node) (parent : node_id) (t : tree) : tree :=
{ nodes := t.nodes.insert id n,
  parents := t.parents.insert id parent }

/- If the node ID doesn't exist yet, it is added. -/
meta def replace (id : node_id) (n : node) (t : tree) : tree :=
{ nodes := t.nodes.insert id n, ..t }

meta def rule_application_is_proven (r : rule_application) (t : tree) : bool :=
r.subgoals.all $ λ id, (node.is_proven <$> t.get id).get_or_else ff

meta def rule_application_is_unprovable (r : rule_application) (t : tree) : bool :=
r.subgoals.any $ λ id, (node.is_unprovable <$> t.get id).get_or_else tt

meta def propagate_proof_core : list (node_id × node) → tree → tree
| [] t := t
| ((id, n) :: ancestors) t :=
  if n.is_proven
    then propagate_proof_core ancestors t
    else
      match n.active.find_and_remove (λ r, rule_application_is_proven r t) with
      | some (r, active) :=
        let t := t.replace id { proof := r, active := active, ..n } in
        propagate_proof_core ancestors t
      | none := t
      end

meta def propagate_proof (id : node_id) (t : tree) : tree :=
propagate_proof_core (t.get_ancestors id) t

meta def propagate_unprovability_core :
  rb_set node_id → node_id → tree → tree × rb_set node_id :=
λ unprovable_nodes id t,
let recurse_into_parent : rb_set node_id → tree → tree × rb_set node_id :=
  λ unprovable t,
  let unprovable := unprovable.insert id in
  match t.get_parent id with
  | some (parent, _) :=
    propagate_unprovability_core unprovable parent t
  | none := (t, unprovable)
  end in
match t.get id with
| none := (t, unprovable_nodes)
| some n :=
  let (unprovable, active) :=
    n.active.partition $ λ r, rule_application_is_unprovable r t in
  let n := { active := active, unprovable := n.unprovable ++ unprovable, ..n } in
  let t := t.replace id n in
  if n.is_unprovable
    then
      let unprovable_nodes := unprovable_nodes.insert id in
      match t.get_parent id with
      | some (parent, _) := propagate_unprovability_core unprovable_nodes parent t
      | none := (t, unprovable_nodes)
      end
    else
      (t, unprovable_nodes)
end

meta def propagate_unprovability : node_id → tree → tree × rb_set node_id :=
propagate_unprovability_core (rb_map.mk _ _)

meta def root_node_is_proven (t : tree) : bool :=
(node.is_proven <$> (t.get node_id.zero)).get_or_else ff

meta def root_node_is_unprovable (t : tree) : bool :=
(node.is_unprovable <$> (t.get node_id.zero)).get_or_else ff

private meta def link_proofs_core : node_id → tree → tactic unit := λ id t, do
  (some n) ← pure $ t.get id
    | fail! "auto/link_proofs: internal error: no node with ID {id}",
  (some p) ← pure $ n.proof
    | fail! "auto/link_proofs: internal error: node {id} not proven",
  p.subgoals.mmap' $ λ subgoal_id, link_proofs_core subgoal_id t,
  unify n.goal p.proof <|> fail!
    "auto/link_proofs: internal error: proof of node {id} did not unify with the node goal"

/- Can only be used ONCE after the root node has been proven. -/
meta def link_proofs : tree → tactic unit :=
link_proofs_core node_id.zero

/- Only use this after you've called `link_proofs`. -/
meta def extract_proof (t : tree) : tactic expr := do
  (some n) ← pure $ t.get node_id.zero
    | fail "auto/extract_proof: internal error: root node does not exist",
  instantiate_mvars n.goal

meta def format_node (id : node_id) (n : node) (parent : option node_id) :
  tactic format := do
  n ← pp n,
  pure $ format.join
    [ "node " ++ to_fmt id,
      format.nested 2 $ format! "parent: {parent}\n{n}"]

protected meta def to_tactic_format (t : tree) : tactic format :=
format.unlines <$> t.nodes.to_list.mmap
  (λ ⟨id, n⟩, format_node id n (t.get_parent_id id))

meta instance : has_to_tactic_format tree :=
⟨tree.to_tactic_format⟩

end tree

meta structure unexpanded_node :=
(parent : node_id)
(rule : rule)

namespace unexpanded_node

protected meta def lt (n m : unexpanded_node) : bool :=
n.rule.penalty < m.rule.penalty

protected meta def to_fmt (n : unexpanded_node) : format :=
"for node " ++ n.parent.to_fmt ++ ": " ++ n.rule.to_fmt

meta instance : has_to_format unexpanded_node :=
⟨unexpanded_node.to_fmt⟩

end unexpanded_node

meta structure state :=
(search_tree : tree)
(next_id : node_id)
(unexpanded_nodes : priority_queue unexpanded_node unexpanded_node.lt)

namespace state

protected meta def to_tactic_format (s : state) : tactic format := do
  t ← pp s.search_tree,
  let unexpanded :=
    format.unlines $ s.unexpanded_nodes.to_list.map unexpanded_node.to_fmt,
  pure $ format.join
    [ "search tree:"
    , format.nested 2 t
    , format.line
    , "unexpanded nodes:"
    , format.nested 2 unexpanded
    ]

meta instance : has_to_tactic_format state :=
⟨state.to_tactic_format⟩

end state

meta def initial_state (rs : rule_set) : tactic state := do
  rules ← rs.applicable_rules,
  let num_rules_todo := rules.length,
  let unexpanded_nodes : priority_queue unexpanded_node unexpanded_node.lt :=
    priority_queue.from_list $ rules.map $ λ r,
      { parent := node_id.zero, rule := r },
  goal ← get_goal,
  pure
    { search_tree := tree.singleton (node.initial goal num_rules_todo),
      next_id := node_id.one,
      unexpanded_nodes := unexpanded_nodes }

meta def run_rule (goal : expr) (r : rule) : tactic (option (expr × list expr)) :=
with_local_goals' [goal] $ do
  tgt ← target,
  goal' ← mk_meta_var tgt,
  set_goals [goal'],
  try_core $ do
    r.tac,
    subgoals ← get_goals,
    pure (goal', subgoals)

meta def select_rules (rs : rule_set) (id : node_id) (goal : expr) :
  tactic (list unexpanded_node) := do
  rules ← with_local_goals' [goal] $ rs.applicable_rules,
  pure $ rules.map $ λ r, { parent := id, rule := r }

meta def make_node (rs : rule_set) (s : state) (goal : expr) (parent : node_id) :
  tactic (node_id × state) := do
  let id := s.next_id,
  unexpanded_nodes ← select_rules rs id goal,
  let node := node.initial goal unexpanded_nodes.length,
  let s : state :=
    { next_id := id.succ,
      unexpanded_nodes := s.unexpanded_nodes.insert_list unexpanded_nodes,
      search_tree := s.search_tree.insert id node parent },
  pure (id, s)

meta def make_nodes (rs : rule_set) (s : state) (goals : list expr)
  (parent : node_id) : tactic (list node_id × state) :=
goals.mfoldl
  (λ ⟨ids, s⟩ goal, do
    (id, s) ← make_node rs s goal parent,
    pure (id :: ids, s))
  ([], s)

meta def prune_unexpanded_nodes (parents : rb_set node_id) (s : state) : state :=
let unexpanded_nodes :=
  s.unexpanded_nodes.filter (λ n, parents.contains n.parent) in
{ unexpanded_nodes := unexpanded_nodes, ..s }

meta def expand_node (rs : rule_set) (s : state) (n : unexpanded_node) :
  tactic state := do
  let t := s.search_tree,
  let parent_id := n.parent,
  let rule := n.rule,
  (some parent) ← pure $ t.get parent_id
    | fail "auto/expand_node: internal error: parent of unexpanded node not found",
  rule_result ← run_rule parent.goal rule,
  let parent := { num_rules_todo := parent.num_rules_todo - 1, ..parent },
  s ← match rule_result with
      | some (prf, []) := do
          -- Rule succeeded and did not generate subgoals, meaning the parent
          -- node is proven.
          -- 1. Record the proof.
          let rule_app : rule_application :=
            { applied_rule := rule, proof := prf, subgoals := [] },
          let parent := parent.set_proof rule_app,
          -- 2. Potentially mark ancestor nodes as proven.
          let t :=
            (t.replace parent_id parent).propagate_proof parent_id,
          pure { search_tree := t, ..s }
      | some (prf, subgoals) := do
          -- Rule succeeded and generated subgoals.
          -- 1. Make nodes for the subgoals.
          (subgoal_nodes, s) ← make_nodes rs s subgoals parent_id,
          -- 2. Add an active rule application with the generated subgoals.
          let rule_app : rule_application :=
            { applied_rule := rule, proof := prf, subgoals := subgoal_nodes },
          let parent := { active := rule_app :: parent.active, ..parent },
          let t := s.search_tree.replace parent_id parent,
          pure { search_tree := t, ..s }
      | none := do
          -- Rule did not succeed.
          -- 1. Record rule failure.
          let parent := { failed := n.rule :: parent.failed, ..parent},
          let t := s.search_tree.replace parent_id parent,
          -- 2. Mark nodes which have become unprovable.
          -- TODO When a node becomes unprovable, its siblings become irrelevant.
          -- We should check whether a rule belongs to a proven or irrelevant
          -- node when we apply the rule. That's easier than removing exactly
          -- the right unexpanded nodes.
          let (t, _) := t.propagate_unprovability parent_id,
          pure { search_tree := t, ..s }
      end,
  trace "---------------------------------------------------------------------",
  trace s,
  pure s

meta def expand (rs : rule_set) (s : state) : tactic (option state) := do
  trace "=====================================================================",
  trace s,
  some (to_expand, unexpanded_nodes) ← pure s.unexpanded_nodes.pop_min
    | pure none,
  let s := { unexpanded_nodes := unexpanded_nodes, ..s },
  (some parent) ← pure $ s.search_tree.get to_expand.parent
    | fail "auto/expand: internal error: parent of unexpanded node not found",
  if parent.is_proven
    then pure (some s)
    else some <$> expand_node rs s to_expand

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
      | fail "auto: failed to prove the goal",
    search_loop s

meta def search (rs : rule_set) : tactic unit :=
initial_state rs >>= search_loop rs

meta def auto : tactic unit :=
attr.registered_rule_set >>= search

/-
TODO

- Purge unexpanded nodes if a sibling rule is proven: it's unnecessary to
  explore these rules then. (Sibling rules have an OR relationship.)
- purge subgoals (and their unexpanded nodes) if a sibling goal is unprovable.
  The parent rule is then unprovable and the siblings don't need to be explored
  further. (Sibling goals have an AND relationship.)
- Instead of actually removing these from unexpanded_nodes, we should check
  whenever we're popping an unexpanded node. Makes the whole thing less horrible.
-/

end auto
end tactic

/-!
## Tests
-/

open tactic.auto

inductive Even : ℕ → Prop
| zero : Even 0
| plus_two {n} : Even n → Even (n + 2)

attribute [auto] Even.zero Even.plus_two

example : Even 6 := by auto
