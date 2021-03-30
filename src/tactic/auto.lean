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

meta def make_apply (e : expr) (penalty : ℕ) : tactic rule :=
pure
  { tac := apply e >> skip,
    penalty := penalty,
    description := format! "apply {e}" }

meta def make_const_apply (n : name) (penalty : ℕ) : tactic rule := do
  n ← resolve_constant n,
  pure
    { tac := mk_const n >>= apply >> skip,
      penalty := penalty,
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

open lean.parser

@[user_attribute]
meta def attr : user_attribute name_set ℕ :=
{ name := `auto,
  descr := "Registers a definition as a rule for the auto tactic.",
  cache_cfg := {
    mk_cache := pure ∘ name_set.of_list,
    dependencies := [] },
  parser := small_nat }

meta def declaration_to_rule (decl : name) (penalty : ℕ) : tactic rule :=
rule.make_const_apply decl penalty

meta def declarations_to_rule_set (decls : name_set) : tactic rule_set :=
rule_set.from_list <$> decls.to_list.mmap (λ decl, do {
  penalty ← attr.get_param decl,
  declaration_to_rule decl penalty
})

meta def registered_rule_set : tactic rule_set :=
attr.get_cache >>= declarations_to_rule_set

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

@[derive decidable_eq]
meta structure rapp_id :=
(to_nat : ℕ)

namespace rapp_id

protected meta def zero : rapp_id :=
⟨0⟩

protected meta def succ : rapp_id → rapp_id
| ⟨n⟩ := ⟨n + 1⟩

protected meta def one : rapp_id :=
⟨1⟩

protected meta def lt (n m : rapp_id) : Prop :=
n.to_nat < m.to_nat

meta instance : has_lt rapp_id :=
⟨rapp_id.lt⟩

-- Surely there's a less annoying way to write this.
meta instance : decidable_rel ((<) : rapp_id → rapp_id → Prop) :=
λ n m, (infer_instance : decidable (n.to_nat < m.to_nat))

protected meta def to_fmt (id : rapp_id) : format :=
_root_.to_fmt id.to_nat

meta instance : has_to_format rapp_id :=
⟨rapp_id.to_fmt⟩

end rapp_id

meta structure node :=
(parent : option rapp_id)
(goal : expr)
(num_rules_todo : ℕ)
(rapps : list rapp_id)
(failed_rapps : list rule)
(is_proven : bool)
(is_unprovable : bool)
(is_irrelevant : bool)

namespace node

protected meta def to_tactic_format (n : node) : tactic format := do
  goal ← format.of_goal n.goal,
  pure $ format.join
    [ format! "parent: {n.parent}\n",
      "goal:",
      format.nested 2 goal,
      format.line,
      format! "number of rules to expand: {n.num_rules_todo}\n",
      format! "is proven: {n.is_proven}\n",
      format! "is unprovable: {n.is_unprovable}\n",
      format! "is irrelevant: {n.is_irrelevant}\n",
      format! "successful rule applications: {n.rapps}\n",
      format! "failed rule applications:",
      format.nested 2 $ format.unlines (n.failed_rapps.map to_fmt) ]

meta instance : has_to_tactic_format node :=
⟨node.to_tactic_format⟩

meta def is_root (n : node) : bool :=
n.parent.is_none

meta def is_unknown (n : node) : bool :=
¬ n.is_proven ∧ ¬ n.is_unprovable

end node

/- Rule application. -/
meta structure rapp :=
(parent : node_id)
(applied_rule : rule)
(proof : expr)
(subgoals : list node_id)
(is_proven : bool)
(is_unprovable : bool)
(is_irrelevant : bool)

namespace rapp

protected meta def to_tactic_format (r : rapp) : tactic format := do
  proof ← pp r.proof,
  pure $ format.join
    [ format! "parent: {r.parent}\n",
      format! "rule: {r.applied_rule}\n",
      format! "is proven: {r.is_proven}\n",
      format! "is unprovable: {r.is_unprovable}\n",
      format! "is irrelevant: {r.is_irrelevant}\n",
      "proof:",
      format.nested 2 proof,
      format.line,
      format! "subgoal nodes: {r.subgoals}" ]

meta instance : has_to_tactic_format rapp :=
⟨rapp.to_tactic_format⟩

end rapp

/-
Invariant: The root node has ID `node_id.zero`.
Invariant: Any `node_id` or `rapp_id` referenced in a `node` or `rapp` in the
tree is contained in `nodes` or `rapps`.
-/
meta structure tree :=
(nodes : rb_map node_id node)
(rapps : rb_map rapp_id rapp)
(next_node_id : node_id)
(next_rapp_id : rapp_id)

namespace tree

meta def empty : tree :=
{ nodes := rb_map.mk _ _,
  rapps := rb_map.mk _ _,
  next_node_id := node_id.zero,
  next_rapp_id := rapp_id.zero }

meta def get_node (id : node_id) (t : tree) : option node :=
t.nodes.find id

meta def get_node' (id : node_id) (err_prefix : format) (t : tree) : tactic node :=
match t.get_node id with
| some n := pure n
| none := fail! "{err_prefix}node {id} not found"
end

/- If the node ID doesn't exist yet, it is added. -/
meta def replace_node (id : node_id) (n : node) (t : tree) : tree :=
{ nodes := t.nodes.insert id n, ..t }

/- If the rapp ID doesn't exist yet, it is added. -/
meta def replace_rapp (rid : rapp_id) (r : rapp) (t : tree) : tree :=
{ rapps := t.rapps.insert rid r, ..t }

meta def with_node' {α} [inhabited α] (id : node_id) (f : node → α) (t : tree) : α :=
match t.get_node id with
| some n := f n
| none := _root_.trace
    (format! "auto/with_node: internal error: node {id} not found").to_string
    (arbitrary α)
end

meta def with_node (id : node_id) (f : node → tree) (t : tree) : tree :=
@with_node' _ ⟨t⟩ id f t

meta def modify_node (id : node_id) (f : node → node) (t : tree) : tree :=
t.with_node id $ λ n, t.replace_node id (f n)

meta def get_rapp (id : rapp_id) (t : tree) : option rapp :=
t.rapps.find id

meta def get_rapp' (id : rapp_id) (err_prefix : format) (t : tree) : tactic rapp :=
match t.get_rapp id with
| some r := pure r
| none := fail! "{err_prefix}node {id} not found"
end

meta def get_rapps (ids : list rapp_id) (t : tree) : list (rapp_id × rapp) :=
ids.filter_map $ λ id, (λ r, (id, r)) <$> t.get_rapp id

meta def with_rapp' {α} [inhabited α] (id : rapp_id) (f : rapp → α) (t : tree) : α :=
match t.get_rapp id with
| some r := f r
| none := _root_.trace
    (format! "auto/with_rapp: internal error: rule application {id} not found").to_string
    (arbitrary α)
end

meta def with_rapp (id : rapp_id) (f : rapp → tree) (t : tree) : tree :=
@with_rapp' _ ⟨t⟩ id f t

meta def modify_rapp (rid : rapp_id) (f : rapp → rapp) (t : tree) : tree :=
t.with_rapp rid $ λ r, t.replace_rapp rid (f r)

meta def insert_node (n : node) (t : tree) :
  node_id × tree :=
let id := t.next_node_id in
let t := { nodes := t.nodes.insert id n, next_node_id := id.succ, ..t} in
match n.parent with
| none := (id, t)
| some parent_id :=
  let t :=
    t.modify_rapp parent_id $ λ parent,
      { subgoals := id :: parent.subgoals, ..parent } in
  (id, t)
end

meta def insert_rapp (r : rapp) (t : tree) : rapp_id × tree :=
let rid := t.next_rapp_id in
let t := { rapps := t.rapps.insert rid r, next_rapp_id := rid.succ, ..t} in
let t := t.modify_node r.parent $ λ parent,
  { rapps := rid :: parent.rapps, ..parent } in
(rid, t)

meta def modify_down (f_node : node_id → node → tree → tree)
  (f_rapp : rapp_id → rapp → tree → tree) : sum node_id rapp_id → tree → tree
| (sum.inl id) t :=
  t.with_node id $ λ n,
    let t := f_node id n t in
    n.rapps.foldl (λ t rid, modify_down (sum.inr rid) t) t
| (sum.inr rid) t :=
  t.with_rapp rid $ λ r,
    let t := f_rapp rid r t in
    r.subgoals.foldl (λ t id, modify_down (sum.inl id) t) t

meta def modify_up (f_node : node_id → node → tree → tree × bool)
  (f_rapp : rapp_id → rapp → tree → tree × bool) :
  sum node_id rapp_id → tree → tree
| (sum.inl id) t :=
  t.with_node id $ λ n,
    let (t, continue) := f_node id n t in
    if continue
      then
        match n.parent with
        | some rid := modify_up (sum.inr rid) t
        | none := t
        end
      else
        t
| (sum.inr rid) t :=
  t.with_rapp rid $ λ r,
    let (t, continue) := f_rapp rid r t in
    if continue
      then modify_up (sum.inl r.parent) t
      else t

meta def set_irrelevant : sum node_id rapp_id → tree → tree :=
modify_down
  (λ id  n t, t.replace_node id  { is_irrelevant := tt, ..n })
  (λ rid r t, t.replace_rapp rid { is_irrelevant := tt, ..r })

meta def set_node_irrelevant (id : node_id) : tree → tree :=
set_irrelevant (sum.inl id)

meta def set_rapp_irrelevant (rid : rapp_id) : tree → tree :=
set_irrelevant (sum.inr rid)

meta def rapp_subgoals_proven (r : rapp) (t : tree) : bool :=
r.subgoals.all $ λ id, t.with_node' id node.is_proven

meta def set_proven : sum node_id rapp_id → tree → tree :=
modify_up
  (λ id  n t, (t.replace_node id { is_proven := tt, ..n }, tt))
  (λ rid r t,
    if ¬ t.rapp_subgoals_proven r
      then (t, ff)
      else
        -- Mark rule application as proven.
        let t := t.replace_rapp rid { is_proven := tt, ..r } in
        -- Mark siblings of the proven rule application (and their descendants)
        -- as irrelevant.
        let t := t.with_node r.parent
          (λ parent,
            let siblings := parent.rapps.filter (λ rid', rid' ≠ rid) in
            siblings.foldl (λ t s, set_rapp_irrelevant s t) t) in
        (t, tt))

meta def set_node_proven (id : node_id) : tree → tree :=
set_proven (sum.inl id)

meta def set_rapp_proven (rid : rapp_id) : tree → tree :=
set_proven (sum.inr rid)

meta def node_has_provable_rapp (n : node) (t : tree) : bool :=
n.rapps.any $ λ id, t.with_rapp' id $ λ r, ¬ r.is_unprovable

meta def set_unprovable : sum node_id rapp_id → tree → tree :=
modify_up
  (λ id n t,
    if t.node_has_provable_rapp n ∨ n.num_rules_todo > 0
      then (t, ff)
      else
        -- Mark node as unprovable.
        let t := t.replace_node id { is_unprovable := tt, ..n } in
        -- Mark siblings of the unprovable node (and their descendants)
        -- as irrelevant.
        match n.parent with
        | none := (t, ff)
        | some parent_rid :=
          let t := t.with_rapp parent_rid
            (λ parent,
              let siblings := parent.subgoals.filter (λ id', id' ≠ id) in
              siblings.foldl (λ t s, set_node_irrelevant s t) t) in
          (t, tt)
        end)
  (λ rid r t, (t.replace_rapp rid { is_unprovable := tt, ..r }, tt))

meta def set_node_unprovable (id : node_id) : tree → tree :=
set_unprovable (sum.inl id)

meta def set_rapp_unprovable (rid : rapp_id) : tree → tree :=
set_unprovable (sum.inr rid)

meta def root_node_is_proven (t : tree) : bool :=
t.with_node' node_id.zero node.is_proven

meta def root_node_is_unprovable (t : tree) : bool :=
t.with_node' node_id.zero node.is_unprovable

meta def find_proven_rapp (rapps : list rapp_id) (t : tree) : option (rapp_id × rapp) :=
(t.get_rapps rapps).find $ λ p, p.snd.is_proven

private meta def link_proofs_core : node_id → tree → tactic unit := λ id t, do
  n ← t.get_node' id "auto/link_proofs: internal error: ",
  (some (rid, r)) ← pure $ t.find_proven_rapp n.rapps
    | fail! "auto/link_proofs: internal error: node {id} not proven",
  r.subgoals.mmap' $ λ subgoal, link_proofs_core subgoal t,
  unify n.goal r.proof <|> fail!
    "auto/link_proofs: internal error: proof of rule application {rid} did not unify with the goal of its parent node {id}"

/- Can only be used ONCE after the root node has been proven. -/
meta def link_proofs : tree → tactic unit :=
link_proofs_core node_id.zero

/- Only use this after you've called `link_proofs`. -/
meta def extract_proof (t : tree) : tactic expr := do
  n ← t.get_node' node_id.zero
    "auto/extract_proof: internal error: ",
  instantiate_mvars n.goal

meta def format_node (id : node_id) (n : node) : tactic format := do
  n ← pp n,
  pure $ format.join
    [ "node " ++ to_fmt id,
      format.nested 2 n ]

meta def format_rapp (rid : rapp_id) (r : rapp) : tactic format := do
  r ← pp r,
  pure $ format.join
    [ "rule application " ++ to_fmt rid,
      format.nested 2 r ]

protected meta def to_tactic_format (t : tree) : tactic format := do
  nodes ← t.nodes.to_list.mmap (function.uncurry format_node),
  rapps ← t.rapps.to_list.mmap (function.uncurry format_rapp),
  pure $ format.unlines $ nodes ++ rapps

meta instance : has_to_tactic_format tree :=
⟨tree.to_tactic_format⟩

end tree

meta structure unexpanded_rapp :=
(parent : node_id)
(rule : rule)

namespace unexpanded_rapp

protected meta def lt (n m : unexpanded_rapp) : bool :=
n.rule.penalty < m.rule.penalty

protected meta def to_fmt (n : unexpanded_rapp) : format :=
"for node " ++ n.parent.to_fmt ++ ": " ++ n.rule.to_fmt

meta instance : has_to_format unexpanded_rapp :=
⟨unexpanded_rapp.to_fmt⟩

end unexpanded_rapp

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

meta def select_rules (rs : rule_set) (id : node_id) (goal : expr) :
  tactic (list unexpanded_rapp) := do
  rules ← with_local_goals' [goal] $ rs.applicable_rules,
  pure $ rules.map $ λ r, { parent := id, rule := r }

meta def add_node (rs : rule_set) (s : state) (goal : expr)
  (parent : option rapp_id) : tactic (node_id × state) := do
  let n : node :=
    { parent := parent,
      goal := goal,
      num_rules_todo := 0,
      rapps := [],
      failed_rapps := [],
      is_proven := ff,
      is_unprovable := ff,
      is_irrelevant := ff },
  let (id, t) := s.search_tree.insert_node n,
  unexpanded_rapps ← select_rules rs id goal,
  let t := t.modify_node id $ λ n,
    { num_rules_todo := unexpanded_rapps.length, ..n },
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
          -- 2. Add an active rule application with the generated subgoals.
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
end tactic

/-!
## Tests
-/

open tactic.auto

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
