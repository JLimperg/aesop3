/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.auto.rule
import tactic.auto.util

namespace tactic
namespace auto

open native

/-! ## Node IDs -/

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

/-! ## Rule Application IDs -/

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

/-! ## Nodes -/

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

/-! ## Rule Applications -/

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
| none := undefined_core $
  (format! "auto/with_node: internal error: node {id} not found").to_string
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
| none := undefined_core $
  (format! "auto/with_rapp: internal error: rule application {id} not found").to_string
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

end auto
end tactic
