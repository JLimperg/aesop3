/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.aesop.util

structure priority_queue (α : Type*) (lt : α → α → bool) :=
(queue : list α)

namespace priority_queue

variables {α : Type*} {lt : α → α → bool}

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

protected meta def to_fmt [has_to_format α] (p : priority_queue α lt) : format :=
_root_.to_fmt p.queue

meta instance [has_to_format α] : has_to_format (priority_queue α lt) :=
⟨priority_queue.to_fmt⟩

protected meta def pp [has_to_tactic_format α] (p : priority_queue α lt) :
  tactic format :=
tactic.pp p.queue

meta instance [has_to_tactic_format α] :
  has_to_tactic_format (priority_queue α lt) :=
⟨priority_queue.pp⟩

meta def to_fmt_lines [has_to_format α] (p : priority_queue α lt) : format :=
format.unlines $ p.queue.map _root_.to_fmt

meta def pp_lines [has_to_tactic_format α] (p : priority_queue α lt) :
  tactic format :=
format.unlines <$> p.queue.mmap tactic.pp

end priority_queue
