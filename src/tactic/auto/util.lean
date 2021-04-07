/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.core

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

def minimum_by₁ {α} (lt : α → α → Prop) [decidable_rel lt] (a : α)
  (as : list α) : α :=
as.foldl (λ a a', if lt a' a then a' else a) a

def minimum_by {α} (lt : α → α → Prop) [decidable_rel lt] : list α → option α
| [] := none
| (a :: as) := some $ minimum_by₁ lt a as

def minimum' {α} [has_lt α] [decidable_rel ((<) : α → α → Prop)] :
  list α → option α :=
minimum_by (<)

def minimum₁ {α} [has_lt α] [decidable_rel ((<) : α → α → Prop)] :
  α → list α → α :=
minimum_by₁ (<)

end list

namespace native
namespace rb_lmap

meta def insert_list {α β} (m : rb_lmap α β) (a : α) (bs : list β) : rb_lmap α β :=
match rb_map.find m a with
| none := rb_map.insert m a bs
| some bs' := rb_map.insert m a (bs ++ bs')
end

end rb_lmap
end native

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

namespace expr

meta def format_goal : expr → tactic format :=
format.of_goal

meta def set_pretty_name {elab} (n : name) : expr elab → expr elab
| (mvar unique _ type) := mvar unique n type
| (local_const unique _ bi type) := local_const unique n bi type
| (lam _ bi type body) := lam n bi type body
| (pi _ bi type body) := pi n bi type body
| (elet _ type assignment body) := elet n type assignment body
| e := e

end expr

namespace lean
namespace parser

meta def small_int : parser ℤ := do
  negate ← succeeds $ tk "-",
  n ← small_nat,
  if negate
    then
      if n = 0 then pure 0 else pure $ int.neg_succ_of_nat (n - 1)
    else
      pure n

end parser
end lean
