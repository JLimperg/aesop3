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
