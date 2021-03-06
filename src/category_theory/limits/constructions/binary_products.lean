/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.terminal
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.binary_products

/-!
# Constructing binary product from pullbacks and terminal object.

If a category has pullbacks and a terminal object, then it has binary products.

TODO: provide the dual result.
-/

universes v u

open category_theory category_theory.category category_theory.limits

/-- Any category with pullbacks and terminal object has binary products. -/
-- This is not an instance, as it is not always how one wants to construct binary products!
lemma has_binary_products_of_terminal_and_pullbacks
  (C : Type u) [饾挒 : category.{v} C] [has_terminal C] [has_pullbacks C] :
  has_binary_products C :=
{ has_limit := 位 F, has_limit.mk
  { cone :=
    { X := pullback (terminal.from (F.obj walking_pair.left))
                    (terminal.from (F.obj walking_pair.right)),
      蟺 := discrete.nat_trans (位 x, walking_pair.cases_on x pullback.fst pullback.snd)},
    is_limit :=
    { lift := 位 c, pullback.lift ((c.蟺).app walking_pair.left)
                                  ((c.蟺).app walking_pair.right)
                                  (subsingleton.elim _ _),
      fac' := 位 s c, walking_pair.cases_on c (limit.lift_蟺 _ _) (limit.lift_蟺 _ _),
      uniq' := 位 s m J,
                begin
                  rw [鈫怞, 鈫怞],
                  ext;
                  rw limit.lift_蟺;
                  refl
                end } } }
