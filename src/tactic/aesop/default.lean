/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.aesop.search

/-!
# Aesop, a general-purpose proof search tactic
-/

namespace tactic

meta def aesop : tactic unit :=
tactic.aesop.aesop

meta def interactive.aesop : tactic unit :=
tactic.aesop.aesop

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

attribute [aesop  50] EvenOrOdd.odd EvenOrOdd.even
attribute [aesop 100] Even.zero Even.plus_two Odd.one

def even_or_odd (n : ℕ) : Prop := EvenOrOdd n

lemma even_or_odd_def {n} : even_or_odd n = EvenOrOdd n := rfl

@[aesop norm 50]
meta def test_norm_tactic : tactic unit := `[try { simp [even_or_odd_def] at * }]

@[aesop 50]
meta def test_regular_tactic : tactic unit := `[apply Odd.plus_two]

set_option trace.aesop.steps true

example : even_or_odd 3 := by aesop
