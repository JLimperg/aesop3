/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.aesop

inductive Even : ℕ → Prop
| zero : Even 0
| plus_two {n} : Even n → Even (n + 2)

inductive Odd : ℕ → Prop
| one : Odd 1
| plus_two {n} : Odd n → Odd (n + 2)

inductive EvenOrOdd : ℕ → Prop
| even {n} : Even n → EvenOrOdd n
| odd {n} : Odd n → EvenOrOdd n

attribute [aesop safe 0] EvenOrOdd.even
attribute [aesop  50] EvenOrOdd.odd
attribute [aesop 100] Even.zero Even.plus_two Odd.one

def even_or_odd (n : ℕ) : Prop := EvenOrOdd n

lemma even_or_odd_def {n} : even_or_odd n = EvenOrOdd n := rfl

meta def test_norm_tactic : tactic unit := `[try { rw [even_or_odd_def] at * }]

meta def test_regular_tactic : tactic unit := `[apply Odd.plus_two]

set_option trace.aesop.steps true

example : even_or_odd 3 :=
by aesop unsafe_rules: [test_regular_tactic 50], norm: [test_norm_tactic]

example : even_or_odd 2 :=
by aesop unsafe_rules: [test_regular_tactic 50], norm: [test_norm_tactic]
