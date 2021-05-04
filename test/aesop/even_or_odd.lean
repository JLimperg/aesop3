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

attribute [aesop  50] EvenOrOdd.even EvenOrOdd.odd
attribute [aesop 100] Even.zero Even.plus_two
-- attribute [aesop 100] Odd.one Odd.plus_two

def even_or_odd (n : ℕ) : Prop := EvenOrOdd n

meta def test_norm_tactic : tactic unit := `[try { rw [even_or_odd] at * }]

set_option trace.aesop.steps true
set_option trace.aesop.tree true

example : even_or_odd 3 :=
by aesop norm_rules: [test_norm_tactic]

example : even_or_odd 2 :=
by aesop norm_rules: [test_norm_tactic]
