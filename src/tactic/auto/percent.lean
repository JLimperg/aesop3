/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.core

namespace tactic.auto

/-
Invariant: between 0 and 100
-/
@[derive has_reflect]
structure percent :=
(to_nat : ℕ)

namespace percent

protected def of_nat (n : ℕ) : option percent :=
if n <= 100 then some ⟨n⟩ else none

protected def mul (p q : percent) : percent :=
⟨max 1 ((p.to_nat * q.to_nat) / 100)⟩

instance : has_mul percent :=
⟨percent.mul⟩

protected def lt (p q : percent) : Prop :=
p.to_nat < q.to_nat

instance : has_lt percent :=
⟨percent.lt⟩

instance : decidable_rel ((<) : percent → percent → Prop) :=
λ p q, (infer_instance : decidable (p.to_nat < q.to_nat))

protected def to_string (p : percent) : string :=
to_string p.to_nat ++ "%"

instance : has_to_string percent :=
⟨percent.to_string⟩

protected meta def to_fmt (p : percent) : format :=
p.to_string

meta instance : has_to_format percent :=
⟨percent.to_fmt⟩

open lean
open lean.parser

meta def parser : parser percent := do
  n ← small_nat <|> interaction_monad.fail "expected number between 0 and 100",
  match percent.of_nat n with
  | some p := pure p
  | none := interaction_monad.fail $ format!
      "expected number between 0 and 100 but got: {n}"
  end

end percent
end tactic.auto
