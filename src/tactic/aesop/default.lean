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

export aesop (aesop)

namespace interactive

open interactive (parse)

meta def aesop : parse aesop.config.parser → tactic unit :=
tactic.aesop.aesop

end interactive
end tactic
