/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.aesop.rule
import tactic.aesop.config

open expr

namespace tactic
namespace aesop
namespace default_rule

/-!
# split_hyps

This tactic splits product-like hypotheses into their constituent parts. E.g.
the hypothesis `h : A ∧ B` is split into `h₁ : A` and `h₂ : B`. The tactic works
for `and`, `prod`, `pprod`, `Exists`, `sigma`, `psigma` and `subtype`.
Hypotheses where an `and`, `prod` or `pprod` occurs under leading Π binders are
also supported, so `h : ∀ x, P x ∧ Q x` is split into `h₁ : ∀ x, P x` and
`h₂ : ∀ x, Q x`.

`split_hyps` makes no effort to generate intelligible or consistent names, so
it's not suitable as an interactive tactic in its present state.
-/

@[reducible] meta def splitter := expr → expr → tactic (list expr)

namespace splitter

@[inline]
meta def under_binders (f : expr → expr → list expr) : splitter :=
λ h type, do
  (lcs, conclusion) ← open_pis type,
  let apps := h.mk_app lcs,
  match f conclusion apps with
  | [] := pure []
  | new_conclusions := do
    new_hyps ← new_conclusions.mmap $ λ c, do {
      let h' := c.lambdas lcs,
      n ← get_unused_name h.local_pp_name,
      note n none h'
    },
    try $ clear h,
    pure new_hyps
  end

@[inline]
meta def and : splitter :=
under_binders $ λ conclusion e,
  match conclusion with
  | `(%%p ∧ %%q) :=
    [ `(@and.elim_left %%p %%q %%e),
      `(@and.elim_right %%p %%q %%e) ]
  | _ := []
  end

@[inline]
meta def prod : splitter :=
under_binders $ λ conclusion e,
  match conclusion with
  | (app (app (const ``_root_.prod [u, v]) x) y)  :=
    [ (const ``_root_.prod.fst [u, v]) x y e,
      (const ``_root_.prod.snd [u, v]) x y e ]
  | _ := []
  end

@[inline]
meta def pprod : splitter :=
under_binders $ λ conclusion e,
  match conclusion with
  | (app (app (const ``_root_.pprod [u, v]) x) y)  :=
    [ (const ``_root_.pprod.fst [u, v]) x y e,
      (const ``_root_.pprod.snd [u, v]) x y e ]
  | _ := []
  end

@[inline]
meta def by_cases (type_cond : expr → bool) : splitter := λ h type,
if ¬ type_cond type
  then pure []
  else do
    [(_, new_hyps, _)] ← cases_core h | fail!
      "splitter.by_cases: unexpected cases_core output",
    pure new_hyps

@[inline]
meta def Exists : splitter :=
by_cases $ λ type, type.is_app_of ``_root_.Exists

@[inline]
meta def sigma : splitter :=
by_cases $ λ type, type.is_app_of ``_root_.sigma

@[inline]
meta def psigma : splitter :=
by_cases $ λ type, type.is_app_of ``_root_.psigma

@[inline]
meta def subtype : splitter :=
by_cases $ λ type, type.is_app_of ``_root_.subtype

@[inline]
meta def combine (s t : splitter) : splitter := λ h type, do
  new_hyps ← s h type,
  match new_hyps with
  | [] := t h type
  | _ := pure new_hyps
  end

meta instance : has_append splitter :=
⟨combine⟩

end splitter

meta def split_hyps_with' (s : splitter) : list expr → tactic unit
| [] := pure ()
| hyps := do
  new_hyps ← list.join <$> hyps.mmap (λ h, infer_type h >>= s h),
  split_hyps_with' new_hyps

meta def split_hyps_with (s : splitter) : tactic unit := do
  ctx ← local_context,
  split_hyps_with' s ctx

@[aesop norm 1]
meta def split_hyps : tactic unit :=
split_hyps_with $
  splitter.Exists ++ splitter.subtype ++ splitter.sigma ++ splitter.and ++
  splitter.prod ++ splitter.psigma ++ splitter.pprod

end default_rule

end aesop
end tactic
