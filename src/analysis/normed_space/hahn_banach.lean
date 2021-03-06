/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import analysis.normed_space.operator_norm
import analysis.normed_space.extend
import analysis.convex.cone
import data.complex.is_R_or_C

/-!
# Hahn-Banach theorem

In this file we prove a version of Hahn-Banach theorem for continuous linear
functions on normed spaces over `β` and `β`.

In order to state and prove its corollaries uniformly, we prove the statements for a field `π`
satisfying `is_R_or_C π`.

In this setting, `exists_dual_vector` states that, for any nonzero `x`, there exists a continuous
linear form `g` of norm `1` with `g x = β₯xβ₯` (where the norm has to be interpreted as an element
of `π`).

-/

universes u v

/--
The norm of `x` as an element of `π` (a normed algebra over `β`). This is needed in particular to
state equalities of the form `g x = norm' π x` when `g` is a linear function.

For the concrete cases of `β` and `β`, this is just `β₯xβ₯` and `ββ₯xβ₯`, respectively.
-/
noncomputable def norm' (π : Type*) [nondiscrete_normed_field π] [semi_normed_algebra β π]
  {E : Type*} [semi_normed_group E] (x : E) : π :=
algebra_map β π β₯xβ₯

lemma norm'_def (π : Type*) [nondiscrete_normed_field π] [semi_normed_algebra β π]
  {E : Type*} [semi_normed_group E] (x : E) :
  norm' π x = (algebra_map β π β₯xβ₯) := rfl

lemma norm_norm'
  (π : Type*) [nondiscrete_normed_field π] [semi_normed_algebra β π]
  (A : Type*) [semi_normed_group A]
  (x : A) : β₯norm' π xβ₯ = β₯xβ₯ :=
by rw [norm'_def, norm_algebra_map_eq, norm_norm]

namespace real
variables {E : Type*} [semi_normed_group E] [semi_normed_space β E]

/-- Hahn-Banach theorem for continuous linear functions over `β`. -/
theorem exists_extension_norm_eq (p : subspace β E) (f : p βL[β] β) :
  β g : E βL[β] β, (β x : p, g x = f x) β§ β₯gβ₯ = β₯fβ₯ :=
begin
  rcases exists_extension_of_le_sublinear β¨p, fβ© (Ξ» x, β₯fβ₯ * β₯xβ₯)
    (Ξ» c hc x, by simp only [norm_smul c x, real.norm_eq_abs, abs_of_pos hc, mul_left_comm])
    (Ξ» x y, _) (Ξ» x, le_trans (le_abs_self _) (f.le_op_norm _))
    with β¨g, g_eq, g_leβ©,
  set g' := g.mk_continuous (β₯fβ₯)
    (Ξ» x, abs_le.2 β¨neg_le.1 $ g.map_neg x βΈ norm_neg x βΈ g_le (-x), g_le xβ©),
  { refine β¨g', g_eq, _β©,
    { apply le_antisymm (g.mk_continuous_norm_le (norm_nonneg f) _),
      refine f.op_norm_le_bound (norm_nonneg _) (Ξ» x, _),
      dsimp at g_eq,
      rw β g_eq,
      apply g'.le_op_norm } },
  { simp only [β mul_add],
    exact mul_le_mul_of_nonneg_left (norm_add_le x y) (norm_nonneg f) }
end

end real

section is_R_or_C
open is_R_or_C

variables {π : Type*} [is_R_or_C π] {F : Type*} [semi_normed_group F] [semi_normed_space π F]

/-- Hahn-Banach theorem for continuous linear functions over `π` satisyfing `is_R_or_C π`. -/
theorem exists_extension_norm_eq (p : subspace π F) (f : p βL[π] π) :
  β g : F βL[π] π, (β x : p, g x = f x) β§ β₯gβ₯ = β₯fβ₯ :=
begin
  letI : module β F := restrict_scalars.module β π F,
  letI : is_scalar_tower β π F := restrict_scalars.is_scalar_tower _ _ _,
  letI : semi_normed_space β F := semi_normed_space.restrict_scalars _ π _,
  -- Let `fr: p βL[β] β` be the real part of `f`.
  let fr := re_clm.comp (f.restrict_scalars β),
  have fr_apply : β x, fr x = re (f x), by { assume x, refl },
  -- Use the real version to get a norm-preserving extension of `fr`, which
  -- we'll call `g : F βL[β] β`.
  rcases real.exists_extension_norm_eq (p.restrict_scalars β) fr with β¨g, β¨hextends, hnormeqβ©β©,
  -- Now `g` can be extended to the `F βL[π] π` we need.
  use g.extend_to_π,
  -- It is an extension of `f`.
  have h : β x : p, g.extend_to_π x = f x,
  { assume x,
    rw [continuous_linear_map.extend_to_π_apply, βsubmodule.coe_smul, hextends, hextends],
    have : (fr x : π) - I * β(fr (I β’ x)) = (re (f x) : π) - (I : π) * (re (f ((I : π) β’ x))),
      by refl,
    rw this,
    apply ext,
    { simp only [add_zero, algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add,
        zero_sub, I_im', zero_mul, of_real_re, eq_self_iff_true, sub_zero, mul_neg_eq_neg_mul_symm,
        of_real_neg, mul_re, mul_zero, sub_neg_eq_add, continuous_linear_map.map_smul] },
    { simp only [algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add, zero_sub, I_im',
        zero_mul, of_real_re, mul_neg_eq_neg_mul_symm, mul_im, zero_add, of_real_neg, mul_re,
        sub_neg_eq_add, continuous_linear_map.map_smul] } },
  refine β¨h, _β©,
  -- And we derive the equality of the norms by bounding on both sides.
  refine le_antisymm _ _,
  { calc β₯g.extend_to_πβ₯
        β€ β₯gβ₯ : g.extend_to_π.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
    ... = β₯frβ₯ : hnormeq
    ... β€ β₯re_clmβ₯ * β₯fβ₯ : continuous_linear_map.op_norm_comp_le _ _
    ... = β₯fβ₯ : by rw [re_clm_norm, one_mul] },
  { exact f.op_norm_le_bound g.extend_to_π.op_norm_nonneg (Ξ» x, h x βΈ g.extend_to_π.le_op_norm x) },
end

end is_R_or_C

section dual_vector
variables {π : Type v} [is_R_or_C π]
variables {E : Type u} [normed_group E] [normed_space π E]

open continuous_linear_equiv submodule
open_locale classical

lemma coord_norm' (x : E) (h : x β  0) : β₯norm' π x β’ coord π x hβ₯ = 1 :=
by rw [norm_smul, norm_norm', coord_norm, mul_inv_cancel (mt norm_eq_zero.mp h)]

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm `1`, whose value on `x` is `β₯xβ₯`. -/
theorem exists_dual_vector (x : E) (h : x β  0) : β g : E βL[π] π, β₯gβ₯ = 1 β§ g x = norm' π x :=
begin
  let p : submodule π E := π β x,
  let f := norm' π x β’ coord π x h,
  obtain β¨g, hgβ© := exists_extension_norm_eq p f,
  use g, split,
  { rw [hg.2, coord_norm'] },
  { calc g x = g (β¨x, mem_span_singleton_self xβ© : π β x) : by rw coe_mk
    ... = (norm' π x β’ coord π x h) (β¨x, mem_span_singleton_self xβ© : π β x) : by rw β hg.1
    ... = norm' π x : by simp }
end

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, and choosing
    the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [nontrivial E] (x : E) :
  β g : E βL[π] π, β₯gβ₯ = 1 β§ g x = norm' π x :=
begin
  by_cases hx : x = 0,
  { obtain β¨y, hyβ© := exists_ne (0 : E),
    obtain β¨g, hgβ© : β g : E βL[π] π, β₯gβ₯ = 1 β§ g y = norm' π y := exists_dual_vector y hy,
    refine β¨g, hg.left, _β©,
    rw [norm'_def, hx, norm_zero, ring_hom.map_zero, continuous_linear_map.map_zero] },
  { exact exists_dual_vector x hx }
end

end dual_vector
