/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/

import algebra.pointwise
import analysis.normed_space.basic

/-!
# Seminorms and Local Convexity

This file introduces the following notions, defined for a vector space
over a normed field:

- the subset properties of being `absorbent` and `balanced`,

- a `seminorm`, a function to the reals that is positive-semidefinite,
  absolutely homogeneous, and subadditive.

We prove related properties.

## TODO

Define and show equivalence of two notions of local convexity for a
topological vector space over β or β: that it has a local base of
balanced convex absorbent sets, and that it carries the initial
topology induced by a family of seminorms.

## References
* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]
-/

/-!
### Subset Properties

Absorbent and balanced sets in a vector space over a
nondiscrete normed field.
-/

section

variables
(π : Type*) [nondiscrete_normed_field π]
{E : Type*} [add_comm_group E] [module π E]

open set normed_field
open_locale topological_space

/-- A set `A` absorbs another set `B` if `B` is contained in scaling
`A` by elements of sufficiently large norms. -/
def absorbs (A B : set E) := β r > 0, β a : π, r β€ β₯aβ₯ β B β a β’ A

/-- A set is absorbent if it absorbs every singleton. -/
def absorbent (A : set E) := β x, β r > 0, β a : π, r β€ β₯aβ₯ β x β a β’ A

/-- A set `A` is balanced if `a β’ A` is contained in `A` whenever `a`
has norm no greater than one. -/
def balanced (A : set E) := β a : π, β₯aβ₯ β€ 1 β a β’ A β A

variables {π} (a : π) {A : set E}

/-- A balanced set absorbs itself. -/
lemma balanced.absorbs_self (hA : balanced π A) : absorbs π A A :=
begin
  use [1, zero_lt_one],
  intros a ha x hx,
  rw mem_smul_set_iff_inv_smul_mem,
  { apply hA aβ»ΒΉ,
    { rw norm_inv, exact inv_le_one ha },
    { rw mem_smul_set, use [x, hx] }},
  { rw βnorm_pos_iff, calc 0 < 1 : zero_lt_one ... β€ β₯aβ₯ : ha, }
end

lemma balanced.univ : balanced π (univ : set E) :=
Ξ» a ha, subset_univ _

lemma balanced.union {Aβ Aβ : set E} (hAβ : balanced π Aβ) (hAβ : balanced π Aβ) :
  balanced π (Aβ βͺ Aβ) :=
begin
  intros a ha t ht,
  rw [smul_set_union] at ht,
  exact ht.imp (Ξ» x, hAβ _ ha x) (Ξ» x, hAβ _ ha x),
end

lemma balanced.inter {Aβ Aβ : set E} (hAβ : balanced π Aβ) (hAβ : balanced π Aβ) :
  balanced π (Aβ β© Aβ) :=
begin
  rintro a ha _ β¨x, β¨hxβ, hxββ©, rflβ©,
  exact β¨hAβ _ ha β¨_, hxβ, rflβ©, hAβ _ ha β¨_, hxβ, rflβ©β©,
end

lemma balanced.add {Aβ Aβ : set E} (hAβ : balanced π Aβ) (hAβ : balanced π Aβ) :
  balanced π (Aβ + Aβ) :=
begin
  rintro a ha _ β¨_, β¨x, y, hx, hy, rflβ©, rflβ©,
  rw smul_add,
  exact β¨_, _, hAβ _ ha β¨_, hx, rflβ©, hAβ _ ha β¨_, hy, rflβ©, rflβ©,
end

lemma balanced.smul (hA : balanced π A) : balanced π (a β’ A) :=
begin
  rintro b hb _ β¨_, β¨x, hx, rflβ©, rflβ©,
  exact β¨b β’ x, hA _ hb β¨_, hx, rflβ©, smul_comm _ _ _β©,
end

lemma absorbent_iff_forall_absorbs_singleton :
  absorbent π A β β x, absorbs π A {x} :=
by simp [absorbs, absorbent]

/-!
Properties of balanced and absorbing sets in a topological vector space:
-/
variables [topological_space E] [has_continuous_smul π E]

/-- Every neighbourhood of the origin is absorbent. -/
lemma absorbent_nhds_zero (hA : A β π (0 : E)) : absorbent π A :=
begin
  intro x,
  rcases mem_nhds_sets_iff.mp hA with β¨w, hwβ, hwβ, hwββ©,
  have hc : continuous (Ξ» t : π, t β’ x), from continuous_id.smul continuous_const,
  rcases metric.is_open_iff.mp (hwβ.preimage hc) 0 (by rwa [mem_preimage, zero_smul])
    with β¨r, hrβ, hrββ©,
  have hrβ, from inv_pos.mpr (half_pos hrβ),
  use [(r/2)β»ΒΉ, hrβ],
  intros a haβ,
  have haβ : 0 < β₯aβ₯ := hrβ.trans_le haβ,
  have haβ : a β»ΒΉ β’ x β w,
  { apply hrβ,
    rw [metric.mem_ball, dist_zero_right, norm_inv],
    calc β₯aβ₯β»ΒΉ β€ r/2 : (inv_le (half_pos hrβ) haβ).mp haβ
    ...       < r : half_lt_self hrβ },
  rw [mem_smul_set_iff_inv_smul_mem (norm_pos_iff.mp haβ)],
  exact hwβ haβ,
end

/-- The union of `{0}` with the interior of a balanced set
    is balanced. -/
lemma balanced_zero_union_interior (hA : balanced π A) :
  balanced π ({(0 : E)} βͺ interior A) :=
begin
  intros a ha, by_cases a = 0,
  { rw [h, zero_smul_set],
    exacts [subset_union_left _ _, β¨0, or.inl rflβ©] },
  { rw [βimage_smul, image_union],
    apply union_subset_union,
    { rw [image_singleton, smul_zero] },
    { calc a β’ interior A β interior (a β’ A) : (is_open_map_smul' h).image_interior_subset A
                      ... β interior A       : interior_mono (hA _ ha) } }
end

/-- The interior of a balanced set is balanced if it contains the origin. -/
lemma balanced.interior (hA : balanced π A) (h : (0 : E) β interior A) :
  balanced π (interior A) :=
begin
  rw βsingleton_subset_iff at h,
  rw [βunion_eq_self_of_subset_left h],
  exact balanced_zero_union_interior hA,
end

/-- The closure of a balanced set is balanced. -/
lemma balanced.closure (hA : balanced π A) : balanced π (closure A) :=
assume a ha,
calc _ β closure (a β’ A) : image_closure_subset_closure_image (continuous_id.const_smul _)
...    β _ : closure_mono (hA _ ha)

end

/-!
### Seminorms
-/

/-- A seminorm on a vector space over a normed field is a function to
the reals that is positive semidefinite, positive homogeneous, and
subadditive. -/
structure seminorm (π : Type*) (E : Type*)
  [normed_field π] [add_comm_group E] [module π E] :=
(to_fun    : E β β)
(smul'     : β (a : π) (x : E), to_fun (a β’ x) = β₯aβ₯ * to_fun x)
(triangle' : β x y : E, to_fun (x + y) β€ to_fun x + to_fun y)

variables
{π : Type*} [nondiscrete_normed_field π]
{E : Type*} [add_comm_group E] [module π E]

instance : inhabited (seminorm π E) :=
β¨{ to_fun     := Ξ» _, 0,
   smul'     := Ξ» _ _, (mul_zero _).symm,
   triangle' := Ξ» x y, by rw add_zero }β©

instance : has_coe_to_fun (seminorm π E) := β¨_, Ξ» p, p.to_funβ©

namespace seminorm

variables (p : seminorm π E) (c : π) (x y : E) (r : β)

protected lemma smul : p (c β’ x) = β₯cβ₯ * p x := p.smul' _ _
protected lemma triangle : p (x + y) β€ p x + p y := p.triangle' _ _

@[simp]
protected lemma zero : p 0 = 0 :=
calc p 0 = p ((0 : π) β’ 0) : by rw zero_smul
...      = 0 : by rw [p.smul, norm_zero, zero_mul]

@[simp]
protected lemma neg : p (-x) = p x :=
calc p (-x) = p ((-1 : π) β’ x) : by rw neg_one_smul
...         = p x : by rw [p.smul, norm_neg, norm_one, one_mul]

lemma nonneg : 0 β€ p x :=
have h: 0 β€ 2 * p x, from
calc 0 = p (x + (- x)) : by rw [add_neg_self, p.zero]
...    β€ p x + p (-x)  : p.triangle _ _
...    = 2 * p x : by rw [p.neg, two_mul],
nonneg_of_mul_nonneg_left h zero_lt_two

lemma sub_rev : p (x - y) = p (y - x) :=
by rw [βneg_sub, p.neg]

/-- The ball of radius `r` at `x` with respect to seminorm `p`
    is the set of elements `y` with `p (y - x) < `r`. -/
def ball (p : seminorm π E) (x : E) (r : β) := { y : E | p (y - x) < r }

lemma mem_ball : y β ball p x r β p (y - x) < r :=
iff.rfl

lemma mem_ball_zero : y β ball p 0 r β p y < r :=
by rw [mem_ball, sub_zero]

lemma ball_zero_eq : ball p 0 r = { y : E | p y < r } :=
set.ext $ Ξ» x,by { rw mem_ball_zero, exact iff.rfl }

/-- Seminorm-balls at the origin are balanced. -/
lemma balanced_ball_zero : balanced π (ball p 0 r) :=
begin
  rintro a ha x β¨y, hy, hxβ©,
  rw [mem_ball_zero, βhx, p.smul],
  calc _ β€ p y : mul_le_of_le_one_left (p.nonneg _) ha
  ...    < r   : by rwa mem_ball_zero at hy,
end

-- TODO: convexity and absorbent/balanced sets in vector spaces over β

end seminorm

-- TODO: the minkowski functional, topology induced by family of
-- seminorms, local convexity.
