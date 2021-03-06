/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.instances.sphere

/-!
# The circle

This file defines `circle` to be the metric sphere (`metric.sphere`) in `β` centred at `0` of
radius `1`.  We equip it with the following structure:

* a submonoid of `β`
* a group
* a topological group
* a charted space with model space `euclidean_space β (fin 1)` (inherited from `metric.sphere`)
* a Lie group with model with corners `π‘ 1`

We furthermore define `exp_map_circle` to be the natural map `Ξ» t, exp (t * I)` from `β` to
`circle`, and show that this map is a group homomorphism and is smooth.

## Implementation notes

To borrow the smooth manifold structure cleanly, the circle needs to be defined using
`metric.sphere`, and therefore the underlying set is `{z : β | abs (z - 0) = 1}`.  This prevents
certain algebraic facts from working definitionally -- for example, the circle is not defeq to
`{z : β | abs z = 1}`, which is the kernel of `complex.abs` considered as a homomorphism from `β`
to `β`, nor is it defeq to `{z : β | norm_sq z = 1}`, which is the kernel of the homomorphism
`complex.norm_sq` from `β` to `β`.

-/

noncomputable theory

open complex finite_dimensional metric
open_locale manifold

local attribute [instance] finrank_real_complex_fact

/-- The unit circle in `β`, here given the structure of a submonoid of `β`. -/
def circle : submonoid β :=
{ carrier := sphere (0:β) 1,
  one_mem' := by simp,
  mul_mem' := Ξ» a b, begin
    simp only [norm_eq_abs, mem_sphere_zero_iff_norm],
    intros ha hb,
    simp [ha, hb],
  end }

@[simp] lemma mem_circle_iff_abs (z : β) : z β circle β abs z = 1 := mem_sphere_zero_iff_norm

lemma circle_def : βcircle = {z : β | abs z = 1} := by { ext, simp }

@[simp] lemma abs_eq_of_mem_circle (z : circle) : abs z = 1 := by { convert z.2, simp }

instance : group circle :=
{ inv := Ξ» z, β¨conj z, by simpβ©,
  mul_left_inv := Ξ» z, subtype.ext $ by { simp [has_inv.inv, β norm_sq_eq_conj_mul_self,
    β mul_self_abs] },
  .. circle.to_monoid }

@[simp] lemma coe_inv_circle (z : circle) : β(zβ»ΒΉ) = conj z := rfl
@[simp] lemma coe_div_circle (z w : circle) : β(z / w) = βz * conj w := rfl

-- the following result could instead be deduced from the Lie group structure on the circle using
-- `topological_group_of_lie_group`, but that seems a little awkward since one has to first provide
-- and then forget the model space
instance : topological_group circle :=
{ continuous_mul := let h : continuous (Ξ» x : circle, (x : β)) := continuous_subtype_coe in
    continuous_induced_rng (continuous_mul.comp (h.prod_map h)),
  continuous_inv := continuous_induced_rng $
    complex.conj_clm.continuous.comp continuous_subtype_coe }

/-- The unit circle in `β` is a charted space modelled on `euclidean_space β (fin 1)`.  This
follows by definition from the corresponding result for `metric.sphere`. -/
instance : charted_space (euclidean_space β (fin 1)) circle := metric.sphere.charted_space

instance : smooth_manifold_with_corners (π‘ 1) circle :=
metric.sphere.smooth_manifold_with_corners

/-- The unit circle in `β` is a Lie group. -/
instance : lie_group (π‘ 1) circle :=
{ smooth_mul := begin
    let c : circle β β := coe,
    have hβ : times_cont_mdiff _ _ _ (prod.map c c) :=
      times_cont_mdiff_coe_sphere.prod_map times_cont_mdiff_coe_sphere,
    have hβ : times_cont_mdiff (π(β, β).prod π(β, β)) π(β, β) β (Ξ» (z : β Γ β), z.fst * z.snd),
    { rw times_cont_mdiff_iff,
      exact β¨continuous_mul, Ξ» x y, (times_cont_diff_mul.restrict_scalars β).times_cont_diff_onβ© },
    exact (hβ.comp hβ).cod_restrict_sphere _,
  end,
  smooth_inv := (complex.conj_clm.times_cont_diff.times_cont_mdiff.comp
    times_cont_mdiff_coe_sphere).cod_restrict_sphere _,
  .. metric.sphere.smooth_manifold_with_corners }

/-- The map `Ξ» t, exp (t * I)` from `β` to the unit circle in `β`. -/
def exp_map_circle (t : β) : circle :=
β¨exp (t * I), by simp [exp_mul_I, abs_cos_add_sin_mul_I]β©

/-- The map `Ξ» t, exp (t * I)` from `β` to the unit circle in `β`, considered as a homomorphism of
groups. -/
def exp_map_circle_hom : β β+ (additive circle) :=
{ to_fun := exp_map_circle,
  map_zero' := by { rw exp_map_circle, convert of_mul_one, simp },
  map_add' := Ξ» x y, show exp_map_circle (x + y) = (exp_map_circle x) * (exp_map_circle y),
    from subtype.ext $ by simp [exp_map_circle, exp_add, add_mul] }

/-- The map `Ξ» t, exp (t * I)` from `β` to the unit circle in `β` is smooth. -/
lemma times_cont_mdiff_exp_map_circle : times_cont_mdiff π(β, β) (π‘ 1) β exp_map_circle :=
(((times_cont_diff_exp.restrict_scalars β).comp
  (times_cont_diff_id.smul times_cont_diff_const)).times_cont_mdiff).cod_restrict_sphere _
