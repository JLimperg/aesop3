/-
Copyright Β© 2020 NicolΓ² Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NicolΓ² Cavalleri
-/
import geometry.manifold.algebra.lie_group

/-!
# Smooth structures

In this file we define smooth structures that build on Lie groups. We prefer using the term smooth
instead of Lie mainly because Lie ring has currently another use in mathematics.
-/

open_locale manifold

section smooth_ring
variables {π : Type*} [nondiscrete_normed_field π]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space π E]

set_option old_structure_cmd true
set_option default_priority 100 -- see Note [default priority]

/-- A smooth semiring is a semiring where addition and multiplication are smooth. -/
-- See note [Design choices about smooth algebraic structures]
class smooth_semiring (I : model_with_corners π E H)
  (R : Type*) [semiring R] [topological_space R] [charted_space H R]
  extends has_smooth_add I R, has_smooth_mul I R : Prop

/-- A smooth ring is a ring where the ring operations are smooth. -/
-- See note [Design choices about smooth algebraic structures]
class smooth_ring (I : model_with_corners π E H)
  (R : Type*) [ring R] [topological_space R] [charted_space H R]
  extends lie_add_group I R, has_smooth_mul I R : Prop

instance smooth_ring.to_smooth_semiring {I : model_with_corners π E H}
  {R : Type*} [ring R] [topological_space R]
  [charted_space H R] [t : smooth_ring I R] :
  smooth_semiring I R := { ..t }

end smooth_ring

instance field_smooth_ring {π : Type*} [nondiscrete_normed_field π] :
  smooth_ring π(π) π :=
{ smooth_mul :=
  begin
    rw smooth_iff,
    refine β¨continuous_mul, Ξ» x y, _β©,
    simp only [prod.mk.eta] with mfld_simps,
    rw times_cont_diff_on_univ,
    exact times_cont_diff_mul,
  end,
  ..normed_space_lie_add_group }

variables {π R E H : Type*} [topological_space R] [topological_space H]
  [nondiscrete_normed_field π] [normed_group E] [normed_space π E]
  [charted_space H R] (I : model_with_corners π E H)

/-- A smooth semiring is a topological semiring. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
lemma topological_semiring_of_smooth [semiring R] [smooth_semiring I R] :
  topological_semiring R :=
{ .. has_continuous_mul_of_smooth I, .. has_continuous_add_of_smooth I }

/-- A smooth ring is a topological ring. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
lemma topological_ring_of_smooth [ring R] [smooth_ring I R] :
  topological_ring R :=
{ .. has_continuous_mul_of_smooth I, .. topological_add_group_of_lie_add_group I }

