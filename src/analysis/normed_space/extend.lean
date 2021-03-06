/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/

import data.complex.is_R_or_C

/-!
# Extending a continuous `â`-linear map to a continuous `ð`-linear map

In this file we provide a way to extend a continuous `â`-linear map to a continuous `ð`-linear map
in a way that bounds the norm by the norm of the original map, when `ð` is either `â` (the
extension is trivial) or `â`. We formulate the extension uniformly, by assuming `is_R_or_C ð`.

We motivate the form of the extension as follows. Note that `fc : F ââ[ð] ð` is determined fully by
`Re fc`: for all `x : F`, `fc (I â¢ x) = I * fc x`, so `Im (fc x) = -Re (fc (I â¢ x))`. Therefore,
given an `fr : F ââ[â] â`, we define `fc x = fr x - fr (I â¢ x) * I`.

## Main definitions

* `linear_map.extend_to_ð`
* `continuous_linear_map.extend_to_ð`

## Implementation details

For convenience, the main definitions above operate in terms of `restrict_scalars â ð F`.
Alternate forms which operate on `[is_scalar_tower â ð F]` instead are provided with a primed name.

-/

open is_R_or_C

variables {ð : Type*} [is_R_or_C ð] {F : Type*} [semi_normed_group F] [semi_normed_space ð F]
local notation `absð` := @is_R_or_C.abs ð _

/-- Extend `fr : F ââ[â] â` to `F ââ[ð] ð` in a way that will also be continuous and have its norm
bounded by `â¥frâ¥` if `fr` is continuous. -/
noncomputable def linear_map.extend_to_ð'
  [module â F] [is_scalar_tower â ð F] (fr : F ââ[â] â) : F ââ[ð] ð :=
begin
  let fc : F â ð := Î» x, (fr x : ð) - (I : ð) * (fr ((I : ð) â¢ x)),
  have add : â x y : F, fc (x + y) = fc x + fc y,
  { assume x y,
    simp only [fc],
    unfold_coes,
    simp only [smul_add, ring_hom.map_add, ring_hom.to_fun_eq_coe, linear_map.to_fun_eq_coe,
               linear_map.map_add],
    rw mul_add,
    abel, },
  have A : â (c : â) (x : F), (fr ((c : ð) â¢ x) : ð) = (c : ð) * (fr x : ð),
  { assume c x,
    rw [â of_real_mul],
    congr' 1,
    rw [is_R_or_C.of_real_alg, smul_assoc, fr.map_smul, algebra.id.smul_eq_mul, one_smul] },
  have smul_â : â (c : â) (x : F), fc ((c : ð) â¢ x) = (c : ð) * fc x,
  { assume c x,
    simp only [fc, A],
    rw A c x,
    rw [smul_smul, mul_comm I (c : ð), â smul_smul, A, mul_sub],
    ring },
  have smul_I : â x : F, fc ((I : ð) â¢ x) = (I : ð) * fc x,
  { assume x,
    simp only [fc],
    cases @I_mul_I_ax ð _ with h h, { simp [h] },
    rw [mul_sub, â mul_assoc, smul_smul, h],
    simp only [neg_mul_eq_neg_mul_symm, linear_map.map_neg, one_mul, one_smul,
      mul_neg_eq_neg_mul_symm, of_real_neg, neg_smul, sub_neg_eq_add, add_comm] },
  have smul_ð : â (c : ð) (x : F), fc (c â¢ x) = c â¢ fc x,
  { assume c x,
    rw [â re_add_im c, add_smul, add_smul, add, smul_â, â smul_smul, smul_â, smul_I, â mul_assoc],
    refl },
  exact { to_fun := fc, map_add' := add, map_smul' := smul_ð }
end

lemma linear_map.extend_to_ð'_apply [module â F] [is_scalar_tower â ð F]
  (fr : F ââ[â] â) (x : F) :
  fr.extend_to_ð' x = (fr x : ð) - (I : ð) * fr ((I : ð) â¢ x) := rfl

/-- The norm of the extension is bounded by `â¥frâ¥`. -/
lemma norm_bound [semi_normed_space â F] [is_scalar_tower â ð F] (fr : F âL[â] â) (x : F) :
  â¥(fr.to_linear_map.extend_to_ð' x : ð)â¥ â¤ â¥frâ¥ * â¥xâ¥ :=
begin
  let lm : F ââ[ð] ð := fr.to_linear_map.extend_to_ð',
  -- We aim to find a `t : ð` such that
  -- * `lm (t â¢ x) = fr (t â¢ x)` (so `lm (t â¢ x) = t * lm x â â`)
  -- * `â¥lm xâ¥ = â¥lm (t â¢ x)â¥` (so `t.abs` must be 1)
  -- If `lm x â  0`, `(lm x)â»Â¹` satisfies the first requirement, and after normalizing, it
  -- satisfies the second.
  -- (If `lm x = 0`, the goal is trivial.)
  classical,
  by_cases h : lm x = 0,
  { rw [h, norm_zero],
    apply mul_nonneg; exact norm_nonneg _ },
  let fx := (lm x)â»Â¹,
  let t := fx / (absð fx : ð),
  have ht : absð t = 1, by field_simp [abs_of_real, of_real_inv, is_R_or_C.abs_inv,
    is_R_or_C.abs_div, is_R_or_C.abs_abs, h],
  have h1 : (fr (t â¢ x) : ð) = lm (t â¢ x),
  { apply ext,
    { simp only [lm, of_real_re, linear_map.extend_to_ð'_apply, mul_re, I_re, of_real_im, zero_mul,
        add_monoid_hom.map_sub, sub_zero, mul_zero],
      refl },
    { symmetry,
      calc im (lm (t â¢ x))
          = im (t * lm x) : by rw [lm.map_smul, smul_eq_mul]
      ... = im ((lm x)â»Â¹ / (absð (lm x)â»Â¹) * lm x) : rfl
      ... = im (1 / (absð (lm x)â»Â¹ : ð)) : by rw [div_mul_eq_mul_div, inv_mul_cancel h]
      ... = 0 : by rw [â of_real_one, â of_real_div, of_real_im]
      ... = im (fr (t â¢ x) : ð) : by rw [of_real_im] } },
  calc â¥lm xâ¥ = absð t * â¥lm xâ¥ : by rw [ht, one_mul]
  ... = â¥t * lm xâ¥ : by rw [â norm_eq_abs, normed_field.norm_mul]
  ... = â¥lm (t â¢ x)â¥ : by rw [âsmul_eq_mul, lm.map_smul]
  ... = â¥(fr (t â¢ x) : ð)â¥ : by rw h1
  ... = â¥fr (t â¢ x)â¥ : by rw [norm_eq_abs, abs_of_real, norm_eq_abs, abs_to_real]
  ... â¤ â¥frâ¥ * â¥t â¢ xâ¥ : continuous_linear_map.le_op_norm _ _
  ... = â¥frâ¥ * (â¥tâ¥ * â¥xâ¥) : by rw norm_smul
  ... â¤ â¥frâ¥ * â¥xâ¥ : by rw [norm_eq_abs, ht, one_mul]
end

/-- Extend `fr : F âL[â] â` to `F âL[ð] ð`. -/
noncomputable def continuous_linear_map.extend_to_ð' [semi_normed_space â F] [is_scalar_tower â ð F]
  (fr : F âL[â] â) :
  F âL[ð] ð :=
linear_map.mk_continuous _ (â¥frâ¥) (norm_bound _)

lemma continuous_linear_map.extend_to_ð'_apply [semi_normed_space â F] [is_scalar_tower â ð F]
  (fr : F âL[â] â) (x : F) :
  fr.extend_to_ð' x = (fr x : ð) - (I : ð) * fr ((I : ð) â¢ x) := rfl

/-- Extend `fr : restrict_scalars â ð F ââ[â] â` to `F ââ[ð] ð`. -/
noncomputable def linear_map.extend_to_ð (fr : (restrict_scalars â ð F) ââ[â] â) : F ââ[ð] ð :=
fr.extend_to_ð'

lemma linear_map.extend_to_ð_apply (fr : (restrict_scalars â ð F) ââ[â] â) (x : F) :
  fr.extend_to_ð x = (fr x : ð) - (I : ð) * fr ((I : ð) â¢ x) := rfl

/-- Extend `fr : restrict_scalars â ð F âL[â] â` to `F âL[ð] ð`. -/
noncomputable def continuous_linear_map.extend_to_ð (fr : (restrict_scalars â ð F) âL[â] â) :
  F âL[ð] ð :=
fr.extend_to_ð'

lemma continuous_linear_map.extend_to_ð_apply (fr : (restrict_scalars â ð F) âL[â] â) (x : F) :
  fr.extend_to_ð x = (fr x : ð) - (I : ð) * fr ((I : ð) â¢ x) := rfl
