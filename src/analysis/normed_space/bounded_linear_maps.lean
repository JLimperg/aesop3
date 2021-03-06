/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes HΓΆlzl

Continuous linear functions -- functions between normed vector spaces which are bounded and linear.
-/
import analysis.normed_space.multilinear

noncomputable theory
open_locale classical big_operators topological_space

open filter (tendsto)
open metric

variables {π : Type*} [nondiscrete_normed_field π]
variables {E : Type*} [normed_group E] [normed_space π E]
variables {F : Type*} [normed_group F] [normed_space π F]
variables {G : Type*} [normed_group G] [normed_space π G]


/-- A function `f` satisfies `is_bounded_linear_map π f` if it is linear and satisfies the
inequality `β₯ f x β₯ β€ M * β₯ x β₯` for some positive constant `M`. -/
structure is_bounded_linear_map (π : Type*) [normed_field π]
  {E : Type*} [normed_group E] [normed_space π E]
  {F : Type*} [normed_group F] [normed_space π F] (f : E β F)
  extends is_linear_map π f : Prop :=
(bound : β M, 0 < M β§ β x : E, β₯ f x β₯ β€ M * β₯ x β₯)

lemma is_linear_map.with_bound
  {f : E β F} (hf : is_linear_map π f) (M : β) (h : β x : E, β₯ f x β₯ β€ M * β₯ x β₯) :
  is_bounded_linear_map π f :=
β¨ hf, classical.by_cases
  (assume : M β€ 0, β¨1, zero_lt_one, assume x,
    le_trans (h x) $ mul_le_mul_of_nonneg_right (le_trans this zero_le_one) (norm_nonneg x)β©)
  (assume : Β¬ M β€ 0, β¨M, lt_of_not_ge this, hβ©)β©

/-- A continuous linear map satisfies `is_bounded_linear_map` -/
lemma continuous_linear_map.is_bounded_linear_map (f : E βL[π] F) : is_bounded_linear_map π f :=
{ bound := f.bound,
  ..f.to_linear_map.is_linear }

namespace is_bounded_linear_map

/-- Construct a linear map from a function `f` satisfying `is_bounded_linear_map π f`. -/
def to_linear_map (f : E β F) (h : is_bounded_linear_map π f) : E ββ[π] F :=
(is_linear_map.mk' _ h.to_is_linear_map)

/-- Construct a continuous linear map from is_bounded_linear_map -/
def to_continuous_linear_map {f : E β F} (hf : is_bounded_linear_map π f) : E βL[π] F :=
{ cont := let β¨C, Cpos, hCβ© := hf.bound in linear_map.continuous_of_bound _ C hC,
  ..to_linear_map f hf}

lemma zero : is_bounded_linear_map π (Ξ» (x:E), (0:F)) :=
(0 : E ββ F).is_linear.with_bound 0 $ by simp [le_refl]

lemma id : is_bounded_linear_map π (Ξ» (x:E), x) :=
linear_map.id.is_linear.with_bound 1 $ by simp [le_refl]

lemma fst : is_bounded_linear_map π (Ξ» x : E Γ F, x.1) :=
begin
  refine (linear_map.fst π E F).is_linear.with_bound 1 (Ξ»x, _),
  rw one_mul,
  exact le_max_left _ _
end

lemma snd : is_bounded_linear_map π (Ξ» x : E Γ F, x.2) :=
begin
  refine (linear_map.snd π E F).is_linear.with_bound 1 (Ξ»x, _),
  rw one_mul,
  exact le_max_right _ _
end

variables { f g : E β F }

lemma smul (c : π) (hf : is_bounded_linear_map π f) :
  is_bounded_linear_map π (Ξ» e, c β’ f e) :=
let β¨hlf, M, hMp, hMβ© := hf in
(c β’ hlf.mk' f).is_linear.with_bound (β₯cβ₯ * M) $ assume x,
  calc β₯c β’ f xβ₯ = β₯cβ₯ * β₯f xβ₯ : norm_smul c (f x)
  ... β€ β₯cβ₯ * (M * β₯xβ₯)        : mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  ... = (β₯cβ₯ * M) * β₯xβ₯        : (mul_assoc _ _ _).symm

lemma neg (hf : is_bounded_linear_map π f) :
  is_bounded_linear_map π (Ξ» e, -f e) :=
begin
  rw show (Ξ» e, -f e) = (Ξ» e, (-1 : π) β’ f e), { funext, simp },
  exact smul (-1) hf
end

lemma add (hf : is_bounded_linear_map π f) (hg : is_bounded_linear_map π g) :
  is_bounded_linear_map π (Ξ» e, f e + g e) :=
let β¨hlf, Mf, hMfp, hMfβ© := hf in
let β¨hlg, Mg, hMgp, hMgβ© := hg in
(hlf.mk' _ + hlg.mk' _).is_linear.with_bound (Mf + Mg) $ assume x,
  calc β₯f x + g xβ₯ β€ Mf * β₯xβ₯ + Mg * β₯xβ₯ : norm_add_le_of_le (hMf x) (hMg x)
               ... β€ (Mf + Mg) * β₯xβ₯     : by rw add_mul

lemma sub (hf : is_bounded_linear_map π f) (hg : is_bounded_linear_map π g) :
  is_bounded_linear_map π (Ξ» e, f e - g e) :=
by simpa [sub_eq_add_neg] using add hf (neg hg)

lemma comp {g : F β G}
  (hg : is_bounded_linear_map π g) (hf : is_bounded_linear_map π f) :
  is_bounded_linear_map π (g β f) :=
(hg.to_continuous_linear_map.comp hf.to_continuous_linear_map).is_bounded_linear_map

protected lemma tendsto (x : E) (hf : is_bounded_linear_map π f) :
  tendsto f (π x) (π (f x)) :=
let β¨hf, M, hMp, hMβ© := hf in
tendsto_iff_norm_tendsto_zero.2 $
  squeeze_zero (assume e, norm_nonneg _)
    (assume e,
      calc β₯f e - f xβ₯ = β₯hf.mk' f (e - x)β₯ : by rw (hf.mk' _).map_sub e x; refl
                   ... β€ M * β₯e - xβ₯        : hM (e - x))
    (suffices tendsto (Ξ» (e : E), M * β₯e - xβ₯) (π x) (π (M * 0)), by simpa,
      tendsto_const_nhds.mul (tendsto_norm_sub_self _))

lemma continuous (hf : is_bounded_linear_map π f) : continuous f :=
continuous_iff_continuous_at.2 $ Ξ» _, hf.tendsto _

lemma lim_zero_bounded_linear_map (hf : is_bounded_linear_map π f) :
  tendsto f (π 0) (π 0) :=
(hf.1.mk' _).map_zero βΈ continuous_iff_continuous_at.1 hf.continuous 0

section
open asymptotics filter

theorem is_O_id {f : E β F} (h : is_bounded_linear_map π f) (l : filter E) :
  is_O f (Ξ» x, x) l :=
let β¨M, hMp, hMβ© := h.bound in is_O.of_bound _ (mem_sets_of_superset univ_mem_sets (Ξ» x _, hM x))

theorem is_O_comp {E : Type*} {g : F β G} (hg : is_bounded_linear_map π g)
  {f : E β F} (l : filter E) : is_O (Ξ» x', g (f x')) f l :=
(hg.is_O_id β€).comp_tendsto le_top

theorem is_O_sub {f : E β F} (h : is_bounded_linear_map π f)
  (l : filter E) (x : E) : is_O (Ξ» x', f (x' - x)) (Ξ» x', x' - x) l :=
is_O_comp h l

end

end is_bounded_linear_map

section
variables {ΞΉ : Type*} [decidable_eq ΞΉ] [fintype ΞΉ]

/-- Taking the cartesian product of two continuous multilinear maps
is a bounded linear operation. -/
lemma is_bounded_linear_map_prod_multilinear
  {E : ΞΉ β Type*} [βi, normed_group (E i)] [βi, normed_space π (E i)] :
  is_bounded_linear_map π
  (Ξ» p : (continuous_multilinear_map π E F) Γ (continuous_multilinear_map π E G), p.1.prod p.2) :=
{ map_add := Ξ» pβ pβ, by { ext1 m, refl },
  map_smul := Ξ» c p, by { ext1 m, refl },
  bound := β¨1, zero_lt_one, Ξ» p, begin
    rw one_mul,
    apply continuous_multilinear_map.op_norm_le_bound _ (norm_nonneg _) (Ξ» m, _),
    rw [continuous_multilinear_map.prod_apply, norm_prod_le_iff],
    split,
    { exact le_trans (p.1.le_op_norm m)
        (mul_le_mul_of_nonneg_right (norm_fst_le p) (finset.prod_nonneg (Ξ» i hi, norm_nonneg _))) },
    { exact le_trans (p.2.le_op_norm m)
        (mul_le_mul_of_nonneg_right (norm_snd_le p) (finset.prod_nonneg (Ξ» i hi, norm_nonneg _))) },
  endβ© }

/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g mβ, ..., g mβ)` is a bounded linear operation. -/
lemma is_bounded_linear_map_continuous_multilinear_map_comp_linear (g : G βL[π] E) :
  is_bounded_linear_map π (Ξ» f : continuous_multilinear_map π (Ξ» (i : ΞΉ), E) F,
    f.comp_continuous_linear_map (Ξ» _, g)) :=
begin
  refine is_linear_map.with_bound β¨Ξ» fβ fβ, by { ext m, refl }, Ξ» c f, by { ext m, refl }β©
    (β₯gβ₯ ^ (fintype.card ΞΉ)) (Ξ» f, _),
  apply continuous_multilinear_map.op_norm_le_bound _ _ (Ξ» m, _),
  { apply_rules [mul_nonneg, pow_nonneg, norm_nonneg] },
  calc β₯f (g β m)β₯ β€
    β₯fβ₯ * β i, β₯g (m i)β₯ : f.le_op_norm _
    ... β€ β₯fβ₯ * β i, (β₯gβ₯ * β₯m iβ₯) : begin
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
      exact finset.prod_le_prod (Ξ» i hi, norm_nonneg _) (Ξ» i hi, g.le_op_norm _)
    end
    ... = β₯gβ₯ ^ fintype.card ΞΉ * β₯fβ₯ * β i, β₯m iβ₯ :
      by { simp [finset.prod_mul_distrib, finset.card_univ], ring }
end

end

section bilinear_map

variable (π)

/-- A map `f : E Γ F β G` satisfies `is_bounded_bilinear_map π f` if it is bilinear and
continuous. -/
structure is_bounded_bilinear_map (f : E Γ F β G) : Prop :=
(add_left   : β(xβ xβ : E) (y : F), f (xβ + xβ, y) = f (xβ, y) + f (xβ, y))
(smul_left  : β(c : π) (x : E) (y : F), f (c β’ x, y) = c β’ f (x,y))
(add_right  : β(x : E) (yβ yβ : F), f (x, yβ + yβ) = f (x, yβ) + f (x, yβ))
(smul_right : β(c : π) (x : E) (y : F), f (x, c β’ y) = c β’ f (x,y))
(bound      : βC>0, β(x : E) (y : F), β₯f (x, y)β₯ β€ C * β₯xβ₯ * β₯yβ₯)

variable {π}
variable {f : E Γ F β G}

lemma continuous_linear_map.is_bounded_bilinear_map (f : E βL[π] F βL[π] G) :
  is_bounded_bilinear_map π (Ξ» x : E Γ F, f x.1 x.2) :=
{ add_left := Ξ» xβ xβ y, by rw [f.map_add, continuous_linear_map.add_apply],
  smul_left := Ξ» c x y, by rw [f.map_smul _, continuous_linear_map.smul_apply],
  add_right := Ξ» x, (f x).map_add,
  smul_right := Ξ» c x y, (f x).map_smul c y,
  bound := β¨max β₯fβ₯ 1, zero_lt_one.trans_le (le_max_right _ _),
    Ξ» x y, (f.le_op_normβ x y).trans $
      by apply_rules [mul_le_mul_of_nonneg_right, norm_nonneg, le_max_left]β© }

protected lemma is_bounded_bilinear_map.is_O (h : is_bounded_bilinear_map π f) :
  asymptotics.is_O f (Ξ» p : E Γ F, β₯p.1β₯ * β₯p.2β₯) β€ :=
let β¨C, Cpos, hCβ© := h.bound in asymptotics.is_O.of_bound _ $
filter.eventually_of_forall $ Ξ» β¨x, yβ©, by simpa [mul_assoc] using hC x y

lemma is_bounded_bilinear_map.is_O_comp {Ξ± : Type*} (H : is_bounded_bilinear_map π f)
  {g : Ξ± β E} {h : Ξ± β F} {l : filter Ξ±} :
  asymptotics.is_O (Ξ» x, f (g x, h x)) (Ξ» x, β₯g xβ₯ * β₯h xβ₯) l :=
H.is_O.comp_tendsto le_top

protected lemma is_bounded_bilinear_map.is_O' (h : is_bounded_bilinear_map π f) :
  asymptotics.is_O f (Ξ» p : E Γ F, β₯pβ₯ * β₯pβ₯) β€ :=
h.is_O.trans (asymptotics.is_O_fst_prod'.norm_norm.mul asymptotics.is_O_snd_prod'.norm_norm)

lemma is_bounded_bilinear_map.map_sub_left (h : is_bounded_bilinear_map π f) {x y : E} {z : F} :
  f (x - y, z) = f (x, z) -  f(y, z) :=
calc f (x - y, z) = f (x + (-1 : π) β’ y, z) : by simp [sub_eq_add_neg]
... = f (x, z) + (-1 : π) β’ f (y, z) : by simp only [h.add_left, h.smul_left]
... = f (x, z) - f (y, z) : by simp [sub_eq_add_neg]

lemma is_bounded_bilinear_map.map_sub_right (h : is_bounded_bilinear_map π f) {x : E} {y z : F} :
  f (x, y - z) = f (x, y) - f (x, z) :=
calc f (x, y - z) = f (x, y + (-1 : π) β’ z) : by simp [sub_eq_add_neg]
... = f (x, y) + (-1 : π) β’ f (x, z) : by simp only [h.add_right, h.smul_right]
... = f (x, y) - f (x, z) : by simp [sub_eq_add_neg]

lemma is_bounded_bilinear_map.is_bounded_linear_map_left (h : is_bounded_bilinear_map π f) (y : F) :
  is_bounded_linear_map π (Ξ» x, f (x, y)) :=
{ map_add  := Ξ» x x', h.add_left _ _ _,
  map_smul := Ξ» c x, h.smul_left _ _ _,
  bound    := begin
    rcases h.bound with β¨C, C_pos, hCβ©,
    refine β¨C * (β₯yβ₯ + 1), mul_pos C_pos (lt_of_lt_of_le (zero_lt_one) (by simp)), Ξ» x, _β©,
    have : β₯yβ₯ β€ β₯yβ₯ + 1, by simp [zero_le_one],
    calc β₯f (x, y)β₯ β€ C * β₯xβ₯ * β₯yβ₯ : hC x y
    ... β€ C * β₯xβ₯ * (β₯yβ₯ + 1) :
      by apply_rules [norm_nonneg, mul_le_mul_of_nonneg_left, le_of_lt C_pos, mul_nonneg]
    ... = C * (β₯yβ₯ + 1) * β₯xβ₯ : by ring
  end }

lemma is_bounded_bilinear_map.is_bounded_linear_map_right
  (h : is_bounded_bilinear_map π f) (x : E) :
  is_bounded_linear_map π (Ξ» y, f (x, y)) :=
{ map_add  := Ξ» y y', h.add_right _ _ _,
  map_smul := Ξ» c y, h.smul_right _ _ _,
  bound    := begin
    rcases h.bound with β¨C, C_pos, hCβ©,
    refine β¨C * (β₯xβ₯ + 1), mul_pos C_pos (lt_of_lt_of_le (zero_lt_one) (by simp)), Ξ» y, _β©,
    have : β₯xβ₯ β€ β₯xβ₯ + 1, by simp [zero_le_one],
    calc β₯f (x, y)β₯ β€ C * β₯xβ₯ * β₯yβ₯ : hC x y
    ... β€ C * (β₯xβ₯ + 1) * β₯yβ₯ :
      by apply_rules [mul_le_mul_of_nonneg_right, norm_nonneg, mul_le_mul_of_nonneg_left,
                      le_of_lt C_pos]
  end }

lemma is_bounded_bilinear_map_smul {π' : Type*} [normed_field π']
  [normed_algebra π π'] {E : Type*} [normed_group E] [normed_space π E] [normed_space π' E]
  [is_scalar_tower π π' E] :
  is_bounded_bilinear_map π (Ξ» (p : π' Γ E), p.1 β’ p.2) :=
{ add_left   := add_smul,
  smul_left  := Ξ» c x y, by simp [smul_assoc],
  add_right  := smul_add,
  smul_right := Ξ» c x y, by simp [smul_assoc, smul_algebra_smul_comm],
  bound      := β¨1, zero_lt_one, Ξ» x y, by simp [norm_smul] β© }

lemma is_bounded_bilinear_map_mul :
  is_bounded_bilinear_map π (Ξ» (p : π Γ π), p.1 * p.2) :=
by simp_rw β smul_eq_mul; exact is_bounded_bilinear_map_smul

lemma is_bounded_bilinear_map_comp :
  is_bounded_bilinear_map π (Ξ»(p : (E βL[π] F) Γ (F βL[π] G)), p.2.comp p.1) :=
{ add_left := Ξ»xβ xβ y, begin
      ext z,
      change y (xβ z + xβ z) = y (xβ z) + y (xβ z),
      rw y.map_add
    end,
  smul_left := Ξ»c x y, begin
      ext z,
      change y (c β’ (x z)) = c β’ y (x z),
      rw continuous_linear_map.map_smul
    end,
  add_right := Ξ»x yβ yβ, rfl,
  smul_right := Ξ»c x y, rfl,
  bound := β¨1, zero_lt_one, Ξ»x y, calc
    β₯continuous_linear_map.comp ((x, y).snd) ((x, y).fst)β₯
      β€ β₯yβ₯ * β₯xβ₯ : continuous_linear_map.op_norm_comp_le _ _
    ... = 1 * β₯xβ₯ * β₯ yβ₯ : by ring β© }

lemma continuous_linear_map.is_bounded_linear_map_comp_left (g : continuous_linear_map π F G) :
  is_bounded_linear_map π (Ξ»(f : E βL[π] F), continuous_linear_map.comp g f) :=
is_bounded_bilinear_map_comp.is_bounded_linear_map_left _

lemma continuous_linear_map.is_bounded_linear_map_comp_right (f : continuous_linear_map π E F) :
  is_bounded_linear_map π (Ξ»(g : F βL[π] G), continuous_linear_map.comp g f) :=
is_bounded_bilinear_map_comp.is_bounded_linear_map_right _

lemma is_bounded_bilinear_map_apply :
  is_bounded_bilinear_map π (Ξ»p : (E βL[π] F) Γ E, p.1 p.2) :=
{ add_left   := by simp,
  smul_left  := by simp,
  add_right  := by simp,
  smul_right := by simp,
  bound      := β¨1, zero_lt_one, by simp [continuous_linear_map.le_op_norm]β© }

/-- The function `continuous_linear_map.smul_right`, associating to a continuous linear map
`f : E β π` and a scalar `c : F` the tensor product `f β c` as a continuous linear map from `E` to
`F`, is a bounded bilinear map. -/
lemma is_bounded_bilinear_map_smul_right :
  is_bounded_bilinear_map π
    (Ξ»p, (continuous_linear_map.smul_right : (E βL[π] π) β F β (E βL[π] F)) p.1 p.2) :=
{ add_left   := Ξ»mβ mβ f, by { ext z, simp [add_smul] },
  smul_left  := Ξ»c m f, by { ext z, simp [mul_smul] },
  add_right  := Ξ»m fβ fβ, by { ext z, simp [smul_add] },
  smul_right := Ξ»c m f, by { ext z, simp [smul_smul, mul_comm] },
  bound      := β¨1, zero_lt_one, Ξ»m f, by simpβ© }

/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
lemma is_bounded_bilinear_map_comp_multilinear {ΞΉ : Type*} {E : ΞΉ β Type*}
[decidable_eq ΞΉ] [fintype ΞΉ] [βi, normed_group (E i)] [βi, normed_space π (E i)] :
  is_bounded_bilinear_map π (Ξ» p : (F βL[π] G) Γ (continuous_multilinear_map π E F),
    p.1.comp_continuous_multilinear_map p.2) :=
{ add_left   := Ξ» gβ gβ f, by { ext m, refl },
  smul_left  := Ξ» c g f, by { ext m, refl },
  add_right  := Ξ» g fβ fβ, by { ext m, simp },
  smul_right := Ξ» c g f, by { ext m, simp },
  bound      := β¨1, zero_lt_one, Ξ» g f, begin
    apply continuous_multilinear_map.op_norm_le_bound _ _ (Ξ»m, _),
    { apply_rules [mul_nonneg, zero_le_one, norm_nonneg] },
    calc β₯g (f m)β₯ β€ β₯gβ₯ * β₯f mβ₯ : g.le_op_norm _
    ... β€ β₯gβ₯ * (β₯fβ₯ * β i, β₯m iβ₯) :
      mul_le_mul_of_nonneg_left (f.le_op_norm _) (norm_nonneg _)
    ... = 1 * β₯gβ₯ * β₯fβ₯ * β i, β₯m iβ₯ : by ring
    endβ© }

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q β¦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here a bounded linear map from `E Γ F` to `G`. The fact that this
is indeed the derivative of `f` is proved in `is_bounded_bilinear_map.has_fderiv_at` in
`fderiv.lean`-/

def is_bounded_bilinear_map.linear_deriv (h : is_bounded_bilinear_map π f) (p : E Γ F) :
  (E Γ F) ββ[π] G :=
{ to_fun := Ξ»q, f (p.1, q.2) + f (q.1, p.2),
  map_add' := Ξ»qβ qβ, begin
    change f (p.1, qβ.2 + qβ.2) + f (qβ.1 + qβ.1, p.2) =
      f (p.1, qβ.2) + f (qβ.1, p.2) + (f (p.1, qβ.2) + f (qβ.1, p.2)),
    simp [h.add_left, h.add_right], abel
  end,
  map_smul' := Ξ»c q, begin
    change f (p.1, c β’ q.2) + f (c β’ q.1, p.2) = c β’ (f (p.1, q.2) + f (q.1, p.2)),
    simp [h.smul_left, h.smul_right, smul_add]
  end }

/-- The derivative of a bounded bilinear map at a point `p : E Γ F`, as a continuous linear map
from `E Γ F` to `G`. -/
def is_bounded_bilinear_map.deriv (h : is_bounded_bilinear_map π f) (p : E Γ F) : (E Γ F) βL[π] G :=
(h.linear_deriv p).mk_continuous_of_exists_bound $ begin
  rcases h.bound with β¨C, Cpos, hCβ©,
  refine β¨C * β₯p.1β₯ + C * β₯p.2β₯, Ξ»q, _β©,
  calc β₯f (p.1, q.2) + f (q.1, p.2)β₯
    β€ C * β₯p.1β₯ * β₯q.2β₯ + C * β₯q.1β₯ * β₯p.2β₯ : norm_add_le_of_le (hC _ _) (hC _ _)
  ... β€ C * β₯p.1β₯ * β₯qβ₯ + C * β₯qβ₯ * β₯p.2β₯ : begin
      apply add_le_add,
      exact mul_le_mul_of_nonneg_left
        (le_max_right _ _) (mul_nonneg (le_of_lt Cpos) (norm_nonneg _)),
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt Cpos),
  end
  ... = (C * β₯p.1β₯ + C * β₯p.2β₯) * β₯qβ₯ : by ring
end

@[simp] lemma is_bounded_bilinear_map_deriv_coe (h : is_bounded_bilinear_map π f) (p q : E Γ F) :
  h.deriv p q = f (p.1, q.2) + f (q.1, p.2) := rfl

variables (π)

/-- The function `lmul_left_right : π' Γ π' β (π' βL[π] π')` is a bounded bilinear map. -/
lemma continuous_linear_map.lmul_left_right_is_bounded_bilinear
  (π' : Type*) [normed_ring π'] [normed_algebra π π'] :
  is_bounded_bilinear_map π (Ξ» p : π' Γ π', continuous_linear_map.lmul_left_right π π' p.1 p.2) :=
(continuous_linear_map.lmul_left_right π π').is_bounded_bilinear_map

variables {π}

/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
lemma is_bounded_bilinear_map.is_bounded_linear_map_deriv (h : is_bounded_bilinear_map π f) :
  is_bounded_linear_map π (Ξ»p : E Γ F, h.deriv p) :=
begin
  rcases h.bound with β¨C, Cpos : 0 < C, hCβ©,
  refine is_linear_map.with_bound β¨Ξ»pβ pβ, _, Ξ»c p, _β© (C + C) (Ξ»p, _),
  { ext; simp [h.add_left, h.add_right]; abel },
  { ext; simp [h.smul_left, h.smul_right, smul_add] },
  { refine continuous_linear_map.op_norm_le_bound _
      (mul_nonneg (add_nonneg Cpos.le Cpos.le) (norm_nonneg _)) (Ξ»q, _),
    calc β₯f (p.1, q.2) + f (q.1, p.2)β₯
      β€ C * β₯p.1β₯ * β₯q.2β₯ + C * β₯q.1β₯ * β₯p.2β₯ : norm_add_le_of_le (hC _ _) (hC _ _)
    ... β€ C * β₯pβ₯ * β₯qβ₯ + C * β₯qβ₯ * β₯pβ₯ : by apply_rules [add_le_add, mul_le_mul, norm_nonneg,
      le_of_lt Cpos, le_refl, le_max_left, le_max_right, mul_nonneg]
    ... = (C + C) * β₯pβ₯ * β₯qβ₯ : by ring },
end

end bilinear_map

/-- A linear isometry preserves the norm. -/
lemma linear_map.norm_apply_of_isometry (f : E ββ[π] F) {x : E} (hf : isometry f) : β₯f xβ₯ = β₯xβ₯ :=
by { simp_rw [βdist_zero_right, βf.map_zero], exact isometry.dist_eq hf _ _ }

/-- Construct a continuous linear equiv from
a linear map that is also an isometry with full range. -/
def continuous_linear_equiv.of_isometry (f : E ββ[π] F) (hf : isometry f) (hfr : f.range = β€) :
  E βL[π] F :=
continuous_linear_equiv.of_homothety
(linear_equiv.of_bijective f (linear_map.ker_eq_bot.mpr (isometry.injective hf)) hfr)
1 zero_lt_one (Ξ» _, by simp [one_mul, f.norm_apply_of_isometry hf])
