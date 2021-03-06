/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.calculus.mean_value

/-!
# L'HΓ΄pital's rule for 0/0 indeterminate forms

In this file, we prove several forms of "L'Hopital's rule" for computing 0/0
indeterminate forms. The proof of `has_deriv_at.lhopital_zero_right_on_Ioo`
is based on the one given in the corresponding
[Wikibooks](https://en.wikibooks.org/wiki/Calculus/L%27H%C3%B4pital%27s_Rule)
chapter, and all other statements are derived from this one by composing by
carefully chosen functions.

Note that the filter `f'/g'` tends to isn't required to be one of `π a`,
`at_top` or `at_bot`. In fact, we give a slightly stronger statement by
allowing it to be any filter on `β`.

Each statement is available in a `has_deriv_at` form and a `deriv` form, which
is denoted by each statement being in either the `has_deriv_at` or the `deriv`
namespace.
-/

open filter set
open_locale filter topological_space

variables {a b : β} (hab : a < b) {l : filter β} {f f' g g' : β β β}

/-!
## Interval-based versions

We start by proving statements where all conditions (derivability, `g' β  0`) have
to be satisfied on an explicitely-provided interval.
-/

namespace has_deriv_at

include hab

theorem lhopital_zero_right_on_Ioo
  (hff' : β x β Ioo a b, has_deriv_at f (f' x) x) (hgg' : β x β Ioo a b, has_deriv_at g (g' x) x)
  (hg' : β x β Ioo a b, g' x β  0)
  (hfa : tendsto f (π[Ioi a] a) (π 0)) (hga : tendsto g (π[Ioi a] a) (π 0))
  (hdiv : tendsto (Ξ» x, (f' x) / (g' x)) (π[Ioi a] a) l) :
  tendsto (Ξ» x, (f x) / (g x)) (π[Ioi a] a) l :=
begin
  have sub : β x β Ioo a b, Ioo a x β Ioo a b := Ξ» x hx, Ioo_subset_Ioo (le_refl a) (le_of_lt hx.2),
  have hg : β x β (Ioo a b), g x β  0,
  { intros x hx h,
    have : tendsto g (π[Iio x] x) (π 0),
    { rw [β h, β nhds_within_Ioo_eq_nhds_within_Iio hx.1],
      exact ((hgg' x hx).continuous_at.continuous_within_at.mono $ sub x hx).tendsto },
    obtain β¨y, hyx, hyβ© : β c β Ioo a x, g' c = 0,
      from exists_has_deriv_at_eq_zero' hx.1 hga this (Ξ» y hy, hgg' y $ sub x hx hy),
    exact hg' y (sub x hx hyx) hy },
  have : β x β Ioo a b, β c β Ioo a x, (f x) * (g' c) = (g x) * (f' c),
  { intros x hx,
    rw [β sub_zero (f x), β sub_zero (g x)],
    exact exists_ratio_has_deriv_at_eq_ratio_slope' g g' hx.1 f f'
      (Ξ» y hy, hgg' y $ sub x hx hy) (Ξ» y hy, hff' y $ sub x hx hy) hga hfa
      (tendsto_nhds_within_of_tendsto_nhds (hgg' x hx).continuous_at.tendsto)
      (tendsto_nhds_within_of_tendsto_nhds (hff' x hx).continuous_at.tendsto) },
  choose! c hc using this,
  have : β x β Ioo a b, ((Ξ» x', (f' x') / (g' x')) β c) x = f x / g x,
  { intros x hx,
    rcases hc x hx with β¨hβ, hββ©,
    field_simp [hg x hx, hg' (c x) ((sub x hx) hβ)],
    simp only [hβ],
    rwa mul_comm },
  have cmp : β x β Ioo a b, a < c x β§ c x < x,
    from Ξ» x hx, (hc x hx).1,
  rw β nhds_within_Ioo_eq_nhds_within_Ioi hab,
  apply tendsto_nhds_within_congr this,
  simp only,
  apply hdiv.comp,
  refine tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_nhds_within_of_tendsto_nhds tendsto_id) _ _) _,
  all_goals
  { apply eventually_nhds_with_of_forall,
    intros x hx,
    have := cmp x hx,
    try {simp},
    linarith [this] }
end

theorem lhopital_zero_right_on_Ico
  (hff' : β x β Ioo a b, has_deriv_at f (f' x) x) (hgg' : β x β Ioo a b, has_deriv_at g (g' x) x)
  (hcf : continuous_on f (Ico a b)) (hcg : continuous_on g (Ico a b))
  (hg' : β x β Ioo a b, g' x β  0)
  (hfa : f a = 0) (hga : g a = 0)
  (hdiv : tendsto (Ξ» x, (f' x) / (g' x)) (nhds_within a (Ioi a)) l) :
  tendsto (Ξ» x, (f x) / (g x)) (nhds_within a (Ioi a)) l :=
begin
  refine lhopital_zero_right_on_Ioo hab hff' hgg' hg' _ _ hdiv,
  { rw [β hfa, β nhds_within_Ioo_eq_nhds_within_Ioi hab],
    exact ((hcf a $ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto },
  { rw [β hga, β nhds_within_Ioo_eq_nhds_within_Ioi hab],
    exact ((hcg a $ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto },
end

theorem lhopital_zero_left_on_Ioo
  (hff' : β x β Ioo a b, has_deriv_at f (f' x) x) (hgg' : β x β Ioo a b, has_deriv_at g (g' x) x)
  (hg' : β x β Ioo a b, g' x β  0)
  (hfb : tendsto f (nhds_within b (Iio b)) (π 0)) (hgb : tendsto g (nhds_within b (Iio b)) (π 0))
  (hdiv : tendsto (Ξ» x, (f' x) / (g' x)) (nhds_within b (Iio b)) l) :
  tendsto (Ξ» x, (f x) / (g x)) (nhds_within b (Iio b)) l :=
begin
  -- Here, we essentially compose by `has_neg.neg`. The following is mostly technical details.
  have hdnf : β x β -Ioo a b, has_deriv_at (f β has_neg.neg) (f' (-x) * (-1)) x,
    from Ξ» x hx, comp x (hff' (-x) hx) (has_deriv_at_neg x),
  have hdng : β x β -Ioo a b, has_deriv_at (g β has_neg.neg) (g' (-x) * (-1)) x,
    from Ξ» x hx, comp x (hgg' (-x) hx) (has_deriv_at_neg x),
  rw preimage_neg_Ioo at hdnf,
  rw preimage_neg_Ioo at hdng,
  have := lhopital_zero_right_on_Ioo (neg_lt_neg hab) hdnf hdng
    (by { intros x hx h,
          apply hg' _ (by {rw β preimage_neg_Ioo at hx, exact hx}),
          rwa [mul_comm, β neg_eq_neg_one_mul, neg_eq_zero] at h })
    (hfb.comp tendsto_neg_nhds_within_Ioi_neg)
    (hgb.comp tendsto_neg_nhds_within_Ioi_neg)
    (by { simp only [neg_div_neg_eq, mul_one, mul_neg_eq_neg_mul_symm],
          exact (tendsto_congr $ Ξ» x, rfl).mp (hdiv.comp tendsto_neg_nhds_within_Ioi_neg) }),
  have := this.comp tendsto_neg_nhds_within_Iio,
  unfold function.comp at this,
  simpa only [neg_neg]
end

theorem lhopital_zero_left_on_Ioc
  (hff' : β x β Ioo a b, has_deriv_at f (f' x) x) (hgg' : β x β Ioo a b, has_deriv_at g (g' x) x)
  (hcf : continuous_on f (Ioc a b)) (hcg : continuous_on g (Ioc a b))
  (hg' : β x β Ioo a b, g' x β  0)
  (hfb : f b = 0) (hgb : g b = 0)
  (hdiv : tendsto (Ξ» x, (f' x) / (g' x)) (nhds_within b (Iio b)) l) :
  tendsto (Ξ» x, (f x) / (g x)) (nhds_within b (Iio b)) l :=
begin
  refine lhopital_zero_left_on_Ioo hab hff' hgg' hg' _ _ hdiv,
  { rw [β hfb, β nhds_within_Ioo_eq_nhds_within_Iio hab],
    exact ((hcf b $ right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto },
  { rw [β hgb, β nhds_within_Ioo_eq_nhds_within_Iio hab],
    exact ((hcg b $ right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto },
end

omit hab

theorem lhopital_zero_at_top_on_Ioi
  (hff' : β x β Ioi a, has_deriv_at f (f' x) x) (hgg' : β x β Ioi a, has_deriv_at g (g' x) x)
  (hg' : β x β Ioi a, g' x β  0)
  (hftop : tendsto f at_top (π 0)) (hgtop : tendsto g at_top (π 0))
  (hdiv : tendsto (Ξ» x, (f' x) / (g' x)) at_top l) :
  tendsto (Ξ» x, (f x) / (g x)) at_top l :=
begin
  obtain β¨ a', haa', ha'β© : β a', a < a' β§ 0 < a' :=
    β¨1 + max a 0, β¨lt_of_le_of_lt (le_max_left a 0) (lt_one_add _),
                   lt_of_le_of_lt (le_max_right a 0) (lt_one_add _)β©β©,
  have fact1 : β (x:β), x β Ioo 0 a'β»ΒΉ β x β  0 := Ξ» _ hx, (ne_of_lt hx.1).symm,
  have fact2 : β x β Ioo 0 a'β»ΒΉ, a < xβ»ΒΉ,
    from Ξ» _ hx, lt_trans haa' ((lt_inv ha' hx.1).mpr hx.2),
  have hdnf : β x β Ioo 0 a'β»ΒΉ, has_deriv_at (f β has_inv.inv) (f' (xβ»ΒΉ) * (-(x^2)β»ΒΉ)) x,
    from Ξ» x hx, comp x (hff' (xβ»ΒΉ) $ fact2 x hx) (has_deriv_at_inv $ fact1 x hx),
  have hdng : β x β Ioo 0 a'β»ΒΉ, has_deriv_at (g β has_inv.inv) (g' (xβ»ΒΉ) * (-(x^2)β»ΒΉ)) x,
    from Ξ» x hx, comp x (hgg' (xβ»ΒΉ) $ fact2 x hx) (has_deriv_at_inv $ fact1 x hx),
  have := lhopital_zero_right_on_Ioo (inv_pos.mpr ha') hdnf hdng
    (by { intros x hx,
          refine mul_ne_zero _ (neg_ne_zero.mpr $ inv_ne_zero $ pow_ne_zero _ $ fact1 x hx),
          exact hg' _ (fact2 x hx) })
    (hftop.comp tendsto_inv_zero_at_top)
    (hgtop.comp tendsto_inv_zero_at_top)
    (by { refine (tendsto_congr' _).mp (hdiv.comp tendsto_inv_zero_at_top),
          rw eventually_eq_iff_exists_mem,
          use [Ioi 0, self_mem_nhds_within],
          intros x hx,
          unfold function.comp,
          erw mul_div_mul_right,
          refine neg_ne_zero.mpr (inv_ne_zero $ pow_ne_zero _ $ ne_of_gt hx) }),
  have := this.comp tendsto_inv_at_top_zero',
  unfold function.comp at this,
  simpa only [inv_inv'],
end

theorem lhopital_zero_at_bot_on_Iio
  (hff' : β x β Iio a, has_deriv_at f (f' x) x) (hgg' : β x β Iio a, has_deriv_at g (g' x) x)
  (hg' : β x β Iio a, g' x β  0)
  (hfbot : tendsto f at_bot (π 0)) (hgbot : tendsto g at_bot (π 0))
  (hdiv : tendsto (Ξ» x, (f' x) / (g' x)) at_bot l) :
  tendsto (Ξ» x, (f x) / (g x)) at_bot l :=
begin
  -- Here, we essentially compose by `has_neg.neg`. The following is mostly technical details.
  have hdnf : β x β -Iio a, has_deriv_at (f β has_neg.neg) (f' (-x) * (-1)) x,
    from Ξ» x hx, comp x (hff' (-x) hx) (has_deriv_at_neg x),
  have hdng : β x β -Iio a, has_deriv_at (g β has_neg.neg) (g' (-x) * (-1)) x,
    from Ξ» x hx, comp x (hgg' (-x) hx) (has_deriv_at_neg x),
  rw preimage_neg_Iio at hdnf,
  rw preimage_neg_Iio at hdng,
  have := lhopital_zero_at_top_on_Ioi hdnf hdng
    (by { intros x hx h,
          apply hg' _ (by {rw β preimage_neg_Iio at hx, exact hx}),
          rwa [mul_comm, β neg_eq_neg_one_mul, neg_eq_zero] at h })
    (hfbot.comp tendsto_neg_at_top_at_bot)
    (hgbot.comp tendsto_neg_at_top_at_bot)
    (by { simp only [mul_one, mul_neg_eq_neg_mul_symm, neg_div_neg_eq],
          exact (tendsto_congr $ Ξ» x, rfl).mp (hdiv.comp tendsto_neg_at_top_at_bot) }),
  have := this.comp tendsto_neg_at_bot_at_top,
  unfold function.comp at this,
  simpa only [neg_neg],
end

end has_deriv_at

namespace deriv

include hab

theorem lhopital_zero_right_on_Ioo
  (hdf : differentiable_on β f (Ioo a b)) (hg' : β x β Ioo a b, deriv g x β  0)
  (hfa : tendsto f (π[Ioi a] a) (π 0)) (hga : tendsto g (π[Ioi a] a) (π 0))
  (hdiv : tendsto (Ξ» x, ((deriv f) x) / ((deriv g) x)) (π[Ioi a] a) l) :
  tendsto (Ξ» x, (f x) / (g x)) (π[Ioi a] a) l :=
begin
  have hdf : β x β Ioo a b, differentiable_at β f x,
    from Ξ» x hx, (hdf x hx).differentiable_at (Ioo_mem_nhds hx.1 hx.2),
  have hdg : β x β Ioo a b, differentiable_at β g x,
    from Ξ» x hx, classical.by_contradiction (Ξ» h, hg' x hx (deriv_zero_of_not_differentiable_at h)),
  exact has_deriv_at.lhopital_zero_right_on_Ioo hab (Ξ» x hx, (hdf x hx).has_deriv_at)
    (Ξ» x hx, (hdg x hx).has_deriv_at) hg' hfa hga hdiv
end

theorem lhopital_zero_right_on_Ico
  (hdf : differentiable_on β f (Ioo a b))
  (hcf : continuous_on f (Ico a b)) (hcg : continuous_on g (Ico a b))
  (hg' : β x β (Ioo a b), (deriv g) x β  0)
  (hfa : f a = 0) (hga : g a = 0)
  (hdiv : tendsto (Ξ» x, ((deriv f) x) / ((deriv g) x)) (nhds_within a (Ioi a)) l) :
  tendsto (Ξ» x, (f x) / (g x)) (nhds_within a (Ioi a)) l :=
begin
  refine lhopital_zero_right_on_Ioo hab hdf hg' _ _ hdiv,
  { rw [β hfa, β nhds_within_Ioo_eq_nhds_within_Ioi hab],
    exact ((hcf a $ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto },
  { rw [β hga, β nhds_within_Ioo_eq_nhds_within_Ioi hab],
    exact ((hcg a $ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto },
end

theorem lhopital_zero_left_on_Ioo
  (hdf : differentiable_on β f (Ioo a b))
  (hg' : β x β (Ioo a b), (deriv g) x β  0)
  (hfb : tendsto f (nhds_within b (Iio b)) (π 0)) (hgb : tendsto g (nhds_within b (Iio b)) (π 0))
  (hdiv : tendsto (Ξ» x, ((deriv f) x) / ((deriv g) x)) (nhds_within b (Iio b)) l) :
  tendsto (Ξ» x, (f x) / (g x)) (nhds_within b (Iio b)) l :=
begin
  have hdf : β x β Ioo a b, differentiable_at β f x,
    from Ξ» x hx, (hdf x hx).differentiable_at (Ioo_mem_nhds hx.1 hx.2),
  have hdg : β x β Ioo a b, differentiable_at β g x,
    from Ξ» x hx, classical.by_contradiction (Ξ» h, hg' x hx (deriv_zero_of_not_differentiable_at h)),
  exact has_deriv_at.lhopital_zero_left_on_Ioo hab (Ξ» x hx, (hdf x hx).has_deriv_at)
    (Ξ» x hx, (hdg x hx).has_deriv_at) hg' hfb hgb hdiv
end

omit hab

theorem lhopital_zero_at_top_on_Ioi
  (hdf : differentiable_on β f (Ioi a))
  (hg' : β x β (Ioi a), (deriv g) x β  0)
  (hftop : tendsto f at_top (π 0)) (hgtop : tendsto g at_top (π 0))
  (hdiv : tendsto (Ξ» x, ((deriv f) x) / ((deriv g) x)) at_top l) :
  tendsto (Ξ» x, (f x) / (g x)) at_top l :=
begin
  have hdf : β x β Ioi a, differentiable_at β f x,
    from Ξ» x hx, (hdf x hx).differentiable_at (Ioi_mem_nhds hx),
  have hdg : β x β Ioi a, differentiable_at β g x,
    from Ξ» x hx, classical.by_contradiction (Ξ» h, hg' x hx (deriv_zero_of_not_differentiable_at h)),
  exact has_deriv_at.lhopital_zero_at_top_on_Ioi (Ξ» x hx, (hdf x hx).has_deriv_at)
    (Ξ» x hx, (hdg x hx).has_deriv_at) hg' hftop hgtop hdiv,
end

theorem lhopital_zero_at_bot_on_Iio
  (hdf : differentiable_on β f (Iio a))
  (hg' : β x β (Iio a), (deriv g) x β  0)
  (hfbot : tendsto f at_bot (π 0)) (hgbot : tendsto g at_bot (π 0))
  (hdiv : tendsto (Ξ» x, ((deriv f) x) / ((deriv g) x)) at_bot l) :
  tendsto (Ξ» x, (f x) / (g x)) at_bot l :=
begin
  have hdf : β x β Iio a, differentiable_at β f x,
    from Ξ» x hx, (hdf x hx).differentiable_at (Iio_mem_nhds hx),
  have hdg : β x β Iio a, differentiable_at β g x,
    from Ξ» x hx, classical.by_contradiction (Ξ» h, hg' x hx (deriv_zero_of_not_differentiable_at h)),
  exact has_deriv_at.lhopital_zero_at_bot_on_Iio (Ξ» x hx, (hdf x hx).has_deriv_at)
    (Ξ» x hx, (hdg x hx).has_deriv_at) hg' hfbot hgbot hdiv,
end

end deriv

/-!
## Generic versions

The following statements no longer any explicit interval, as they only require
conditions holding eventually.
-/

namespace has_deriv_at

/-- L'HΓ΄pital's rule for approaching a real from the right, `has_deriv_at` version -/
theorem lhopital_zero_nhds_right
  (hff' : βαΆ  x in π[Ioi a] a, has_deriv_at f (f' x) x)
  (hgg' : βαΆ  x in π[Ioi a] a, has_deriv_at g (g' x) x)
  (hg' : βαΆ  x in π[Ioi a] a, g' x β  0)
  (hfa : tendsto f (π[Ioi a] a) (π 0)) (hga : tendsto g (π[Ioi a] a) (π 0))
  (hdiv : tendsto (Ξ» x, (f' x) / (g' x)) (π[Ioi a] a) l) :
  tendsto (Ξ» x, (f x) / (g x)) (π[Ioi a] a) l :=
begin
  rw eventually_iff_exists_mem at *,
  rcases hff' with β¨sβ, hsβ, hff'β©,
  rcases hgg' with β¨sβ, hsβ, hgg'β©,
  rcases hg' with β¨sβ, hsβ, hg'β©,
  let s := sβ β© sβ β© sβ,
  have hs : s β π[Ioi a] a := inter_mem_sets (inter_mem_sets hsβ hsβ) hsβ,
  rw mem_nhds_within_Ioi_iff_exists_Ioo_subset at hs,
  rcases hs with β¨u, hau, huβ©,
  refine lhopital_zero_right_on_Ioo hau _ _ _ hfa hga hdiv;
  intros x hx;
  apply_assumption;
  exact (hu hx).1.1 <|> exact (hu hx).1.2 <|> exact (hu hx).2
end

/-- L'HΓ΄pital's rule for approaching a real from the left, `has_deriv_at` version -/
theorem lhopital_zero_nhds_left
  (hff' : βαΆ  x in π[Iio a] a, has_deriv_at f (f' x) x)
  (hgg' : βαΆ  x in π[Iio a] a, has_deriv_at g (g' x) x)
  (hg' : βαΆ  x in π[Iio a] a, g' x β  0)
  (hfa : tendsto f (π[Iio a] a) (π 0)) (hga : tendsto g (π[Iio a] a) (π 0))
  (hdiv : tendsto (Ξ» x, (f' x) / (g' x)) (π[Iio a] a) l) :
  tendsto (Ξ» x, (f x) / (g x)) (π[Iio a] a) l :=
begin
  rw eventually_iff_exists_mem at *,
  rcases hff' with β¨sβ, hsβ, hff'β©,
  rcases hgg' with β¨sβ, hsβ, hgg'β©,
  rcases hg' with β¨sβ, hsβ, hg'β©,
  let s := sβ β© sβ β© sβ,
  have hs : s β π[Iio a] a := inter_mem_sets (inter_mem_sets hsβ hsβ) hsβ,
  rw mem_nhds_within_Iio_iff_exists_Ioo_subset at hs,
  rcases hs with β¨l, hal, hlβ©,
  refine lhopital_zero_left_on_Ioo hal _ _ _ hfa hga hdiv;
  intros x hx;
  apply_assumption;
  exact (hl hx).1.1 <|> exact (hl hx).1.2 <|> exact (hl hx).2
end

/-- L'HΓ΄pital's rule for approaching a real, `has_deriv_at` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds'
  (hff' : βαΆ  x in π[univ \ {a}] a, has_deriv_at f (f' x) x)
  (hgg' : βαΆ  x in π[univ \ {a}] a, has_deriv_at g (g' x) x)
  (hg' : βαΆ  x in π[univ \ {a}] a, g' x β  0)
  (hfa : tendsto f (π[univ \ {a}] a) (π 0)) (hga : tendsto g (π[univ \ {a}] a) (π 0))
  (hdiv : tendsto (Ξ» x, (f' x) / (g' x)) (π[univ \ {a}] a) l) :
  tendsto (Ξ» x, (f x) / (g x)) (π[univ \ {a}] a) l :=
begin
  have : univ \ {a} = Iio a βͺ Ioi a,
  { ext, rw [mem_diff_singleton, eq_true_intro $ mem_univ x, true_and, ne_iff_lt_or_gt], refl },
  simp only [this, nhds_within_union, tendsto_sup, eventually_sup] at *,
  exact β¨lhopital_zero_nhds_left hff'.1 hgg'.1 hg'.1 hfa.1 hga.1 hdiv.1,
          lhopital_zero_nhds_right hff'.2 hgg'.2 hg'.2 hfa.2 hga.2 hdiv.2β©
end

/-- L'HΓ΄pital's rule for approaching a real, `has_deriv_at` version -/
theorem lhopital_zero_nhds
  (hff' : βαΆ  x in π a, has_deriv_at f (f' x) x)
  (hgg' : βαΆ  x in π a, has_deriv_at g (g' x) x)
  (hg' : βαΆ  x in π a, g' x β  0)
  (hfa : tendsto f (π a) (π 0)) (hga : tendsto g (π a) (π 0))
  (hdiv : tendsto (Ξ» x, f' x / g' x) (π a) l) :
  tendsto (Ξ» x, f x / g x) (π[univ \ {a}] a) l :=
begin
  apply @lhopital_zero_nhds' _ _ _ f' _ g';
  apply eventually_nhds_within_of_eventually_nhds <|> apply tendsto_nhds_within_of_tendsto_nhds;
  assumption
end

/-- L'HΓ΄pital's rule for approaching +β, `has_deriv_at` version -/
theorem lhopital_zero_at_top
  (hff' : βαΆ  x in at_top, has_deriv_at f (f' x) x)
  (hgg' : βαΆ  x in at_top, has_deriv_at g (g' x) x)
  (hg' : βαΆ  x in at_top, g' x β  0)
  (hftop : tendsto f at_top (π 0)) (hgtop : tendsto g at_top (π 0))
  (hdiv : tendsto (Ξ» x, (f' x) / (g' x)) at_top l) :
  tendsto (Ξ» x, (f x) / (g x)) at_top l :=
begin
  rw eventually_iff_exists_mem at *,
  rcases hff' with β¨sβ, hsβ, hff'β©,
  rcases hgg' with β¨sβ, hsβ, hgg'β©,
  rcases hg' with β¨sβ, hsβ, hg'β©,
  let s := sβ β© sβ β© sβ,
  have hs : s β at_top := inter_mem_sets (inter_mem_sets hsβ hsβ) hsβ,
  rw mem_at_top_sets at hs,
  rcases hs with β¨l, hlβ©,
  have hl' : Ioi l β s := Ξ» x hx, hl x (le_of_lt hx),
  refine lhopital_zero_at_top_on_Ioi _ _ (Ξ» x hx, hg' x $ (hl' hx).2) hftop hgtop hdiv;
  intros x hx;
  apply_assumption;
  exact (hl' hx).1.1 <|> exact (hl' hx).1.2
end

/-- L'HΓ΄pital's rule for approaching -β, `has_deriv_at` version -/
theorem lhopital_zero_at_bot
  (hff' : βαΆ  x in at_bot, has_deriv_at f (f' x) x)
  (hgg' : βαΆ  x in at_bot, has_deriv_at g (g' x) x)
  (hg' : βαΆ  x in at_bot, g' x β  0)
  (hfbot : tendsto f at_bot (π 0)) (hgbot : tendsto g at_bot (π 0))
  (hdiv : tendsto (Ξ» x, (f' x) / (g' x)) at_bot l) :
  tendsto (Ξ» x, (f x) / (g x)) at_bot l :=
begin
  rw eventually_iff_exists_mem at *,
  rcases hff' with β¨sβ, hsβ, hff'β©,
  rcases hgg' with β¨sβ, hsβ, hgg'β©,
  rcases hg' with β¨sβ, hsβ, hg'β©,
  let s := sβ β© sβ β© sβ,
  have hs : s β at_bot := inter_mem_sets (inter_mem_sets hsβ hsβ) hsβ,
  rw mem_at_bot_sets at hs,
  rcases hs with β¨l, hlβ©,
  have hl' : Iio l β s := Ξ» x hx, hl x (le_of_lt hx),
  refine lhopital_zero_at_bot_on_Iio _ _ (Ξ» x hx, hg' x $ (hl' hx).2) hfbot hgbot hdiv;
  intros x hx;
  apply_assumption;
  exact (hl' hx).1.1 <|> exact (hl' hx).1.2
end

end has_deriv_at

namespace deriv

/-- L'HΓ΄pital's rule for approaching a real from the right, `deriv` version -/
theorem lhopital_zero_nhds_right
  (hdf : βαΆ  x in π[Ioi a] a, differentiable_at β f x)
  (hg' : βαΆ  x in π[Ioi a] a, deriv g x β  0)
  (hfa : tendsto f (π[Ioi a] a) (π 0)) (hga : tendsto g (π[Ioi a] a) (π 0))
  (hdiv : tendsto (Ξ» x, ((deriv f) x) / ((deriv g) x)) (π[Ioi a] a) l) :
  tendsto (Ξ» x, (f x) / (g x)) (π[Ioi a] a) l :=
begin
  have hdg : βαΆ  x in π[Ioi a] a, differentiable_at β g x,
    from hg'.mp (eventually_of_forall $
      Ξ» _ hg', classical.by_contradiction (Ξ» h, hg' (deriv_zero_of_not_differentiable_at h))),
  have hdf' : βαΆ  x in π[Ioi a] a, has_deriv_at f (deriv f x) x,
    from hdf.mp (eventually_of_forall $ Ξ» _, differentiable_at.has_deriv_at),
  have hdg' : βαΆ  x in π[Ioi a] a, has_deriv_at g (deriv g x) x,
    from hdg.mp (eventually_of_forall $ Ξ» _, differentiable_at.has_deriv_at),
  exact has_deriv_at.lhopital_zero_nhds_right hdf' hdg' hg' hfa hga hdiv
end

/-- L'HΓ΄pital's rule for approaching a real from the left, `deriv` version -/
theorem lhopital_zero_nhds_left
  (hdf : βαΆ  x in π[Iio a] a, differentiable_at β f x)
  (hg' : βαΆ  x in π[Iio a] a, deriv g x β  0)
  (hfa : tendsto f (π[Iio a] a) (π 0)) (hga : tendsto g (π[Iio a] a) (π 0))
  (hdiv : tendsto (Ξ» x, ((deriv f) x) / ((deriv g) x)) (π[Iio a] a) l) :
  tendsto (Ξ» x, (f x) / (g x)) (π[Iio a] a) l :=
begin
  have hdg : βαΆ  x in π[Iio a] a, differentiable_at β g x,
    from hg'.mp (eventually_of_forall $
      Ξ» _ hg', classical.by_contradiction (Ξ» h, hg' (deriv_zero_of_not_differentiable_at h))),
  have hdf' : βαΆ  x in π[Iio a] a, has_deriv_at f (deriv f x) x,
    from hdf.mp (eventually_of_forall $ Ξ» _, differentiable_at.has_deriv_at),
  have hdg' : βαΆ  x in π[Iio a] a, has_deriv_at g (deriv g x) x,
    from hdg.mp (eventually_of_forall $ Ξ» _, differentiable_at.has_deriv_at),
  exact has_deriv_at.lhopital_zero_nhds_left hdf' hdg' hg' hfa hga hdiv
end

/-- L'HΓ΄pital's rule for approaching a real, `deriv` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds'
  (hdf : βαΆ  x in π[univ \ {a}] a, differentiable_at β f x)
  (hg' : βαΆ  x in π[univ \ {a}] a, deriv g x β  0)
  (hfa : tendsto f (π[univ \ {a}] a) (π 0)) (hga : tendsto g (π[univ \ {a}] a) (π 0))
  (hdiv : tendsto (Ξ» x, ((deriv f) x) / ((deriv g) x)) (π[univ \ {a}] a) l) :
  tendsto (Ξ» x, (f x) / (g x)) (π[univ \ {a}] a) l :=
begin
  have : univ \ {a} = Iio a βͺ Ioi a,
  { ext, rw [mem_diff_singleton, eq_true_intro $ mem_univ x, true_and, ne_iff_lt_or_gt], refl },
  simp only [this, nhds_within_union, tendsto_sup, eventually_sup] at *,
  exact β¨lhopital_zero_nhds_left hdf.1 hg'.1 hfa.1 hga.1 hdiv.1,
          lhopital_zero_nhds_right hdf.2 hg'.2 hfa.2 hga.2 hdiv.2β©,
end

/-- L'HΓ΄pital's rule for approaching a real, `deriv` version -/
theorem lhopital_zero_nhds
  (hdf : βαΆ  x in π a, differentiable_at β f x)
  (hg' : βαΆ  x in π a, deriv g x β  0)
  (hfa : tendsto f (π a) (π 0)) (hga : tendsto g (π a) (π 0))
  (hdiv : tendsto (Ξ» x, ((deriv f) x) / ((deriv g) x)) (π a) l) :
  tendsto (Ξ» x, (f x) / (g x)) (π[univ \ {a}] a) l :=
begin
  apply lhopital_zero_nhds';
  apply eventually_nhds_within_of_eventually_nhds <|> apply tendsto_nhds_within_of_tendsto_nhds;
  assumption
end

/-- L'HΓ΄pital's rule for approaching +β, `deriv` version -/
theorem lhopital_zero_at_top
  (hdf : βαΆ  (x : β) in at_top, differentiable_at β f x)
  (hg' : βαΆ  (x : β) in at_top, deriv g x β  0)
  (hftop : tendsto f at_top (π 0)) (hgtop : tendsto g at_top (π 0))
  (hdiv : tendsto (Ξ» x, ((deriv f) x) / ((deriv g) x)) at_top l) :
  tendsto (Ξ» x, (f x) / (g x)) at_top l :=
begin
  have hdg : βαΆ  x in at_top, differentiable_at β g x,
    from hg'.mp (eventually_of_forall $
      Ξ» _ hg', classical.by_contradiction (Ξ» h, hg' (deriv_zero_of_not_differentiable_at h))),
  have hdf' : βαΆ  x in at_top, has_deriv_at f (deriv f x) x,
    from hdf.mp (eventually_of_forall $ Ξ» _, differentiable_at.has_deriv_at),
  have hdg' : βαΆ  x in at_top, has_deriv_at g (deriv g x) x,
    from hdg.mp (eventually_of_forall $ Ξ» _, differentiable_at.has_deriv_at),
  exact has_deriv_at.lhopital_zero_at_top hdf' hdg' hg' hftop hgtop hdiv
end

/-- L'HΓ΄pital's rule for approaching -β, `deriv` version -/
theorem lhopital_zero_at_bot
  (hdf : βαΆ  (x : β) in at_bot, differentiable_at β f x)
  (hg' : βαΆ  (x : β) in at_bot, deriv g x β  0)
  (hfbot : tendsto f at_bot (π 0)) (hgbot : tendsto g at_bot (π 0))
  (hdiv : tendsto (Ξ» x, ((deriv f) x) / ((deriv g) x)) at_bot l) :
  tendsto (Ξ» x, (f x) / (g x)) at_bot l :=
begin
  have hdg : βαΆ  x in at_bot, differentiable_at β g x,
    from hg'.mp (eventually_of_forall $
      Ξ» _ hg', classical.by_contradiction (Ξ» h, hg' (deriv_zero_of_not_differentiable_at h))),
  have hdf' : βαΆ  x in at_bot, has_deriv_at f (deriv f x) x,
    from hdf.mp (eventually_of_forall $ Ξ» _, differentiable_at.has_deriv_at),
  have hdg' : βαΆ  x in at_bot, has_deriv_at g (deriv g x) x,
    from hdg.mp (eventually_of_forall $ Ξ» _, differentiable_at.has_deriv_at),
  exact has_deriv_at.lhopital_zero_at_bot hdf' hdg' hg' hfbot hgbot hdiv
end

end deriv
