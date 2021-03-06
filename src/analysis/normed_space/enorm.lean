/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.normed_space.basic

/-!
# Extended norm

In this file we define a structure `enorm ð V` representing an extended norm (i.e., a norm that can
take the value `â`) on a vector space `V` over a normed field `ð`. We do not use `class` for
an `enorm` because the same space can have more than one extended norm. For example, the space of
measurable functions `f : Î± â â` has a family of `L_p` extended norms.

We prove some basic inequalities, then define

* `emetric_space` structure on `V` corresponding to `e : enorm ð V`;
* the subspace of vectors with finite norm, called `e.finite_subspace`;
* a `normed_space` structure on this space.

The last definition is an instance because the type involves `e`.

## Implementation notes

We do not define extended normed groups. They can be added to the chain once someone will need them.

## Tags

normed space, extended norm
-/

local attribute [instance, priority 1001] classical.prop_decidable
open_locale ennreal

/-- Extended norm on a vector space. As in the case of normed spaces, we require only
`â¥c â¢ xâ¥ â¤ â¥câ¥ * â¥xâ¥` in the definition, then prove an equality in `map_smul`. -/
structure enorm (ð : Type*) (V : Type*) [normed_field ð] [add_comm_group V] [module ð V] :=
(to_fun : V â ââ¥0â)
(eq_zero' : â x, to_fun x = 0 â x = 0)
(map_add_le' : â x y : V, to_fun (x + y) â¤ to_fun x + to_fun y)
(map_smul_le' : â (c : ð) (x : V), to_fun (c â¢ x) â¤ nnnorm c * to_fun x)

namespace enorm

variables {ð : Type*} {V : Type*} [normed_field ð] [add_comm_group V] [module ð V]
  (e : enorm ð V)

instance : has_coe_to_fun (enorm ð V) := â¨_, enorm.to_funâ©

lemma coe_fn_injective : function.injective (Î» (e : enorm ð V) (x : V), e x) :=
Î» eâ eâ h, by cases eâ; cases eâ; congr; exact h

@[ext] lemma ext {eâ eâ : enorm ð V} (h : â x, eâ x = eâ x) : eâ = eâ :=
coe_fn_injective $ funext h

lemma ext_iff {eâ eâ : enorm ð V} : eâ = eâ â â x, eâ x = eâ x :=
â¨Î» h x, h â¸ rfl, extâ©

@[simp, norm_cast] lemma coe_inj {eâ eâ : enorm ð V} : âeâ = eâ â eâ = eâ :=
coe_fn_injective.eq_iff

@[simp] lemma map_smul (c : ð) (x : V) : e (c â¢ x) = nnnorm c * e x :=
le_antisymm (e.map_smul_le' c x) $
begin
  by_cases hc : c = 0, { simp [hc] },
  calc (nnnorm c : ââ¥0â) * e x = nnnorm c * e (câ»Â¹ â¢ c â¢ x) : by rw [inv_smul_smul' hc]
  ... â¤ nnnorm c * (nnnorm (câ»Â¹) * e (c â¢ x)) : _
  ... = e (c â¢ x) : _,
  { exact ennreal.mul_le_mul (le_refl _) (e.map_smul_le' _ _) },
  { rw [â mul_assoc, normed_field.nnnorm_inv, ennreal.coe_inv,
     ennreal.mul_inv_cancel _ ennreal.coe_ne_top, one_mul]; simp [hc] }
end

@[simp] lemma map_zero : e 0 = 0 :=
by { rw [â zero_smul ð (0:V), e.map_smul], norm_num }

@[simp] lemma eq_zero_iff {x : V} : e x = 0 â x = 0 :=
â¨e.eq_zero' x, Î» h, h.symm â¸ e.map_zeroâ©

@[simp] lemma map_neg (x : V) : e (-x) = e x :=
calc e (-x) = nnnorm (-1:ð) * e x : by rw [â map_smul, neg_one_smul]
        ... = e x                 : by simp

lemma map_sub_rev (x y : V) : e (x - y) = e (y - x) :=
by rw [â neg_sub, e.map_neg]

lemma map_add_le (x y : V) : e (x + y) â¤ e x + e y := e.map_add_le' x y

lemma map_sub_le (x y : V) : e (x - y) â¤ e x + e y :=
calc e (x - y) = e (x + -y)   : by rw sub_eq_add_neg
           ... â¤ e x + e (-y) : e.map_add_le x (-y)
           ... = e x + e y    : by rw [e.map_neg]

instance : partial_order (enorm ð V) :=
{ le := Î» eâ eâ, â x, eâ x â¤ eâ x,
  le_refl := Î» e x, le_refl _,
  le_trans := Î» eâ eâ eâ hââ hââ x, le_trans (hââ x) (hââ x),
  le_antisymm := Î» eâ eâ hââ hââ, ext $ Î» x, le_antisymm (hââ x) (hââ x) }

/-- The `enorm` sending each non-zero vector to infinity. -/
noncomputable instance : has_top (enorm ð V) :=
â¨{ to_fun := Î» x, if x = 0 then 0 else â¤,
   eq_zero' := Î» x, by { split_ifs; simp [*] },
   map_add_le' := Î» x y,
     begin
       split_ifs with hxy hx hy hy hx hy hy; try { simp [*] },
       simpa [hx, hy] using hxy
     end,
   map_smul_le' := Î» c x,
     begin
       split_ifs with hcx hx hx; simp only [smul_eq_zero, not_or_distrib] at hcx,
       { simp only [mul_zero, le_refl] },
       { have : c = 0, by tauto,
         simp [this] },
       { tauto },
       { simp [hcx.1] }
     end }â©

noncomputable instance : inhabited (enorm ð V) := â¨â¤â©

lemma top_map {x : V} (hx : x â  0) : (â¤ : enorm ð V) x = â¤ := if_neg hx

noncomputable instance : semilattice_sup_top (enorm ð V) :=
{ le := (â¤),
  lt := (<),
  top := â¤,
  le_top := Î» e x, if h : x = 0 then by simp [h] else by simp [top_map h],
  sup := Î» eâ eâ,
  { to_fun := Î» x, max (eâ x) (eâ x),
    eq_zero' := Î» x h, eâ.eq_zero_iff.1 (ennreal.max_eq_zero_iff.1 h).1,
    map_add_le' := Î» x y, max_le
      (le_trans (eâ.map_add_le _ _) $ add_le_add (le_max_left _ _) (le_max_left _ _))
      (le_trans (eâ.map_add_le _ _) $ add_le_add (le_max_right _ _) (le_max_right _ _)),
    map_smul_le' := Î» c x, le_of_eq $ by simp only [map_smul, ennreal.mul_max] },
  le_sup_left := Î» eâ eâ x, le_max_left _ _,
  le_sup_right := Î» eâ eâ x, le_max_right _ _,
  sup_le := Î» eâ eâ eâ hâ hâ x, max_le (hâ x) (hâ x),
  .. enorm.partial_order }

@[simp, norm_cast] lemma coe_max (eâ eâ : enorm ð V) : â(eâ â eâ) = Î» x, max (eâ x) (eâ x) := rfl

@[norm_cast]
lemma max_map (eâ eâ : enorm ð V) (x : V) : (eâ â eâ) x = max (eâ x) (eâ x) := rfl

/-- Structure of an `emetric_space` defined by an extended norm. -/
def emetric_space : emetric_space V :=
{ edist := Î» x y, e (x - y),
  edist_self := Î» x, by simp,
  eq_of_edist_eq_zero := Î» x y, by simp [sub_eq_zero],
  edist_comm := e.map_sub_rev,
  edist_triangle := Î» x y z,
    calc e (x - z) = e ((x - y) + (y - z)) : by rw [sub_add_sub_cancel]
               ... â¤ e (x - y) + e (y - z) : e.map_add_le (x - y) (y - z) }

/-- The subspace of vectors with finite enorm. -/
def finite_subspace : subspace ð V :=
{ carrier   := {x | e x < â¤},
  zero_mem' := by simp,
  add_mem'  := Î» x y hx hy, lt_of_le_of_lt (e.map_add_le x y) (ennreal.add_lt_top.2 â¨hx, hyâ©),
  smul_mem' := Î» c x hx,
    calc e (c â¢ x) = nnnorm c * e x : e.map_smul c x
               ... < â¤              : ennreal.mul_lt_top ennreal.coe_lt_top hx }

/-- Metric space structure on `e.finite_subspace`. We use `emetric_space.to_metric_space_of_dist`
to ensure that this definition agrees with `e.emetric_space`. -/
instance : metric_space e.finite_subspace :=
begin
  letI := e.emetric_space,
  refine emetric_space.to_metric_space_of_dist _ (Î» x y, _) (Î» x y, rfl),
  change e (x - y) â  â¤,
  rw [â ennreal.lt_top_iff_ne_top],
  exact lt_of_le_of_lt (e.map_sub_le x y) (ennreal.add_lt_top.2 â¨x.2, y.2â©)
end

lemma finite_dist_eq (x y : e.finite_subspace) : dist x y = (e (x - y)).to_real := rfl

lemma finite_edist_eq (x y : e.finite_subspace) : edist x y = e (x - y) := rfl

/-- Normed group instance on `e.finite_subspace`. -/
instance : normed_group e.finite_subspace :=
{ norm := Î» x, (e x).to_real,
  dist_eq := Î» x y, rfl }

lemma finite_norm_eq (x : e.finite_subspace) : â¥xâ¥ = (e x).to_real := rfl

/-- Normed space instance on `e.finite_subspace`. -/
instance : normed_space ð e.finite_subspace :=
{ norm_smul_le := Î» c x, le_of_eq $ by simp [finite_norm_eq, ennreal.to_real_mul] }

end enorm
