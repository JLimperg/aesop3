/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne
-/

import topology.category.CompHaus
import topology.connected
import topology.subset_properties
import category_theory.adjunction.reflective
import category_theory.monad.limits

/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `Top`. The fully faithful functor
is called `Profinite_to_Top`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

## TODO

0. Link to category of projective limits of finite discrete sets.
1. finite coproducts
2. Clausen/Scholze topology on the category `Profinite`.

## Tags

profinite

-/

open category_theory

/-- The type of profinite topological spaces. -/
structure Profinite :=
(to_Top : Top)
[is_compact : compact_space to_Top]
[is_t2 : t2_space to_Top]
[is_totally_disconnected : totally_disconnected_space to_Top]

namespace Profinite

instance : inhabited Profinite := ⟨{to_Top := { α := pempty }}⟩

instance category : category Profinite := induced_category.category to_Top
instance concrete_category : concrete_category Profinite := induced_category.concrete_category _
instance has_forget₂ : has_forget₂ Profinite Top := induced_category.has_forget₂ _

instance : has_coe_to_sort Profinite := ⟨Type*, λ X, X.to_Top⟩
instance {X : Profinite} : compact_space X := X.is_compact
instance {X : Profinite} : t2_space X := X.is_t2
instance {X : Profinite} : totally_disconnected_space X := X.is_totally_disconnected

@[simp]
lemma coe_to_Top {X : Profinite} : (X.to_Top : Type*) = X :=
rfl

@[simp] lemma coe_id (X : Profinite) : (𝟙 X : X → X) = id := rfl

@[simp] lemma coe_comp {X Y Z : Profinite} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f := rfl

end Profinite

/-- The fully faithful embedding of `Profinite` in `Top`. -/
@[simps, derive [full, faithful]]
def Profinite_to_Top : Profinite ⥤ Top := forget₂ _ _

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
@[simps] def Profinite.to_CompHaus : Profinite ⥤ CompHaus :=
{ obj := λ X, { to_Top := X.to_Top },
  map := λ _ _ f, f }

instance : full Profinite.to_CompHaus := { preimage := λ _ _ f, f }
instance : faithful Profinite.to_CompHaus := {}

@[simp] lemma Profinite.to_CompHaus_to_Top :
  Profinite.to_CompHaus ⋙ CompHaus_to_Top = Profinite_to_Top :=
rfl

section Profinite
local attribute [instance] connected_component_setoid

universes u

/--
(Implementation) The object part of the connected_components functor from compact Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components.
See: https://stacks.math.columbia.edu/tag/0900
-/
-- Without explicit universe annotations here, Lean introduces two universe variables and
-- unhelpfully defines a function `CompHaus.{max u₁ u₂} → Profinite.{max u₁ u₂}`.
def CompHaus.to_Profinite_obj (X : CompHaus.{u}) : Profinite.{u} :=
{ to_Top := { α := connected_components X.to_Top.α },
  is_compact := quotient.compact_space,
  is_t2 := connected_components.t2,
  is_totally_disconnected := connected_components.totally_disconnected_space }

/--
(Implementation) The bijection of homsets to establish the reflective adjunction of Profinite
spaces in compact Hausdorff spaces.
-/
def Profinite.to_CompHaus_equivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
  (CompHaus.to_Profinite_obj X ⟶ Y) ≃ (X ⟶ Profinite.to_CompHaus.obj Y) :=
{ to_fun := λ f,
  { to_fun := f.1 ∘ quotient.mk,
    continuous_to_fun := continuous.comp f.2 (continuous_quotient_mk) },
  inv_fun := λ g,
    { to_fun := continuous.connected_components_lift g.2,
      continuous_to_fun := continuous.connected_components_lift_continuous g.2},
  left_inv := λ f, continuous_map.ext $ λ x, quotient.induction_on x $ λ a, rfl,
  right_inv := λ f, continuous_map.ext $ λ x, rfl }

/--
The connected_components functor from compact Hausdorff spaces to profinite spaces,
left adjoint to the inclusion functor.
-/
def CompHaus.to_Profinite : CompHaus ⥤ Profinite :=
adjunction.left_adjoint_of_equiv Profinite.to_CompHaus_equivalence (λ _ _ _ _ _, rfl)

lemma CompHaus.to_Profinite_obj' (X : CompHaus) :
  ↥(CompHaus.to_Profinite.obj X) = connected_components X.to_Top.α := rfl

end Profinite

namespace Profinite

/--
The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus
-/
def to_Profinite_adj_to_CompHaus : CompHaus.to_Profinite ⊣ Profinite.to_CompHaus :=
adjunction.adjunction_of_equiv_left _ _

/-- The category of profinite sets is reflective in the category of compact hausdroff spaces -/
instance to_CompHaus.reflective : reflective Profinite.to_CompHaus :=
{ to_is_right_adjoint := ⟨CompHaus.to_Profinite, Profinite.to_Profinite_adj_to_CompHaus⟩ }

noncomputable
instance to_CompHaus.creates_limits : creates_limits Profinite.to_CompHaus :=
monadic_creates_limits _

noncomputable
instance to_Top.reflective : reflective (Profinite_to_Top : Profinite ⥤ Top) :=
reflective.comp Profinite.to_CompHaus CompHaus_to_Top

noncomputable
instance to_Top.creates_limits : creates_limits Profinite_to_Top :=
monadic_creates_limits _

instance has_limits : limits.has_limits Profinite :=
has_limits_of_has_limits_creates_limits Profinite_to_Top

instance has_colimits : limits.has_colimits Profinite :=
has_colimits_of_reflective to_CompHaus

/-- Any morphism of profinite spaces is a closed map. -/
lemma is_closed_map {X Y : Profinite} (f : X ⟶ Y) : is_closed_map f :=
show is_closed_map (Profinite.to_CompHaus.map f), from CompHaus.is_closed_map _

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
lemma is_iso_of_bijective {X Y : Profinite} (f : X ⟶ Y)
  (bij : function.bijective f) : is_iso f :=
begin
  haveI := CompHaus.is_iso_of_bijective (Profinite.to_CompHaus.map f) bij,
  exact is_iso_of_fully_faithful Profinite.to_CompHaus _
end

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
noncomputable def iso_of_bijective {X Y : Profinite} (f : X ⟶ Y)
  (bij : function.bijective f) : X ≅ Y :=
by letI := Profinite.is_iso_of_bijective f bij; exact as_iso f

instance forget_reflects_isomorphisms : reflects_isomorphisms (forget Profinite) :=
⟨by introsI A B f hf; exact Profinite.is_iso_of_bijective _ ((is_iso_iff_bijective ⇑f).mp hf)⟩

end Profinite
