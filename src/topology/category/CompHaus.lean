/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bhavik Mehta
-/

import category_theory.adjunction.reflective
import topology.category.Top
import topology.stone_cech
import category_theory.monad.limits

/-!

# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `Top`.
The fully faithful functor `CompHaus ⥤ Top` is denoted `CompHaus_to_Top`.

**Note:** The file `topology/category/Compactum.lean` provides the equivalence between `Compactum`,
which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`Compactum_to_CompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `Compactum_to_CompHaus.is_equivalence`.
See `topology/category/Compactum.lean` for a more detailed discussion where these definitions are
introduced.

-/

universe u

open category_theory

/-- The type of Compact Hausdorff topological spaces. -/
structure CompHaus :=
(to_Top : Top)
[is_compact : compact_space to_Top]
[is_hausdorff : t2_space to_Top]

namespace CompHaus

instance : inhabited CompHaus := ⟨{to_Top := { α := pempty }}⟩

instance : has_coe_to_sort CompHaus := ⟨Type*, λ X, X.to_Top⟩
instance {X : CompHaus} : compact_space X := X.is_compact
instance {X : CompHaus} : t2_space X := X.is_hausdorff

instance category : category CompHaus := induced_category.category to_Top

instance concrete_category : concrete_category CompHaus :=
induced_category.concrete_category _

@[simp]
lemma coe_to_Top {X : CompHaus} : (X.to_Top : Type*) = X :=
rfl

variables (X : Type*) [topological_space X] [compact_space X] [t2_space X]

/-- A constructor for objects of the category `CompHaus`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
def of : CompHaus :=
{ to_Top := Top.of X,
  is_compact := ‹_›,
  is_hausdorff := ‹_› }

@[simp] lemma coe_of : (CompHaus.of X : Type _) = X := rfl

/-- Any continuous function on compact Hausdorff spaces is a closed map. -/
lemma is_closed_map {X Y : CompHaus} (f : X ⟶ Y) : is_closed_map f :=
λ C hC, (hC.compact.image f.continuous).is_closed

/-- Any continuous bijection of compact Hausdorff spaces is an isomorphism. -/
lemma is_iso_of_bijective {X Y : CompHaus} (f : X ⟶ Y) (bij : function.bijective f) : is_iso f :=
begin
  let E := equiv.of_bijective _ bij,
  have hE : continuous E.symm,
  { rw continuous_iff_is_closed,
    intros S hS,
    rw ← E.image_eq_preimage,
    exact is_closed_map f S hS },
  refine ⟨⟨⟨E.symm, hE⟩, _, _⟩⟩,
  { ext x,
    apply E.symm_apply_apply },
  { ext x,
    apply E.apply_symm_apply }
end

/-- Any continuous bijection of compact Hausdorff spaces induces an isomorphism. -/
noncomputable
def iso_of_bijective {X Y : CompHaus} (f : X ⟶ Y) (bij : function.bijective f) : X ≅ Y :=
by letI := is_iso_of_bijective _ bij; exact as_iso f

end CompHaus

/-- The fully faithful embedding of `CompHaus` in `Top`. -/
@[simps {rhs_md := semireducible}, derive [full, faithful]]
def CompHaus_to_Top : CompHaus.{u} ⥤ Top.{u} := induced_functor _

instance CompHaus.forget_reflects_isomorphisms : reflects_isomorphisms (forget CompHaus) :=
⟨by introsI A B f hf; exact CompHaus.is_iso_of_bijective _ ((is_iso_iff_bijective ⇑f).mp hf)⟩

/--
(Implementation) The object part of the compactification functor from topological spaces to
compact Hausdorff spaces.
-/
@[simps]
def StoneCech_obj (X : Top) : CompHaus := CompHaus.of (stone_cech X)

/--
(Implementation) The bijection of homsets to establish the reflective adjunction of compact
Hausdorff spaces in topological spaces.
-/
noncomputable def stone_cech_equivalence (X : Top) (Y : CompHaus) :
  (StoneCech_obj X ⟶ Y) ≃ (X ⟶ CompHaus_to_Top.obj Y) :=
{ to_fun := λ f,
  { to_fun := f ∘ stone_cech_unit,
    continuous_to_fun := f.2.comp (@continuous_stone_cech_unit X _) },
  inv_fun := λ f,
  { to_fun := stone_cech_extend f.2,
    continuous_to_fun := continuous_stone_cech_extend f.2 },
  left_inv :=
  begin
    rintro ⟨f : stone_cech X ⟶ Y, hf : continuous f⟩,
    ext (x : stone_cech X),
    refine congr_fun _ x,
    apply continuous.ext_on dense_range_stone_cech_unit (continuous_stone_cech_extend _) hf,
    rintro _ ⟨y, rfl⟩,
    apply congr_fun (stone_cech_extend_extends (hf.comp _)) y,
  end,
  right_inv :=
  begin
    rintro ⟨f : ↥X ⟶ Y, hf : continuous f⟩,
    ext,
    exact congr_fun (stone_cech_extend_extends hf) x,
  end }

/--
The Stone-Cech compactification functor from topological spaces to compact Hausdorff spaces,
left adjoint to the inclusion functor.
-/
noncomputable def Top_to_CompHaus : Top.{u} ⥤ CompHaus.{u} :=
adjunction.left_adjoint_of_equiv stone_cech_equivalence.{u u} (λ _ _ _ _ _, rfl)

lemma Top_to_CompHaus_obj (X : Top) : ↥(Top_to_CompHaus.obj X) = stone_cech X :=
rfl

/--
The category of compact Hausdorff spaces is reflective in the category of topological spaces.
-/
noncomputable instance CompHaus_to_Top.reflective : reflective CompHaus_to_Top :=
{ to_is_right_adjoint := ⟨Top_to_CompHaus, adjunction.adjunction_of_equiv_left _ _⟩ }

noncomputable instance CompHaus_to_Top.creates_limits : creates_limits CompHaus_to_Top :=
monadic_creates_limits _

instance CompHaus.has_limits : limits.has_limits CompHaus :=
has_limits_of_has_limits_creates_limits CompHaus_to_Top

instance CompHaus.has_colimits : limits.has_colimits CompHaus :=
has_colimits_of_reflective CompHaus_to_Top
