/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.comma

/-!
# The category of arrows

The category of arrows, with morphisms commutative squares.
We set this up as a specialization of the comma category `comma L R`,
where `L` and `R` are both the identity functor.

We also define the typeclass `has_lift`, representing a choice of a lift
of a commutative square (that is, a diagonal morphism making the two triangles commute).

## Tags

comma, arrow
-/

namespace category_theory

universes v u -- morphism levels before object levels. See note [category_theory universes].
variables {T : Type u} [category.{v} T]

section
variables (T)

/-- The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative
     squares in `T`. -/
@[derive category]
def arrow := comma.{v v v} (ğ­ T) (ğ­ T)

-- Satisfying the inhabited linter
instance arrow.inhabited [inhabited T] : inhabited (arrow T) :=
{ default := show comma (ğ­ T) (ğ­ T), from default (comma (ğ­ T) (ğ­ T)) }

end

namespace arrow

@[simp] lemma id_left (f : arrow T) : comma_morphism.left (ğ f) = ğ (f.left) := rfl
@[simp] lemma id_right (f : arrow T) : comma_morphism.right (ğ f) = ğ (f.right) := rfl

/-- An object in the arrow category is simply a morphism in `T`. -/
@[simps]
def mk {X Y : T} (f : X â¶ Y) : arrow T :=
{ left := X,
  right := Y,
  hom := f }

instance {X Y : T} : has_coe (X â¶ Y) (arrow T) := â¨mkâ©

/-- A morphism in the arrow category is a commutative square connecting two objects of the arrow
    category. -/
@[simps]
def hom_mk {f g : arrow T} {u : f.left â¶ g.left} {v : f.right â¶ g.right}
  (w : u â« g.hom = f.hom â« v) : f â¶ g :=
{ left := u,
  right := v,
  w' := w }

/-- We can also build a morphism in the arrow category out of any commutative square in `T`. -/
@[simps]
def hom_mk' {X Y : T} {f : X â¶ Y} {P Q : T} {g : P â¶ Q} {u : X â¶ P} {v : Y â¶ Q}
  (w : u â« g = f â« v) : arrow.mk f â¶ arrow.mk g :=
{ left := u,
  right := v,
  w' := w }

@[simp, reassoc] lemma w {f g : arrow T} (sq : f â¶ g) : sq.left â« g.hom = f.hom â« sq.right := sq.w

-- `w_mk_left` is not needed, as it is a consequence of `w` and `mk_hom`.
@[simp, reassoc] lemma w_mk_right {f : arrow T} {X Y : T} {g : X â¶ Y} (sq : f â¶ mk g) :
  sq.left â« g = f.hom â« sq.right :=
sq.w

/-- Given a square from an arrow `i` to an isomorphism `p`, express the source part of `sq`
in terms of the inverse of `p`. -/
@[simp] lemma square_to_iso_invert (i : arrow T) {X Y : T} (p : X â Y) (sq : i â¶ arrow.mk p.hom) :
  i.hom â« sq.right â« p.inv = sq.left :=
by simpa only [category.assoc] using (iso.comp_inv_eq p).mpr ((arrow.w_mk_right sq).symm)

/-- Given a square from an isomorphism `i` to an arrow `p`, express the target part of `sq`
in terms of the inverse of `i`. -/
lemma square_from_iso_invert {X Y : T} (i : X â Y) (p : arrow T) (sq : arrow.mk i.hom â¶ p) :
  i.inv â« sq.left â« p.hom = sq.right :=
by simp only [iso.inv_hom_id_assoc, arrow.w, arrow.mk_hom]

/-- A lift of a commutative square is a diagonal morphism making the two triangles commute. -/
@[ext] structure lift_struct {f g : arrow T} (sq : f â¶ g) :=
(lift : f.right â¶ g.left)
(fac_left' : f.hom â« lift = sq.left . obviously)
(fac_right' : lift â« g.hom = sq.right . obviously)

restate_axiom lift_struct.fac_left'
restate_axiom lift_struct.fac_right'

instance lift_struct_inhabited {X : T} : inhabited (lift_struct (ğ (arrow.mk (ğ X)))) :=
â¨â¨ğ _, category.id_comp _, category.comp_id _â©â©

/-- `has_lift sq` says that there is some `lift_struct sq`, i.e., that it is possible to find a
    diagonal morphism making the two triangles commute. -/
class has_lift {f g : arrow T} (sq : f â¶ g) : Prop :=
mk' :: (exists_lift : nonempty (lift_struct sq))

lemma has_lift.mk {f g : arrow T} {sq : f â¶ g} (s : lift_struct sq) : has_lift sq :=
â¨nonempty.intro sâ©

attribute [simp, reassoc] lift_struct.fac_left lift_struct.fac_right

/-- Given `has_lift sq`, obtain a lift. -/
noncomputable def has_lift.struct {f g : arrow T} (sq : f â¶ g) [has_lift sq] : lift_struct sq :=
classical.choice has_lift.exists_lift

/-- If there is a lift of a commutative square `sq`, we can access it by saying `lift sq`. -/
noncomputable abbreviation lift {f g : arrow T} (sq : f â¶ g) [has_lift sq] : f.right â¶ g.left :=
(has_lift.struct sq).lift

lemma lift.fac_left {f g : arrow T} (sq : f â¶ g) [has_lift sq] : f.hom â« lift sq = sq.left :=
by simp

lemma lift.fac_right {f g : arrow T} (sq : f â¶ g) [has_lift sq] : lift sq â« g.hom = sq.right :=
by simp

@[simp, reassoc]
lemma lift.fac_right_of_to_mk {X Y : T} {f : arrow T} {g : X â¶ Y} (sq : f â¶ mk g) [has_lift sq] :
  lift sq â« g = sq.right :=
by simp only [âmk_hom g, lift.fac_right]

@[simp, reassoc]
lemma lift.fac_left_of_from_mk {X Y : T} {f : X â¶ Y} {g : arrow T} (sq : mk f â¶ g) [has_lift sq] :
  f â« lift sq = sq.left :=
by simp only [âmk_hom f, lift.fac_left]

@[simp, reassoc]
lemma lift_mk'_left {X Y P Q : T} {f : X â¶ Y} {g : P â¶ Q} {u : X â¶ P} {v : Y â¶ Q}
  (h : u â« g = f â« v) [has_lift $ arrow.hom_mk' h] : f â« lift (arrow.hom_mk' h) = u :=
by simp only [âarrow.mk_hom f, lift.fac_left, arrow.hom_mk'_left]

@[simp, reassoc]
lemma lift_mk'_right {X Y P Q : T} {f : X â¶ Y} {g : P â¶ Q} {u : X â¶ P} {v : Y â¶ Q}
  (h : u â« g = f â« v) [has_lift $ arrow.hom_mk' h] : lift (arrow.hom_mk' h) â« g = v :=
by simp only [âarrow.mk_hom g, lift.fac_right, arrow.hom_mk'_right]

section

instance subsingleton_lift_struct_of_epi {f g : arrow T} (sq : f â¶ g) [epi f.hom] :
  subsingleton (lift_struct sq) :=
subsingleton.intro $ Î» a b, lift_struct.ext a b $ (cancel_epi f.hom).1 $ by simp

instance subsingleton_lift_struct_of_mono {f g : arrow T} (sq : f â¶ g) [mono g.hom] :
  subsingleton (lift_struct sq) :=
subsingleton.intro $ Î» a b, lift_struct.ext a b $ (cancel_mono g.hom).1 $ by simp

end

variables {C : Type u} [category.{v} C]
/-- A helper construction: given a square between `i` and `f â« g`, produce a square between
`i` and `g`, whose top leg uses `f`:
A  â X
     âf
âi   Y             --> A â Y
     âg                âi  âg
B  â Z                 B â Z
 -/
@[simps] def square_to_snd {X Y Z: C} {i : arrow C} {f : X â¶ Y} {g : Y â¶ Z}
  (sq : i â¶ arrow.mk (f â« g)) :
  i â¶ arrow.mk g :=
{ left := sq.left â« f,
  right := sq.right }

end arrow

namespace functor

universes vâ vâ uâ uâ

variables {C : Type uâ} [category.{vâ} C] {D : Type uâ} [category.{vâ} D]

/-- A functor `C â¥¤ D` induces a functor between the corresponding arrow categories. -/
@[simps]
def map_arrow (F : C â¥¤ D) : arrow C â¥¤ arrow D :=
{ obj := Î» a,
  { left := F.obj a.left,
    right := F.obj a.right,
    hom := F.map a.hom, },
  map := Î» a b f,
  { left := F.map f.left,
    right := F.map f.right,
    w' := by { have w := f.w, simp only [id_map] at w, dsimp, simp only [âF.map_comp, w], } } }

end functor

end category_theory
