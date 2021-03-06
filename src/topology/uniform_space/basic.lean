/-
Copyright (c) 2017 Johannes HΓΆlzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes HΓΆlzl, Mario Carneiro, Patrick Massot
-/
import order.filter.lift
import topology.separation
/-!
# Uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* uniform continuity (in this file)
* completeness (in `cauchy.lean`)
* extension of uniform continuous functions to complete spaces (in `uniform_embedding.lean`)
* totally bounded sets (in `cauchy.lean`)
* totally bounded complete sets are compact (in `cauchy.lean`)

A uniform structure on a type `X` is a filter `π€ X` on `X Γ X` satisfying some conditions
which makes it reasonable to say that `βαΆ  (p : X Γ X) in π€ X, ...` means
"for all p.1 and p.2 in X close enough, ...". Elements of this filter are called entourages
of `X`. The two main examples are:

* If `X` is a metric space, `V β π€ X β β Ξ΅ > 0, { p | dist p.1 p.2 < Ξ΅ } β V`
* If `G` is an additive topological group, `V β π€ G β β U β π (0 : G), {p | p.2 - p.1 β U} β V`

Those examples are generalizations in two different directions of the elementary example where
`X = β` and `V β π€ β β β Ξ΅ > 0, { p | |p.2 - p.1| < Ξ΅ } β V` which features both the topological
group structure on `β` and its metric space structure.

Each uniform structure on `X` induces a topology on `X` characterized by

> `nhds_eq_comap_uniformity : β {x : X}, π x = comap (prod.mk x) (π€ X)`

where `prod.mk x : X β X Γ X := (Ξ» y, (x, y))` is the partial evaluation of the product
constructor.

The dictionary with metric spaces includes:
* an upper bound for `dist x y` translates into `(x, y) β V` for some `V β π€ X`
* a ball `ball x r` roughly corresponds to `uniform_space.ball x V := {y | (x, y) β V}`
  for some `V β π€ X`, but the later is more general (it includes in
  particular both open and closed balls for suitable `V`).
  In particular we have:
  `is_open_iff_ball_subset {s : set X} : is_open s β β x β s, β V β π€ X, ball x V β s`

The triangle inequality is abstracted to a statement involving the composition of relations in `X`.
First note that the triangle inequality in a metric space is equivalent to
`β (x y z : X) (r r' : β), dist x y β€ r β dist y z β€ r' β dist x z β€ r + r'`.
Then, for any `V` and `W` with type `set (X Γ X)`, the composition `V β W : set (X Γ X)` is
defined as `{ p : X Γ X | β z, (p.1, z) β V β§ (z, p.2) β W }`.
In the metric space case, if `V = { p | dist p.1 p.2 β€ r }` and `W = { p | dist p.1 p.2 β€ r' }`
then the triangle inequality, as reformulated above, says `V β W` is contained in
`{p | dist p.1 p.2 β€ r + r'}` which is the entourage associated to the radius `r + r'`.
In general we have `mem_ball_comp (h : y β ball x V) (h' : z β ball y W) : z β ball x (V β W)`.
Note that this discussion does not depend on any axiom imposed on the uniformity filter,
it is simply captured by the definition of composition.

The uniform space axioms ask the filter `π€ X` to satisfy the following:
* every `V β π€ X` contains the diagonal `id_rel = { p | p.1 = p.2 }`. This abstracts the fact
  that `dist x x β€ r` for every non-negative radius `r` in the metric space case and also that
  `x - x` belongs to every neighborhood of zero in the topological group case.
* `V β π€ X β prod.swap '' V β π€ X`. This is tightly related the fact that `dist x y = dist y x`
  in a metric space, and to continuity of negation in the topological group case.
* `β V β π€ X, β W β π€ X, W β W β V`. In the metric space case, it corresponds
  to cutting the radius of a ball in half and applying the triangle inequality.
  In the topological group case, it comes from continuity of addition at `(0, 0)`.

These three axioms are stated more abstractly in the definition below, in terms of
operations on filters, without directly manipulating entourages.

##Β Main definitions

* `uniform_space X` is a uniform space structure on a type `X`
* `uniform_continuous f` is a predicate saying a function `f : Ξ± β Ξ²` between uniform spaces
  is uniformly continuous : `β r β π€ Ξ², βαΆ  (x : Ξ± Γ Ξ±) in π€ Ξ±, (f x.1, f x.2) β r`

In this file we also define a complete lattice structure on the type `uniform_space X`
of uniform structures on `X`, as well as the pullback (`uniform_space.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notations

Localized in `uniformity`, we have the notation `π€ X` for the uniformity on a uniform space `X`,
and `β` for composition of relations, seen as terms with type `set (X Γ X)`.

## Implementation notes

There is already a theory of relations in `data/rel.lean` where the main definition is
`def rel (Ξ± Ξ² : Type*) := Ξ± β Ξ² β Prop`.
The relations used in the current file involve only one type, but this is not the reason why
we don't reuse `data/rel.lean`. We use `set (Ξ± Γ Ξ±)`
instead of `rel Ξ± Ξ±` because we really need sets to use the filter library, and elements
of filters on `Ξ± Γ Ξ±` have type `set (Ξ± Γ Ξ±)`.

The structure `uniform_space X` bundles a uniform structure on `X`, a topology on `X` and
an assumption saying those are compatible. This may not seem mathematically reasonable at first,
but is in fact an instance of the forgetful inheritance pattern. See Note [forgetful inheritance]
below.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/

open set filter classical
open_locale classical topological_space filter

set_option eqn_compiler.zeta true

universes u

/-!
### Relations, seen as `set (Ξ± Γ Ξ±)`
-/
variables {Ξ± : Type*} {Ξ² : Type*} {Ξ³ : Type*} {Ξ΄ : Type*} {ΞΉ : Sort*}

/-- The identity relation, or the graph of the identity function -/
def id_rel {Ξ± : Type*} := {p : Ξ± Γ Ξ± | p.1 = p.2}

@[simp] theorem mem_id_rel {a b : Ξ±} : (a, b) β @id_rel Ξ± β a = b := iff.rfl

@[simp] theorem id_rel_subset {s : set (Ξ± Γ Ξ±)} : id_rel β s β β a, (a, a) β s :=
by simp [subset_def]; exact forall_congr (Ξ» a, by simp)

/-- The composition of relations -/
def comp_rel {Ξ± : Type u} (rβ rβ : set (Ξ±ΓΞ±)) := {p : Ξ± Γ Ξ± | βz:Ξ±, (p.1, z) β rβ β§ (z, p.2) β rβ}

localized "infix ` β `:55 := comp_rel" in uniformity

@[simp] theorem mem_comp_rel {rβ rβ : set (Ξ±ΓΞ±)}
  {x y : Ξ±} : (x, y) β rβ β rβ β β z, (x, z) β rβ β§ (z, y) β rβ := iff.rfl

@[simp] theorem swap_id_rel : prod.swap '' id_rel = @id_rel Ξ± :=
set.ext $ assume β¨a, bβ©, by simp [image_swap_eq_preimage_swap]; exact eq_comm

theorem monotone_comp_rel [preorder Ξ²] {f g : Ξ² β set (Ξ±ΓΞ±)}
  (hf : monotone f) (hg : monotone g) : monotone (Ξ»x, (f x) β (g x)) :=
assume a b h p β¨z, hβ, hββ©, β¨z, hf h hβ, hg h hββ©

@[mono]
lemma comp_rel_mono {f g h k: set (Ξ±ΓΞ±)} (hβ : f β h) (hβ : g β k) : f β g β h β k :=
Ξ» β¨x, yβ© β¨z, h, h'β©, β¨z, hβ h, hβ h'β©

lemma prod_mk_mem_comp_rel {a b c : Ξ±} {s t : set (Ξ±ΓΞ±)} (hβ : (a, c) β s) (hβ : (c, b) β t) :
  (a, b) β s β t :=
β¨c, hβ, hββ©

@[simp] lemma id_comp_rel {r : set (Ξ±ΓΞ±)} : id_rel β r = r :=
set.ext $ assume β¨a, bβ©, by simp

lemma comp_rel_assoc {r s t : set (Ξ±ΓΞ±)} :
  (r β s) β t = r β (s β t) :=
by ext p; cases p; simp only [mem_comp_rel]; tauto

lemma subset_comp_self {Ξ± : Type*} {s : set (Ξ± Γ Ξ±)} (h : id_rel β s) : s β s β s :=
Ξ» β¨x, yβ© xy_in, β¨x, h (by rw mem_id_rel), xy_inβ©

/-- The relation is invariant under swapping factors. -/
def symmetric_rel (V : set (Ξ± Γ Ξ±)) : Prop := prod.swap β»ΒΉ' V = V

/-- The maximal symmetric relation contained in a given relation. -/
def symmetrize_rel (V : set (Ξ± Γ Ξ±)) : set (Ξ± Γ Ξ±) := V β© prod.swap β»ΒΉ' V

lemma symmetric_symmetrize_rel (V : set (Ξ± Γ Ξ±)) : symmetric_rel (symmetrize_rel V) :=
by simp [symmetric_rel, symmetrize_rel, preimage_inter, inter_comm, β preimage_comp]

lemma symmetrize_rel_subset_self (V : set (Ξ± Γ Ξ±)) : symmetrize_rel V β V :=
sep_subset _ _

@[mono]
lemma symmetrize_mono {V W: set (Ξ± Γ Ξ±)} (h : V β W) : symmetrize_rel V β symmetrize_rel W :=
inter_subset_inter h $ preimage_mono h

lemma symmetric_rel_inter {U V : set (Ξ± Γ Ξ±)} (hU : symmetric_rel U) (hV : symmetric_rel V) :
symmetric_rel (U β© V) :=
begin
  unfold symmetric_rel at *,
  rw [preimage_inter, hU, hV],
end

/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure uniform_space.core (Ξ± : Type u) :=
(uniformity : filter (Ξ± Γ Ξ±))
(refl       : π id_rel β€ uniformity)
(symm       : tendsto prod.swap uniformity uniformity)
(comp       : uniformity.lift' (Ξ»s, s β s) β€ uniformity)

/-- An alternative constructor for `uniform_space.core`. This version unfolds various
`filter`-related definitions. -/
def uniform_space.core.mk' {Ξ± : Type u} (U : filter (Ξ± Γ Ξ±))
  (refl : β (r β U) x, (x, x) β r)
  (symm : β r β U, prod.swap β»ΒΉ' r β U)
  (comp : β r β U, β t β U, t β t β r) : uniform_space.core Ξ± :=
β¨U, Ξ» r ru, id_rel_subset.2 (refl _ ru), symm,
  begin
    intros r ru,
    rw [mem_lift'_sets],
    exact comp _ ru,
    apply monotone_comp_rel; exact monotone_id,
  endβ©

/-- A uniform space generates a topological space -/
def uniform_space.core.to_topological_space {Ξ± : Type u} (u : uniform_space.core Ξ±) :
  topological_space Ξ± :=
{ is_open        := Ξ»s, βxβs, { p : Ξ± Γ Ξ± | p.1 = x β p.2 β s } β u.uniformity,
  is_open_univ   := by simp; intro; exact univ_mem_sets,
  is_open_inter  :=
    assume s t hs ht x β¨xs, xtβ©, by filter_upwards [hs x xs, ht x xt]; simp {contextual := tt},
  is_open_sUnion :=
    assume s hs x β¨t, ts, xtβ©, by filter_upwards [hs t ts x xt] assume p ph h, β¨t, ts, ph hβ© }

lemma uniform_space.core_eq :
  β{uβ uβ : uniform_space.core Ξ±}, uβ.uniformity = uβ.uniformity β uβ = uβ
| β¨uβ, _, _, _β©  β¨uβ, _, _, _β© h := by { congr, exact h }

-- the topological structure is embedded in the uniform structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].

/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `Ξ± Γ Ξ±` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
class uniform_space (Ξ± : Type u) extends topological_space Ξ±, uniform_space.core Ξ± :=
(is_open_uniformity : βs, is_open s β (βxβs, { p : Ξ± Γ Ξ± | p.1 = x β p.2 β s } β uniformity))

/-- Alternative constructor for `uniform_space Ξ±` when a topology is already given. -/
@[pattern] def uniform_space.mk' {Ξ±} (t : topological_space Ξ±)
  (c : uniform_space.core Ξ±)
  (is_open_uniformity : βs:set Ξ±, t.is_open s β
    (βxβs, { p : Ξ± Γ Ξ± | p.1 = x β p.2 β s } β c.uniformity)) :
  uniform_space Ξ± := β¨c, is_open_uniformityβ©

/-- Construct a `uniform_space` from a `uniform_space.core`. -/
def uniform_space.of_core {Ξ± : Type u} (u : uniform_space.core Ξ±) : uniform_space Ξ± :=
{ to_core := u,
  to_topological_space := u.to_topological_space,
  is_open_uniformity := assume a, iff.rfl }

/-- Construct a `uniform_space` from a `u : uniform_space.core` and a `topological_space` structure
that is equal to `u.to_topological_space`. -/
def uniform_space.of_core_eq {Ξ± : Type u} (u : uniform_space.core Ξ±) (t : topological_space Ξ±)
  (h : t = u.to_topological_space) : uniform_space Ξ± :=
{ to_core := u,
  to_topological_space := t,
  is_open_uniformity := assume a, h.symm βΈ iff.rfl }

lemma uniform_space.to_core_to_topological_space (u : uniform_space Ξ±) :
  u.to_core.to_topological_space = u.to_topological_space :=
topological_space_eq $ funext $ assume s,
  by rw [uniform_space.core.to_topological_space, uniform_space.is_open_uniformity]

@[ext]
lemma uniform_space_eq : β{uβ uβ : uniform_space Ξ±}, uβ.uniformity = uβ.uniformity β uβ = uβ
| (uniform_space.mk' tβ uβ oβ)  (uniform_space.mk' tβ uβ oβ) h :=
  have uβ = uβ, from uniform_space.core_eq h,
  have tβ = tβ, from topological_space_eq $ funext $ assume s, by rw [oβ, oβ]; simp [this],
  by simp [*]

lemma uniform_space.of_core_eq_to_core
  (u : uniform_space Ξ±) (t : topological_space Ξ±) (h : t = u.to_core.to_topological_space) :
  uniform_space.of_core_eq u.to_core t h = u :=
uniform_space_eq rfl

section uniform_space
variables [uniform_space Ξ±]

/-- The uniformity is a filter on Ξ± Γ Ξ± (inferred from an ambient uniform space
  structure on Ξ±). -/
def uniformity (Ξ± : Type u) [uniform_space Ξ±] : filter (Ξ± Γ Ξ±) :=
  (@uniform_space.to_core Ξ± _).uniformity

localized "notation `π€` := uniformity" in uniformity

lemma is_open_uniformity {s : set Ξ±} :
  is_open s β (βxβs, { p : Ξ± Γ Ξ± | p.1 = x β p.2 β s } β π€ Ξ±) :=
uniform_space.is_open_uniformity s

lemma refl_le_uniformity : π id_rel β€ π€ Ξ± :=
(@uniform_space.to_core Ξ± _).refl

lemma refl_mem_uniformity {x : Ξ±} {s : set (Ξ± Γ Ξ±)} (h : s β π€ Ξ±) :
  (x, x) β s :=
refl_le_uniformity h rfl

lemma symm_le_uniformity : map (@prod.swap Ξ± Ξ±) (π€ _) β€ (π€ _) :=
(@uniform_space.to_core Ξ± _).symm

lemma comp_le_uniformity : (π€ Ξ±).lift' (Ξ»s:set (Ξ±ΓΞ±), s β s) β€ π€ Ξ± :=
(@uniform_space.to_core Ξ± _).comp

lemma tendsto_swap_uniformity : tendsto (@prod.swap Ξ± Ξ±) (π€ Ξ±) (π€ Ξ±) :=
symm_le_uniformity

lemma comp_mem_uniformity_sets {s : set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) :
  β t β π€ Ξ±, t β t β s :=
have s β (π€ Ξ±).lift' (Ξ»t:set (Ξ±ΓΞ±), t β t),
  from comp_le_uniformity hs,
(mem_lift'_sets $ monotone_comp_rel monotone_id monotone_id).mp this

/-- Relation `Ξ» f g, tendsto (Ξ» x, (f x, g x)) l (π€ Ξ±)` is transitive. -/
lemma filter.tendsto.uniformity_trans {l : filter Ξ²} {fβ fβ fβ : Ξ² β Ξ±}
  (hββ : tendsto (Ξ» x, (fβ x, fβ x)) l (π€ Ξ±)) (hββ : tendsto (Ξ» x, (fβ x, fβ x)) l (π€ Ξ±)) :
  tendsto (Ξ» x, (fβ x, fβ x)) l (π€ Ξ±) :=
begin
  refine le_trans (le_lift' $ Ξ» s hs, mem_map.2 _) comp_le_uniformity,
  filter_upwards [hββ hs, hββ hs],
  exact Ξ» x hxββ hxββ, β¨_, hxββ, hxβββ©
end

/-- Relation `Ξ» f g, tendsto (Ξ» x, (f x, g x)) l (π€ Ξ±)` is symmetric -/
lemma filter.tendsto.uniformity_symm {l : filter Ξ²} {f : Ξ² β Ξ± Γ Ξ±}
  (h : tendsto f l (π€ Ξ±)) :
  tendsto (Ξ» x, ((f x).2, (f x).1)) l (π€ Ξ±) :=
tendsto_swap_uniformity.comp h

/-- Relation `Ξ» f g, tendsto (Ξ» x, (f x, g x)) l (π€ Ξ±)` is reflexive. -/
lemma tendsto_diag_uniformity (f : Ξ² β Ξ±) (l : filter Ξ²) :
  tendsto (Ξ» x, (f x, f x)) l (π€ Ξ±) :=
assume s hs, mem_map.2 $ univ_mem_sets' $ Ξ» x, refl_mem_uniformity hs

lemma tendsto_const_uniformity {a : Ξ±} {f : filter Ξ²} : tendsto (Ξ» _, (a, a)) f (π€ Ξ±) :=
tendsto_diag_uniformity (Ξ» _, a) f

lemma symm_of_uniformity {s : set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) :
  β t β π€ Ξ±, (βa b, (a, b) β t β (b, a) β t) β§ t β s :=
have preimage prod.swap s β π€ Ξ±, from symm_le_uniformity hs,
β¨s β© preimage prod.swap s, inter_mem_sets hs this, Ξ» a b β¨hβ, hββ©, β¨hβ, hββ©, inter_subset_left _ _β©

lemma comp_symm_of_uniformity {s : set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) :
  β t β π€ Ξ±, (β{a b}, (a, b) β t β (b, a) β t) β§ t β t β s :=
let β¨t, htβ, htββ© := comp_mem_uniformity_sets hs in
let β¨t', ht', ht'β, ht'ββ© := symm_of_uniformity htβ in
β¨t', ht', ht'β, subset.trans (monotone_comp_rel monotone_id monotone_id ht'β) htββ©

lemma uniformity_le_symm : π€ Ξ± β€ (@prod.swap Ξ± Ξ±) <$> π€ Ξ± :=
by rw [map_swap_eq_comap_swap];
from map_le_iff_le_comap.1 tendsto_swap_uniformity

lemma uniformity_eq_symm : π€ Ξ± = (@prod.swap Ξ± Ξ±) <$> π€ Ξ± :=
le_antisymm uniformity_le_symm symm_le_uniformity

lemma symmetrize_mem_uniformity {V : set (Ξ± Γ Ξ±)} (h : V β π€ Ξ±) : symmetrize_rel V β π€ Ξ± :=
begin
  apply (π€ Ξ±).inter_sets h,
  rw [β image_swap_eq_preimage_swap, uniformity_eq_symm],
  exact image_mem_map h,
end

theorem uniformity_lift_le_swap {g : set (Ξ±ΓΞ±) β filter Ξ²} {f : filter Ξ²} (hg : monotone g)
  (h : (π€ Ξ±).lift (Ξ»s, g (preimage prod.swap s)) β€ f) : (π€ Ξ±).lift g β€ f :=
calc (π€ Ξ±).lift g β€ (filter.map (@prod.swap Ξ± Ξ±) $ π€ Ξ±).lift g :
    lift_mono uniformity_le_symm (le_refl _)
  ... β€ _ :
    by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h

lemma uniformity_lift_le_comp {f : set (Ξ±ΓΞ±) β filter Ξ²} (h : monotone f) :
  (π€ Ξ±).lift (Ξ»s, f (s β s)) β€ (π€ Ξ±).lift f :=
calc (π€ Ξ±).lift (Ξ»s, f (s β s)) =
    ((π€ Ξ±).lift' (Ξ»s:set (Ξ±ΓΞ±), s β s)).lift f :
  begin
    rw [lift_lift'_assoc],
    exact monotone_comp_rel monotone_id monotone_id,
    exact h
  end
  ... β€ (π€ Ξ±).lift f : lift_mono comp_le_uniformity (le_refl _)

lemma comp_le_uniformity3 :
  (π€ Ξ±).lift' (Ξ»s:set (Ξ±ΓΞ±), s β (s β s)) β€ (π€ Ξ±) :=
calc (π€ Ξ±).lift' (Ξ»d, d β (d β d)) =
  (π€ Ξ±).lift (Ξ»s, (π€ Ξ±).lift' (Ξ»t:set(Ξ±ΓΞ±), s β (t β t))) :
  begin
    rw [lift_lift'_same_eq_lift'],
    exact (assume x, monotone_comp_rel monotone_const $ monotone_comp_rel monotone_id monotone_id),
    exact (assume x, monotone_comp_rel monotone_id monotone_const),
  end
  ... β€ (π€ Ξ±).lift (Ξ»s, (π€ Ξ±).lift' (Ξ»t:set(Ξ±ΓΞ±), s β t)) :
    lift_mono' $ assume s hs, @uniformity_lift_le_comp Ξ± _ _ (π β (β) s) $
      monotone_principal.comp (monotone_comp_rel monotone_const monotone_id)
  ... = (π€ Ξ±).lift' (Ξ»s:set(Ξ±ΓΞ±), s β s) :
    lift_lift'_same_eq_lift'
      (assume s, monotone_comp_rel monotone_const monotone_id)
      (assume s, monotone_comp_rel monotone_id monotone_const)
  ... β€ (π€ Ξ±) : comp_le_uniformity

lemma comp_symm_mem_uniformity_sets {s : set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) :
  β t β π€ Ξ±, symmetric_rel t β§ t β t β s :=
begin
  obtain β¨w, w_in, w_subβ© : β w β π€ Ξ±, w β w β s := comp_mem_uniformity_sets hs,
  use [symmetrize_rel w, symmetrize_mem_uniformity w_in, symmetric_symmetrize_rel w],
  have : symmetrize_rel w β w := symmetrize_rel_subset_self w,
  calc symmetrize_rel w β symmetrize_rel w β w β w : by mono
                                       ... β s     : w_sub,
end

lemma subset_comp_self_of_mem_uniformity {s : set (Ξ± Γ Ξ±)} (h : s β π€ Ξ±) : s β s β s :=
subset_comp_self (refl_le_uniformity h)

lemma comp_comp_symm_mem_uniformity_sets {s : set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) :
  β t β π€ Ξ±, symmetric_rel t β§ t β t β t β s :=
begin
  rcases comp_symm_mem_uniformity_sets hs with β¨w, w_in, w_symm, w_subβ©,
  rcases comp_symm_mem_uniformity_sets w_in with β¨t, t_in, t_symm, t_subβ©,
  use [t, t_in, t_symm],
  have : t β t β t :=  subset_comp_self_of_mem_uniformity t_in,
  calc
  t β t β t β w β t       : by mono
        ... β w β (t β t) : by mono
        ... β w β w       : by mono
        ... β s           : w_sub,
end

/-!
###Β Balls in uniform spaces
-/

/-- The ball around `(x : Ξ²)` with respect to `(V : set (Ξ² Γ Ξ²))`. Intended to be
used for `V β π€ Ξ²`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`.  -/
def uniform_space.ball (x : Ξ²) (V : set (Ξ² Γ Ξ²)) : set Ξ² := (prod.mk x) β»ΒΉ' V

open uniform_space (ball)

lemma uniform_space.mem_ball_self (x : Ξ±) {V : set (Ξ± Γ Ξ±)} (hV : V β π€ Ξ±) :
  x β ball x V :=
refl_mem_uniformity hV

/-- The triangle inequality for `uniform_space.ball` -/
lemma mem_ball_comp {V W : set (Ξ² Γ Ξ²)} {x y z} (h : y β ball x V) (h' : z β ball y W) :
  z β ball x (V β W) :=
prod_mk_mem_comp_rel h h'

lemma ball_subset_of_comp_subset {V W : set (Ξ² Γ Ξ²)} {x y} (h : x β ball y W) (h' : W β W β V) :
  ball x W β ball y V :=
Ξ» z z_in, h' (mem_ball_comp h z_in)

lemma ball_mono {V W : set (Ξ² Γ Ξ²)} (h : V β W) (x : Ξ²) : ball x V β ball x W :=
by tauto

lemma mem_ball_symmetry {V : set (Ξ² Γ Ξ²)} (hV : symmetric_rel V) {x y} :
  x β ball y V β y β ball x V :=
show (x, y) β prod.swap β»ΒΉ' V β (x, y) β V, by { unfold symmetric_rel at hV, rw hV }

lemma ball_eq_of_symmetry {V : set (Ξ² Γ Ξ²)} (hV : symmetric_rel V) {x} :
  ball x V = {y | (y, x) β V} :=
by { ext y, rw mem_ball_symmetry hV, exact iff.rfl }

lemma mem_comp_of_mem_ball {V W : set (Ξ² Γ Ξ²)} {x y z : Ξ²} (hV : symmetric_rel V)
  (hx : x β ball z V) (hy : y β ball z W) : (x, y) β V β W :=
begin
  rw mem_ball_symmetry hV at hx,
  exact β¨z, hx, hyβ©
end

lemma uniform_space.is_open_ball (x : Ξ±) {V : set (Ξ± Γ Ξ±)} (hV : is_open V) :
  is_open (ball x V) :=
hV.preimage $ continuous_const.prod_mk continuous_id

lemma mem_comp_comp {V W M : set (Ξ² Γ Ξ²)} (hW' : symmetric_rel W) {p : Ξ² Γ Ξ²} :
  p β V β M β W β ((ball p.1 V).prod (ball p.2 W) β© M).nonempty :=
begin
  cases p with x y,
  split,
  { rintros β¨z, β¨w, hpw, hwzβ©, hzyβ©,
    exact β¨(w, z), β¨hpw, by rwa mem_ball_symmetry hW'β©, hwzβ©, },
  { rintro β¨β¨w, zβ©, β¨w_in, z_inβ©, hwzβ©,
    rwa mem_ball_symmetry hW' at z_in,
    use [z, w] ; tauto },
end

/-!
### Neighborhoods in uniform spaces
-/

lemma mem_nhds_uniformity_iff_right {x : Ξ±} {s : set Ξ±} :
  s β π x β {p : Ξ± Γ Ξ± | p.1 = x β p.2 β s} β π€ Ξ± :=
β¨ begin
    simp only [mem_nhds_sets_iff, is_open_uniformity, and_imp, exists_imp_distrib],
    exact assume t ts ht xt, by filter_upwards [ht x xt] assume β¨x', yβ© h eq, ts $ h eq
  end,

  assume hs,
  mem_nhds_sets_iff.mpr β¨{x | {p : Ξ± Γ Ξ± | p.1 = x β p.2 β s} β π€ Ξ±},
    assume x' hx', refl_mem_uniformity hx' rfl,
    is_open_uniformity.mpr $ assume x' hx',
      let β¨t, ht, trβ© := comp_mem_uniformity_sets hx' in
      by filter_upwards [ht] assume β¨a, bβ© hp' (hax' : a = x'),
      by filter_upwards [ht] assume β¨a, b'β© hp'' (hab : a = b),
      have hp : (x', b) β t, from hax' βΈ hp',
      have (b, b') β t, from hab βΈ hp'',
      have (x', b') β t β t, from β¨b, hp, thisβ©,
      show b' β s,
        from tr this rfl,
    hsβ©β©

lemma mem_nhds_uniformity_iff_left {x : Ξ±} {s : set Ξ±} :
  s β π x β {p : Ξ± Γ Ξ± | p.2 = x β p.1 β s} β π€ Ξ± :=
by { rw [uniformity_eq_symm, mem_nhds_uniformity_iff_right], refl }

lemma nhds_eq_comap_uniformity_aux  {Ξ± : Type u} {x : Ξ±} {s : set Ξ±} {F : filter (Ξ± Γ Ξ±)} :
  {p : Ξ± Γ Ξ± | p.fst = x β p.snd β s} β F β s β comap (prod.mk x) F :=
by rw mem_comap_sets ; from iff.intro
  (assume hs, β¨_, hs, assume x hx, hx rflβ©)
  (assume β¨t, h, htβ©, F.sets_of_superset h $
    assume β¨pβ, pββ© hp (h : pβ = x), ht $ by simp [h.symm, hp])


lemma nhds_eq_comap_uniformity {x : Ξ±} : π x = (π€ Ξ±).comap (prod.mk x) :=
by { ext s, rw [mem_nhds_uniformity_iff_right], exact nhds_eq_comap_uniformity_aux }

lemma is_open_iff_ball_subset {s : set Ξ±} : is_open s β β x β s, β V β π€ Ξ±, ball x V β s :=
begin
  simp_rw [is_open_iff_mem_nhds, nhds_eq_comap_uniformity],
  exact iff.rfl,
end

lemma nhds_basis_uniformity' {p : Ξ² β Prop} {s : Ξ² β set (Ξ± Γ Ξ±)} (h : (π€ Ξ±).has_basis p s)
  {x : Ξ±} :
  (π x).has_basis p (Ξ» i, ball x (s i)) :=
by { rw [nhds_eq_comap_uniformity], exact h.comap (prod.mk x) }

lemma nhds_basis_uniformity {p : Ξ² β Prop} {s : Ξ² β set (Ξ± Γ Ξ±)} (h : (π€ Ξ±).has_basis p s) {x : Ξ±} :
  (π x).has_basis p (Ξ» i, {y | (y, x) β s i}) :=
begin
  replace h := h.comap prod.swap,
  rw [β map_swap_eq_comap_swap, β uniformity_eq_symm] at h,
  exact nhds_basis_uniformity' h
end

lemma uniform_space.mem_nhds_iff {x : Ξ±} {s : set Ξ±} : s β π x β β V β π€ Ξ±, ball x V β s :=
begin
  rw [nhds_eq_comap_uniformity, mem_comap_sets],
  exact iff.rfl,
end

lemma uniform_space.ball_mem_nhds (x : Ξ±) β¦V : set (Ξ± Γ Ξ±)β¦ (V_in : V β π€ Ξ±) : ball x V β π x :=
begin
  rw uniform_space.mem_nhds_iff,
  exact β¨V, V_in, subset.refl _β©
end

lemma uniform_space.mem_nhds_iff_symm {x : Ξ±} {s : set Ξ±} :
  s β π x β β V β π€ Ξ±, symmetric_rel V β§ ball x V β s :=
begin
  rw uniform_space.mem_nhds_iff,
  split,
  { rintros β¨V, V_in, V_subβ©,
    use [symmetrize_rel V, symmetrize_mem_uniformity V_in, symmetric_symmetrize_rel V],
    exact subset.trans (ball_mono (symmetrize_rel_subset_self V) x) V_sub },
  { rintros β¨V, V_in, V_symm, V_subβ©,
    exact β¨V, V_in, V_subβ© }
end

lemma uniform_space.has_basis_nhds (x : Ξ±) :
  has_basis (π x) (Ξ» s : set (Ξ± Γ Ξ±), s β π€ Ξ± β§ symmetric_rel s) (Ξ» s, ball x s) :=
β¨Ξ» t, by simp [uniform_space.mem_nhds_iff_symm, and_assoc]β©

open uniform_space

lemma uniform_space.has_basis_nhds_prod (x y : Ξ±) :
  has_basis (π (x, y)) (Ξ» s, s β π€ Ξ± β§ symmetric_rel s) $ Ξ» s, (ball x s).prod (ball y s) :=
begin
  rw nhds_prod_eq,
  apply (has_basis_nhds x).prod' (has_basis_nhds y),
  rintro U V β¨U_in, U_symmβ© β¨V_in, V_symmβ©,
  exact β¨U β© V, β¨(π€ Ξ±).inter_sets U_in V_in, symmetric_rel_inter U_symm V_symmβ©,
         ball_mono (inter_subset_left U V) x, ball_mono (inter_subset_right U V) yβ©,
end

lemma nhds_eq_uniformity {x : Ξ±} : π x = (π€ Ξ±).lift' (ball x) :=
(nhds_basis_uniformity' (π€ Ξ±).basis_sets).eq_binfi

lemma mem_nhds_left (x : Ξ±) {s : set (Ξ±ΓΞ±)} (h : s β π€ Ξ±) :
  {y : Ξ± | (x, y) β s} β π x :=
ball_mem_nhds x h

lemma mem_nhds_right (y : Ξ±) {s : set (Ξ±ΓΞ±)} (h : s β π€ Ξ±) :
  {x : Ξ± | (x, y) β s} β π y :=
mem_nhds_left _ (symm_le_uniformity h)

lemma tendsto_right_nhds_uniformity {a : Ξ±} : tendsto (Ξ»a', (a', a)) (π a) (π€ Ξ±) :=
assume s, mem_nhds_right a

lemma tendsto_left_nhds_uniformity {a : Ξ±} : tendsto (Ξ»a', (a, a')) (π a) (π€ Ξ±) :=
assume s, mem_nhds_left a

lemma lift_nhds_left {x : Ξ±} {g : set Ξ± β filter Ξ²} (hg : monotone g) :
  (π x).lift g = (π€ Ξ±).lift (Ξ»s:set (Ξ±ΓΞ±), g {y | (x, y) β s}) :=
eq.trans
  begin
    rw [nhds_eq_uniformity],
    exact (filter.lift_assoc $ monotone_principal.comp $ monotone_preimage.comp monotone_preimage )
  end
  (congr_arg _ $ funext $ assume s, filter.lift_principal hg)

lemma lift_nhds_right {x : Ξ±} {g : set Ξ± β filter Ξ²} (hg : monotone g) :
  (π x).lift g = (π€ Ξ±).lift (Ξ»s:set (Ξ±ΓΞ±), g {y | (y, x) β s}) :=
calc (π x).lift g = (π€ Ξ±).lift (Ξ»s:set (Ξ±ΓΞ±), g {y | (x, y) β s}) : lift_nhds_left hg
  ... = ((@prod.swap Ξ± Ξ±) <$> (π€ Ξ±)).lift (Ξ»s:set (Ξ±ΓΞ±), g {y | (x, y) β s}) :
    by rw [βuniformity_eq_symm]
  ... = (π€ Ξ±).lift (Ξ»s:set (Ξ±ΓΞ±), g {y | (x, y) β image prod.swap s}) :
    map_lift_eq2 $ hg.comp monotone_preimage
  ... = _ : by simp [image_swap_eq_preimage_swap]

lemma nhds_nhds_eq_uniformity_uniformity_prod {a b : Ξ±} :
  π a ΓαΆ  π b =
  (π€ Ξ±).lift (Ξ»s:set (Ξ±ΓΞ±), (π€ Ξ±).lift' (Ξ»t:set (Ξ±ΓΞ±),
    set.prod {y : Ξ± | (y, a) β s} {y : Ξ± | (b, y) β t})) :=
begin
  rw [prod_def],
  show (π a).lift (Ξ»s:set Ξ±, (π b).lift (Ξ»t:set Ξ±, π (set.prod s t))) = _,
  rw [lift_nhds_right],
  apply congr_arg, funext s,
  rw [lift_nhds_left],
  refl,
  exact monotone_principal.comp (monotone_prod monotone_const monotone_id),
  exact (monotone_lift' monotone_const $ monotone_lam $
    assume x, monotone_prod monotone_id monotone_const)
end

lemma nhds_eq_uniformity_prod {a b : Ξ±} :
  π (a, b) =
  (π€ Ξ±).lift' (Ξ»s:set (Ξ±ΓΞ±), set.prod {y : Ξ± | (y, a) β s} {y : Ξ± | (b, y) β s}) :=
begin
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift'],
  { intro s, exact monotone_prod monotone_const monotone_preimage },
  { intro t, exact monotone_prod monotone_preimage monotone_const }
end

lemma nhdset_of_mem_uniformity {d : set (Ξ±ΓΞ±)} (s : set (Ξ±ΓΞ±)) (hd : d β π€ Ξ±) :
  β(t : set (Ξ±ΓΞ±)), is_open t β§ s β t β§ t β {p | βx y, (p.1, x) β d β§ (x, y) β s β§ (y, p.2) β d} :=
let cl_d := {p:Ξ±ΓΞ± | βx y, (p.1, x) β d β§ (x, y) β s β§ (y, p.2) β d} in
have βp β s, βt β cl_d, is_open t β§ p β t, from
  assume β¨x, yβ© hp, mem_nhds_sets_iff.mp $
  show cl_d β π (x, y),
  begin
    rw [nhds_eq_uniformity_prod, mem_lift'_sets],
    exact β¨d, hd, assume β¨a, bβ© β¨ha, hbβ©, β¨x, y, ha, hp, hbβ©β©,
    exact monotone_prod monotone_preimage monotone_preimage
  end,
have βt:(Ξ (p:Ξ±ΓΞ±) (h:p β s), set (Ξ±ΓΞ±)),
    βp, βh:p β s, t p h β cl_d β§ is_open (t p h) β§ p β t p h,
  by simp [classical.skolem] at this; simp; assumption,
match this with
| β¨t, htβ© :=
  β¨(β p:Ξ±ΓΞ±, β h : p β s, t p h : set (Ξ±ΓΞ±)),
    is_open_Union $ assume (p:Ξ±ΓΞ±), is_open_Union $ assume hp, (ht p hp).right.left,
    assume β¨a, bβ© hp, begin simp; exact β¨a, b, hp, (ht (a,b) hp).right.rightβ© end,
    Union_subset $ assume p, Union_subset $ assume hp, (ht p hp).leftβ©
end

/-- Entourages are neighborhoods of the diagonal. -/
lemma nhds_le_uniformity (x : Ξ±) : π (x, x) β€ π€ Ξ± :=
begin
  intros V V_in,
  rcases comp_symm_mem_uniformity_sets V_in with β¨w, w_in, w_symm, w_subβ©,
  have : (ball x w).prod (ball x w) β π (x, x),
  { rw nhds_prod_eq,
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in) },
  apply mem_sets_of_superset this,
  rintros β¨u, vβ© β¨u_in, v_inβ©,
  exact w_sub (mem_comp_of_mem_ball w_symm u_in v_in)
end

/-- Entourages are neighborhoods of the diagonal. -/
lemma supr_nhds_le_uniformity : (β¨ x : Ξ±, π (x, x)) β€ π€ Ξ± :=
supr_le nhds_le_uniformity

/-!
### Closure and interior in uniform spaces
-/

lemma closure_eq_uniformity (s : set $ Ξ± Γ Ξ±) :
  closure s = β V β {V | V β π€ Ξ± β§ symmetric_rel V}, V β s β V :=
begin
  ext β¨x, yβ©,
  simp_rw [mem_closure_iff_nhds_basis (uniform_space.has_basis_nhds_prod x y),
           mem_Inter, mem_set_of_eq],
  apply forall_congr,
  intro V,
  apply forall_congr,
  rintros β¨V_in, V_symmβ©,
  simp_rw [mem_comp_comp V_symm, inter_comm, exists_prop],
  exact iff.rfl,
end

lemma uniformity_has_basis_closed : has_basis (π€ Ξ±) (Ξ» V : set (Ξ± Γ Ξ±), V β π€ Ξ± β§ is_closed V) id :=
begin
  refine filter.has_basis_self.2 (Ξ» t h, _),
  rcases comp_comp_symm_mem_uniformity_sets h with β¨w, w_in, w_symm, rβ©,
  refine β¨closure w, mem_sets_of_superset w_in subset_closure, is_closed_closure, _β©,
  refine subset.trans _ r,
  rw closure_eq_uniformity,
  apply Inter_subset_of_subset,
  apply Inter_subset,
  exact β¨w_in, w_symmβ©
end

/-- Closed entourages form a basis of the uniformity filter. -/
lemma uniformity_has_basis_closure : has_basis (π€ Ξ±) (Ξ» V : set (Ξ± Γ Ξ±), V β π€ Ξ±) closure :=
β¨begin
  intro t,
  rw uniformity_has_basis_closed.mem_iff,
  split,
  { rintros β¨r, β¨r_in, r_closedβ©, r_subβ©,
    use [r, r_in],
    convert r_sub,
    rw r_closed.closure_eq,
    refl },
  { rintros β¨r, r_in, r_subβ©,
    exact β¨closure r, β¨mem_sets_of_superset r_in subset_closure, is_closed_closureβ©, r_subβ© }
endβ©

lemma closure_eq_inter_uniformity {t : set (Ξ±ΓΞ±)} :
  closure t = (β d β π€ Ξ±, d β (t β d)) :=
set.ext $ assume β¨a, bβ©,
calc (a, b) β closure t β (π (a, b) β π t β  β₯) : mem_closure_iff_nhds_ne_bot
  ... β (((@prod.swap Ξ± Ξ±) <$> π€ Ξ±).lift'
      (Ξ» (s : set (Ξ± Γ Ξ±)), set.prod {x : Ξ± | (x, a) β s} {y : Ξ± | (b, y) β s}) β π t β  β₯) :
    by rw [βuniformity_eq_symm, nhds_eq_uniformity_prod]
  ... β ((map (@prod.swap Ξ± Ξ±) (π€ Ξ±)).lift'
      (Ξ» (s : set (Ξ± Γ Ξ±)), set.prod {x : Ξ± | (x, a) β s} {y : Ξ± | (b, y) β s}) β π t β  β₯) :
    by refl
  ... β ((π€ Ξ±).lift'
      (Ξ» (s : set (Ξ± Γ Ξ±)), set.prod {y : Ξ± | (a, y) β s} {x : Ξ± | (x, b) β s}) β π t β  β₯) :
  begin
    rw [map_lift'_eq2],
    simp [image_swap_eq_preimage_swap, function.comp],
    exact monotone_prod monotone_preimage monotone_preimage
  end
  ... β (βs β π€ Ξ±, (set.prod {y : Ξ± | (a, y) β s} {x : Ξ± | (x, b) β s} β© t).nonempty) :
  begin
    rw [lift'_inf_principal_eq, β ne_bot_iff, lift'_ne_bot_iff],
    exact monotone_inter (monotone_prod monotone_preimage monotone_preimage) monotone_const
  end
  ... β (β s β π€ Ξ±, (a, b) β s β (t β s)) :
    forall_congr $ assume s, forall_congr $ assume hs,
    β¨assume β¨β¨x, yβ©, β¨β¨hx, hyβ©, hxytβ©β©, β¨x, hx, y, hxyt, hyβ©,
      assume β¨x, hx, y, hxyt, hyβ©, β¨β¨x, yβ©, β¨β¨hx, hyβ©, hxytβ©β©β©
  ... β _ : by simp

lemma uniformity_eq_uniformity_closure : π€ Ξ± = (π€ Ξ±).lift' closure :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, by simp; filter_upwards [hs] subset_closure)
  (calc (π€ Ξ±).lift' closure β€ (π€ Ξ±).lift' (Ξ»d, d β (d β d)) :
      lift'_mono' (by intros s hs; rw [closure_eq_inter_uniformity]; exact bInter_subset_of_mem hs)
    ... β€ (π€ Ξ±) : comp_le_uniformity3)

lemma uniformity_eq_uniformity_interior : π€ Ξ± = (π€ Ξ±).lift' interior :=
le_antisymm
  (le_infi $ assume d, le_infi $ assume hd,
    let β¨s, hs, hs_compβ© := (mem_lift'_sets $
      monotone_comp_rel monotone_id $ monotone_comp_rel monotone_id monotone_id).mp
        (comp_le_uniformity3 hd) in
    let β¨t, ht, hst, ht_compβ© := nhdset_of_mem_uniformity s hs in
    have s β interior d, from
      calc s β t : hst
       ... β interior d : (subset_interior_iff_subset_of_open ht).mpr $
        Ξ» x (hx : x β t), let β¨x, y, hβ, hβ, hββ© := ht_comp hx in hs_comp β¨x, hβ, y, hβ, hββ©,
    have interior d β π€ Ξ±, by filter_upwards [hs] this,
    by simp [this])
  (assume s hs, ((π€ Ξ±).lift' interior).sets_of_superset (mem_lift' hs) interior_subset)

lemma interior_mem_uniformity {s : set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) :
  interior s β π€ Ξ± :=
by rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs

lemma mem_uniformity_is_closed {s : set (Ξ±ΓΞ±)} (h : s β π€ Ξ±) :
  βt β π€ Ξ±, is_closed t β§ t β s :=
let β¨t, β¨ht_mem, htcβ©, htsβ© := uniformity_has_basis_closed.mem_iff.1 h in
β¨t, ht_mem, htc, htsβ©

/-- The uniform neighborhoods of all points of a dense set cover the whole space. -/
lemma dense.bUnion_uniformity_ball {s : set Ξ±} {U : set (Ξ± Γ Ξ±)} (hs : dense s) (hU : U β π€ Ξ±) :
  (β x β s, ball x U) = univ :=
begin
  refine bUnion_eq_univ_iff.2 (Ξ» y, _),
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with β¨x, hxs, hxy : (x, y) β Uβ©,
  exact β¨x, hxs, hxyβ©
end

/-!
### Uniformity bases
-/

/-- Open elements of `π€ Ξ±` form a basis of `π€ Ξ±`. -/
lemma uniformity_has_basis_open : has_basis (π€ Ξ±) (Ξ» V : set (Ξ± Γ Ξ±), V β π€ Ξ± β§ is_open V) id :=
has_basis_self.2 $ Ξ» s hs,
  β¨interior s, interior_mem_uniformity hs, is_open_interior, interior_subsetβ©

lemma filter.has_basis.mem_uniformity_iff {p : Ξ² β Prop} {s : Ξ² β set (Ξ±ΓΞ±)}
  (h : (π€ Ξ±).has_basis p s) {t : set (Ξ± Γ Ξ±)} :
  t β π€ Ξ± β β i (hi : p i), β a b, (a, b) β s i β (a, b) β t :=
h.mem_iff.trans $ by simp only [prod.forall, subset_def]

/-- Symmetric entourages form a basis of `π€ Ξ±` -/
lemma uniform_space.has_basis_symmetric :
  (π€ Ξ±).has_basis (Ξ» s : set (Ξ± Γ Ξ±), s β π€ Ξ± β§ symmetric_rel s) id :=
has_basis_self.2 $ Ξ» t t_in, β¨symmetrize_rel t, symmetrize_mem_uniformity t_in,
  symmetric_symmetrize_rel t, symmetrize_rel_subset_self tβ©

/-- Open elements `s : set (Ξ± Γ Ξ±)` of `π€ Ξ±` such that `(x, y) β s β (y, x) β s` form a basis
of `π€ Ξ±`. -/
lemma uniformity_has_basis_open_symmetric :
  has_basis (π€ Ξ±) (Ξ» V : set (Ξ± Γ Ξ±), V β π€ Ξ± β§ is_open V β§ symmetric_rel V) id :=
begin
  simp only [β and_assoc],
  refine uniformity_has_basis_open.restrict (Ξ» s hs, β¨symmetrize_rel s, _β©),
  exact β¨β¨symmetrize_mem_uniformity hs.1, is_open_inter hs.2 (hs.2.preimage continuous_swap)β©,
    symmetric_symmetrize_rel s, symmetrize_rel_subset_self sβ©
end

lemma uniform_space.has_seq_basis (h : is_countably_generated $ π€ Ξ±) :
  β V : β β set (Ξ± Γ Ξ±), has_antimono_basis (π€ Ξ±) (Ξ» _, true) V β§ β n, symmetric_rel (V n) :=
let β¨U, hsym, hbasisβ© := h.exists_antimono_subbasis uniform_space.has_basis_symmetric
in β¨U, hbasis, Ξ» n, (hsym n).2β©

/-! ### Uniform continuity -/

/-- A function `f : Ξ± β Ξ²` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `Ξ±`. -/
def uniform_continuous [uniform_space Ξ²] (f : Ξ± β Ξ²) :=
tendsto (Ξ»x:Ξ±ΓΞ±, (f x.1, f x.2)) (π€ Ξ±) (π€ Ξ²)

/-- A function `f : Ξ± β Ξ²` is *uniformly continuous* on `s : set Ξ±` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s.prod s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`.-/
def uniform_continuous_on [uniform_space Ξ²] (f : Ξ± β Ξ²) (s : set Ξ±) : Prop :=
tendsto (Ξ» x : Ξ± Γ Ξ±, (f x.1, f x.2)) (π€ Ξ± β principal (s.prod s)) (π€ Ξ²)

theorem uniform_continuous_def [uniform_space Ξ²] {f : Ξ± β Ξ²} :
  uniform_continuous f β β r β π€ Ξ², { x : Ξ± Γ Ξ± | (f x.1, f x.2) β r} β π€ Ξ± :=
iff.rfl

theorem uniform_continuous_iff_eventually [uniform_space Ξ²] {f : Ξ± β Ξ²} :
  uniform_continuous f β β r β π€ Ξ², βαΆ  (x : Ξ± Γ Ξ±) in π€ Ξ±, (f x.1, f x.2) β r :=
iff.rfl

lemma uniform_continuous_of_const [uniform_space Ξ²] {c : Ξ± β Ξ²} (h : βa b, c a = c b) :
  uniform_continuous c :=
have (Ξ» (x : Ξ± Γ Ξ±), (c (x.fst), c (x.snd))) β»ΒΉ' id_rel = univ, from
  eq_univ_iff_forall.2 $ assume β¨a, bβ©, h a b,
le_trans (map_le_iff_le_comap.2 $ by simp [comap_principal, this, univ_mem_sets]) refl_le_uniformity

lemma uniform_continuous_id : uniform_continuous (@id Ξ±) :=
by simp [uniform_continuous]; exact tendsto_id

lemma uniform_continuous_const [uniform_space Ξ²] {b : Ξ²} : uniform_continuous (Ξ»a:Ξ±, b) :=
uniform_continuous_of_const $ Ξ» _ _, rfl

lemma uniform_continuous.comp [uniform_space Ξ²] [uniform_space Ξ³] {g : Ξ² β Ξ³} {f : Ξ± β Ξ²}
  (hg : uniform_continuous g) (hf : uniform_continuous f) : uniform_continuous (g β f) :=
hg.comp hf

lemma filter.has_basis.uniform_continuous_iff [uniform_space Ξ²] {p : Ξ³ β Prop} {s : Ξ³ β set (Ξ±ΓΞ±)}
  (ha : (π€ Ξ±).has_basis p s) {q : Ξ΄ β Prop} {t : Ξ΄ β set (Ξ²ΓΞ²)} (hb : (π€ Ξ²).has_basis q t)
  {f : Ξ± β Ξ²} :
  uniform_continuous f β β i (hi : q i), β j (hj : p j), β x y, (x, y) β s j β (f x, f y) β t i :=
(ha.tendsto_iff hb).trans $ by simp only [prod.forall]

lemma filter.has_basis.uniform_continuous_on_iff [uniform_space Ξ²] {p : Ξ³ β Prop}
  {s : Ξ³ β set (Ξ±ΓΞ±)} (ha : (π€ Ξ±).has_basis p s) {q : Ξ΄ β Prop} {t : Ξ΄ β set (Ξ²ΓΞ²)}
  (hb : (π€ Ξ²).has_basis q t) {f : Ξ± β Ξ²} {S : set Ξ±} :
  uniform_continuous_on f S β
    β i (hi : q i), β j (hj : p j), β x y β S, (x, y) β s j β (f x, f y) β t i :=
((ha.inf_principal (S.prod S)).tendsto_iff hb).trans $ by finish [prod.forall]

end uniform_space

open_locale uniformity

section constructions

instance : partial_order (uniform_space Ξ±) :=
{ le          := Ξ»t s, t.uniformity β€ s.uniformity,
  le_antisymm := assume t s hβ hβ, uniform_space_eq $ le_antisymm hβ hβ,
  le_refl     := assume t, le_refl _,
  le_trans    := assume a b c hβ hβ, le_trans hβ hβ }

instance : has_Inf (uniform_space Ξ±) :=
β¨assume s, uniform_space.of_core {
  uniformity := (β¨uβs, @uniformity Ξ± u),
  refl       := le_infi $ assume u, le_infi $ assume hu, u.refl,
  symm       := le_infi $ assume u, le_infi $ assume hu,
    le_trans (map_mono $ infi_le_of_le _ $ infi_le _ hu) u.symm,
  comp       := le_infi $ assume u, le_infi $ assume hu,
    le_trans (lift'_mono (infi_le_of_le _ $ infi_le _ hu) $ le_refl _) u.comp }β©

private lemma Inf_le {tt : set (uniform_space Ξ±)} {t : uniform_space Ξ±} (h : t β tt) :
  Inf tt β€ t :=
show (β¨uβtt, @uniformity Ξ± u) β€ t.uniformity,
  from infi_le_of_le t $ infi_le _ h

private lemma le_Inf {tt : set (uniform_space Ξ±)} {t : uniform_space Ξ±} (h : βt'βtt, t β€ t') :
  t β€ Inf tt :=
show t.uniformity β€ (β¨uβtt, @uniformity Ξ± u),
  from le_infi $ assume t', le_infi $ assume ht', h t' ht'

instance : has_top (uniform_space Ξ±) :=
β¨uniform_space.of_core { uniformity := β€, refl := le_top, symm := le_top, comp := le_top }β©

instance : has_bot (uniform_space Ξ±) :=
β¨{ to_topological_space := β₯,
  uniformity  := π id_rel,
  refl        := le_refl _,
  symm        := by simp [tendsto]; apply subset.refl,
  comp        :=
  begin
    rw [lift'_principal], {simp},
    exact monotone_comp_rel monotone_id monotone_id
  end,
  is_open_uniformity :=
    assume s, by simp [is_open_fold, subset_def, id_rel] {contextual := tt } } β©

instance : complete_lattice (uniform_space Ξ±) :=
{ sup           := Ξ»a b, Inf {x | a β€ x β§ b β€ x},
  le_sup_left   := Ξ» a b, le_Inf (Ξ» _ β¨h, _β©, h),
  le_sup_right  := Ξ» a b, le_Inf (Ξ» _ β¨_, hβ©, h),
  sup_le        := Ξ» a b c hβ hβ, Inf_le β¨hβ, hββ©,
  inf           := Ξ» a b, Inf {a, b},
  le_inf        := Ξ» a b c hβ hβ, le_Inf (Ξ» u h,
                     by { cases h, exact h.symm βΈ hβ, exact (mem_singleton_iff.1 h).symm βΈ hβ }),
  inf_le_left   := Ξ» a b, Inf_le (by simp),
  inf_le_right  := Ξ» a b, Inf_le (by simp),
  top           := β€,
  le_top        := Ξ» a, show a.uniformity β€ β€, from le_top,
  bot           := β₯,
  bot_le        := Ξ» u, u.refl,
  Sup           := Ξ» tt, Inf {t | β t' β tt, t' β€ t},
  le_Sup        := Ξ» s u h, le_Inf (Ξ» u' h', h' u h),
  Sup_le        := Ξ» s u h, Inf_le h,
  Inf           := Inf,
  le_Inf        := Ξ» s a hs, le_Inf hs,
  Inf_le        := Ξ» s a ha, Inf_le ha,
  ..uniform_space.partial_order }

lemma infi_uniformity {ΞΉ : Sort*} {u : ΞΉ β uniform_space Ξ±} :
  (infi u).uniformity = (β¨i, (u i).uniformity) :=
show (β¨a (h : βi:ΞΉ, u i = a), a.uniformity) = _, from
le_antisymm
  (le_infi $ assume i, infi_le_of_le (u i) $ infi_le _ β¨i, rflβ©)
  (le_infi $ assume a, le_infi $ assume β¨i, (ha : u i = a)β©, ha βΈ infi_le _ _)

lemma inf_uniformity {u v : uniform_space Ξ±} :
  (u β v).uniformity = u.uniformity β v.uniformity :=
have (u β v) = (β¨i (h : i = u β¨ i = v), i), by simp [infi_or, infi_inf_eq],
calc (u β v).uniformity = ((β¨i (h : i = u β¨ i = v), i) : uniform_space Ξ±).uniformity : by rw [this]
  ... = _ : by simp [infi_uniformity, infi_or, infi_inf_eq]

instance inhabited_uniform_space : inhabited (uniform_space Ξ±) := β¨β₯β©
instance inhabited_uniform_space_core : inhabited (uniform_space.core Ξ±) :=
β¨@uniform_space.to_core _ (default _)β©

/-- Given `f : Ξ± β Ξ²` and a uniformity `u` on `Ξ²`, the inverse image of `u` under `f`
  is the inverse image in the filter sense of the induced function `Ξ± Γ Ξ± β Ξ² Γ Ξ²`. -/
def uniform_space.comap (f : Ξ± β Ξ²) (u : uniform_space Ξ²) : uniform_space Ξ± :=
{ uniformity := u.uniformity.comap (Ξ»p:Ξ±ΓΞ±, (f p.1, f p.2)),
  to_topological_space := u.to_topological_space.induced f,
  refl := le_trans (by simp; exact assume β¨a, bβ© (h : a = b), h βΈ rfl) (comap_mono u.refl),
  symm := by simp [tendsto_comap_iff, prod.swap, (β)];
            exact tendsto_swap_uniformity.comp tendsto_comap,
  comp := le_trans
    begin
      rw [comap_lift'_eq, comap_lift'_eq2],
      exact (lift'_mono' $ assume s hs β¨aβ, aββ© β¨x, hβ, hββ©, β¨f x, hβ, hββ©),
      repeat { exact monotone_comp_rel monotone_id monotone_id }
    end
    (comap_mono u.comp),
  is_open_uniformity := Ξ» s, begin
    change (@is_open Ξ± (u.to_topological_space.induced f) s β _),
    simp [is_open_iff_nhds, nhds_induced, mem_nhds_uniformity_iff_right, filter.comap, and_comm],
    refine ball_congr (Ξ» x hx, β¨_, _β©),
    { rintro β¨t, hts, htβ©, refine β¨_, ht, _β©,
      rintro β¨xβ, xββ© h rfl, exact hts (h rfl) },
    { rintro β¨t, ht, htsβ©,
      exact β¨{y | (f x, y) β t}, Ξ» y hy, @hts (x, y) hy rfl,
        mem_nhds_uniformity_iff_right.1 $ mem_nhds_left _ htβ© }
  end }

lemma uniformity_comap [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²}
  (h : βΉuniform_space Ξ±βΊ = uniform_space.comap f βΉuniform_space Ξ²βΊ) :
  π€ Ξ± = comap (prod.map f f) (π€ Ξ²) :=
by { rw h, refl }

lemma uniform_space_comap_id {Ξ± : Type*} : uniform_space.comap (id : Ξ± β Ξ±) = id :=
by ext u ; dsimp [uniform_space.comap] ; rw [prod.id_prod, filter.comap_id]

lemma uniform_space.comap_comap {Ξ± Ξ² Ξ³} [uΞ³ : uniform_space Ξ³] {f : Ξ± β Ξ²} {g : Ξ² β Ξ³} :
  uniform_space.comap (g β f) uΞ³ = uniform_space.comap f (uniform_space.comap g uΞ³) :=
by ext ; dsimp [uniform_space.comap] ; rw filter.comap_comap

lemma uniform_continuous_iff {Ξ± Ξ²} [uΞ± : uniform_space Ξ±] [uΞ² : uniform_space Ξ²] {f : Ξ± β Ξ²} :
  uniform_continuous f β uΞ± β€ uΞ².comap f :=
filter.map_le_iff_le_comap

lemma uniform_continuous_comap {f : Ξ± β Ξ²} [u : uniform_space Ξ²] :
  @uniform_continuous Ξ± Ξ² (uniform_space.comap f u) u f :=
tendsto_comap

theorem to_topological_space_comap {f : Ξ± β Ξ²} {u : uniform_space Ξ²} :
  @uniform_space.to_topological_space _ (uniform_space.comap f u) =
  topological_space.induced f (@uniform_space.to_topological_space Ξ² u) := rfl

lemma uniform_continuous_comap' {f : Ξ³ β Ξ²} {g : Ξ± β Ξ³} [v : uniform_space Ξ²] [u : uniform_space Ξ±]
  (h : uniform_continuous (f β g)) : @uniform_continuous Ξ± Ξ³ u (uniform_space.comap f v) g :=
tendsto_comap_iff.2 h

lemma to_nhds_mono {uβ uβ : uniform_space Ξ±} (h : uβ β€ uβ) (a : Ξ±) :
  @nhds _ (@uniform_space.to_topological_space _ uβ) a β€
    @nhds _ (@uniform_space.to_topological_space _ uβ) a :=
by rw [@nhds_eq_uniformity Ξ± uβ a, @nhds_eq_uniformity Ξ± uβ a]; exact (lift'_mono h le_rfl)

lemma to_topological_space_mono {uβ uβ : uniform_space Ξ±} (h : uβ β€ uβ) :
  @uniform_space.to_topological_space _ uβ β€ @uniform_space.to_topological_space _ uβ :=
le_of_nhds_le_nhds $ to_nhds_mono h

lemma uniform_continuous.continuous [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²}
  (hf : uniform_continuous f) : continuous f :=
continuous_iff_le_induced.mpr $ to_topological_space_mono $ uniform_continuous_iff.1 hf

lemma to_topological_space_bot : @uniform_space.to_topological_space Ξ± β₯ = β₯ := rfl

lemma to_topological_space_top : @uniform_space.to_topological_space Ξ± β€ = β€ :=
top_unique $ assume s hs, s.eq_empty_or_nonempty.elim
  (assume : s = β, this.symm βΈ @is_open_empty _ β€)
  (assume  β¨x, hxβ©,
    have s = univ, from top_unique $ assume y hy, hs x hx (x, y) rfl,
    this.symm βΈ @is_open_univ _ β€)

lemma to_topological_space_infi {ΞΉ : Sort*} {u : ΞΉ β uniform_space Ξ±} :
  (infi u).to_topological_space = β¨i, (u i).to_topological_space :=
begin
  by_cases h : nonempty ΞΉ,
  { resetI,
    refine (eq_of_nhds_eq_nhds $ assume a, _),
    rw [nhds_infi, nhds_eq_uniformity],
    change (infi u).uniformity.lift' (preimage $ prod.mk a) = _,
    rw [infi_uniformity, lift'_infi],
    { simp only [nhds_eq_uniformity], refl },
    { exact assume a b, rfl } },
  { rw [infi_of_empty h, infi_of_empty h, to_topological_space_top] }
end

lemma to_topological_space_Inf {s : set (uniform_space Ξ±)} :
  (Inf s).to_topological_space = (β¨iβs, @uniform_space.to_topological_space Ξ± i) :=
begin
  rw [Inf_eq_infi],
  simp only [β to_topological_space_infi],
end

lemma to_topological_space_inf {u v : uniform_space Ξ±} :
  (u β v).to_topological_space = u.to_topological_space β v.to_topological_space :=
by rw [to_topological_space_Inf, infi_pair]

instance : uniform_space empty := β₯
instance : uniform_space unit := β₯
instance : uniform_space bool := β₯
instance : uniform_space β := β₯
instance : uniform_space β€ := β₯

instance {p : Ξ± β Prop} [t : uniform_space Ξ±] : uniform_space (subtype p) :=
uniform_space.comap subtype.val t

lemma uniformity_subtype {p : Ξ± β Prop} [t : uniform_space Ξ±] :
  π€ (subtype p) = comap (Ξ»q:subtype p Γ subtype p, (q.1.1, q.2.1)) (π€ Ξ±) :=
rfl

lemma uniform_continuous_subtype_val {p : Ξ± β Prop} [uniform_space Ξ±] :
  uniform_continuous (subtype.val : {a : Ξ± // p a} β Ξ±) :=
uniform_continuous_comap

lemma uniform_continuous_subtype_mk {p : Ξ± β Prop} [uniform_space Ξ±] [uniform_space Ξ²]
  {f : Ξ² β Ξ±} (hf : uniform_continuous f) (h : βx, p (f x)) :
  uniform_continuous (Ξ»x, β¨f x, h xβ© : Ξ² β subtype p) :=
uniform_continuous_comap' hf

lemma uniform_continuous_on_iff_restrict [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²}
  {s : set Ξ±} :
  uniform_continuous_on f s β uniform_continuous (s.restrict f) :=
begin
  unfold uniform_continuous_on set.restrict uniform_continuous tendsto,
  rw [show (Ξ» x : s Γ s, (f x.1, f x.2)) = prod.map f f β coe, by ext x; cases x; refl,
      uniformity_comap rfl,
      show prod.map subtype.val subtype.val = (coe : s Γ s β Ξ± Γ Ξ±), by ext x; cases x; refl],
  conv in (map _ (comap _ _)) { rw β filter.map_map },
  rw subtype_coe_map_comap_prod, refl,
end

lemma tendsto_of_uniform_continuous_subtype
  [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²} {s : set Ξ±} {a : Ξ±}
  (hf : uniform_continuous (Ξ»x:s, f x.val)) (ha : s β π a) :
  tendsto f (π a) (π (f a)) :=
by rw [(@map_nhds_subtype_coe_eq Ξ± _ s a (mem_of_nhds ha) ha).symm]; exact
tendsto_map' (continuous_iff_continuous_at.mp hf.continuous _)

lemma uniform_continuous_on.continuous_on [uniform_space Ξ±] [uniform_space Ξ²] {f : Ξ± β Ξ²}
  {s : set Ξ±} (h : uniform_continuous_on f s) : continuous_on f s :=
begin
  rw uniform_continuous_on_iff_restrict at h,
  rw continuous_on_iff_continuous_restrict,
  exact h.continuous
end

section prod

/- a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/
instance [uβ : uniform_space Ξ±] [uβ : uniform_space Ξ²] : uniform_space (Ξ± Γ Ξ²) :=
uniform_space.of_core_eq
  (uβ.comap prod.fst β uβ.comap prod.snd).to_core
  prod.topological_space
  (calc prod.topological_space = (uβ.comap prod.fst β uβ.comap prod.snd).to_topological_space :
      by rw [to_topological_space_inf, to_topological_space_comap, to_topological_space_comap]; refl
    ... = _ : by rw [uniform_space.to_core_to_topological_space])

theorem uniformity_prod [uniform_space Ξ±] [uniform_space Ξ²] : π€ (Ξ± Γ Ξ²) =
  (π€ Ξ±).comap (Ξ»p:(Ξ± Γ Ξ²) Γ Ξ± Γ Ξ², (p.1.1, p.2.1)) β
  (π€ Ξ²).comap (Ξ»p:(Ξ± Γ Ξ²) Γ Ξ± Γ Ξ², (p.1.2, p.2.2)) :=
inf_uniformity

lemma uniformity_prod_eq_prod [uniform_space Ξ±] [uniform_space Ξ²] :
  π€ (Ξ±ΓΞ²) =
    map (Ξ»p:(Ξ±ΓΞ±)Γ(Ξ²ΓΞ²), ((p.1.1, p.2.1), (p.1.2, p.2.2))) (π€ Ξ± ΓαΆ  π€ Ξ²) :=
have map (Ξ»p:(Ξ±ΓΞ±)Γ(Ξ²ΓΞ²), ((p.1.1, p.2.1), (p.1.2, p.2.2))) =
  comap (Ξ»p:(Ξ±ΓΞ²)Γ(Ξ±ΓΞ²), ((p.1.1, p.2.1), (p.1.2, p.2.2))),
  from funext $ assume f, map_eq_comap_of_inverse
    (funext $ assume β¨β¨_, _β©, β¨_, _β©β©, rfl) (funext $ assume β¨β¨_, _β©, β¨_, _β©β©, rfl),
by rw [this, uniformity_prod, filter.prod, comap_inf, comap_comap, comap_comap]

lemma mem_map_sets_iff' {Ξ± : Type*} {Ξ² : Type*} {f : filter Ξ±} {m : Ξ± β Ξ²} {t : set Ξ²} :
  t β (map m f).sets β (βsβf, m '' s β t) :=
mem_map_sets_iff

lemma mem_uniformity_of_uniform_continuous_invariant [uniform_space Ξ±] {s:set (Ξ±ΓΞ±)} {f : Ξ± β Ξ± β Ξ±}
  (hf : uniform_continuous (Ξ»p:Ξ±ΓΞ±, f p.1 p.2)) (hs : s β π€ Ξ±) :
  βuβπ€ Ξ±, βa b c, (a, b) β u β (f a c, f b c) β s :=
begin
  rw [uniform_continuous, uniformity_prod_eq_prod, tendsto_map'_iff, (β)] at hf,
  rcases mem_map_sets_iff'.1 (hf hs) with β¨t, ht, htsβ©, clear hf,
  rcases mem_prod_iff.1 ht with β¨u, hu, v, hv, huvtβ©, clear ht,
  refine β¨u, hu, assume a b c hab, hts $ (mem_image _ _ _).2 β¨β¨β¨a, bβ©, β¨c, cβ©β©, huvt β¨_, _β©, _β©β©,
  exact hab,
  exact refl_mem_uniformity hv,
  refl
end

lemma mem_uniform_prod [tβ : uniform_space Ξ±] [tβ : uniform_space Ξ²] {a : set (Ξ± Γ Ξ±)}
  {b : set (Ξ² Γ Ξ²)} (ha : a β π€ Ξ±) (hb : b β π€ Ξ²) :
  {p:(Ξ±ΓΞ²)Γ(Ξ±ΓΞ²) | (p.1.1, p.2.1) β a β§ (p.1.2, p.2.2) β b } β (@uniformity (Ξ± Γ Ξ²) _) :=
by rw [uniformity_prod]; exact inter_mem_inf_sets (preimage_mem_comap ha) (preimage_mem_comap hb)

lemma tendsto_prod_uniformity_fst [uniform_space Ξ±] [uniform_space Ξ²] :
  tendsto (Ξ»p:(Ξ±ΓΞ²)Γ(Ξ±ΓΞ²), (p.1.1, p.2.1)) (π€ (Ξ± Γ Ξ²)) (π€ Ξ±) :=
le_trans (map_mono (@inf_le_left (uniform_space (Ξ±ΓΞ²)) _ _ _)) map_comap_le

lemma tendsto_prod_uniformity_snd [uniform_space Ξ±] [uniform_space Ξ²] :
  tendsto (Ξ»p:(Ξ±ΓΞ²)Γ(Ξ±ΓΞ²), (p.1.2, p.2.2)) (π€ (Ξ± Γ Ξ²)) (π€ Ξ²) :=
le_trans (map_mono (@inf_le_right (uniform_space (Ξ±ΓΞ²)) _ _ _)) map_comap_le

lemma uniform_continuous_fst [uniform_space Ξ±] [uniform_space Ξ²] :
  uniform_continuous (Ξ»p:Ξ±ΓΞ², p.1) :=
tendsto_prod_uniformity_fst

lemma uniform_continuous_snd [uniform_space Ξ±] [uniform_space Ξ²] :
  uniform_continuous (Ξ»p:Ξ±ΓΞ², p.2) :=
tendsto_prod_uniformity_snd

variables [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³]
lemma uniform_continuous.prod_mk
  {fβ : Ξ± β Ξ²} {fβ : Ξ± β Ξ³} (hβ : uniform_continuous fβ) (hβ : uniform_continuous fβ) :
  uniform_continuous (Ξ»a, (fβ a, fβ a)) :=
by rw [uniform_continuous, uniformity_prod]; exact
tendsto_inf.2 β¨tendsto_comap_iff.2 hβ, tendsto_comap_iff.2 hββ©

lemma uniform_continuous.prod_mk_left {f : Ξ± Γ Ξ² β Ξ³} (h : uniform_continuous f) (b) :
  uniform_continuous (Ξ» a, f (a,b)) :=
h.comp (uniform_continuous_id.prod_mk uniform_continuous_const)

lemma uniform_continuous.prod_mk_right {f : Ξ± Γ Ξ² β Ξ³} (h : uniform_continuous f) (a) :
  uniform_continuous (Ξ» b, f (a,b)) :=
h.comp (uniform_continuous_const.prod_mk  uniform_continuous_id)

lemma uniform_continuous.prod_map [uniform_space Ξ΄] {f : Ξ± β Ξ³} {g : Ξ² β Ξ΄}
  (hf : uniform_continuous f) (hg : uniform_continuous g) :
  uniform_continuous (prod.map f g) :=
(hf.comp uniform_continuous_fst).prod_mk (hg.comp uniform_continuous_snd)

lemma to_topological_space_prod {Ξ±} {Ξ²} [u : uniform_space Ξ±] [v : uniform_space Ξ²] :
  @uniform_space.to_topological_space (Ξ± Γ Ξ²) prod.uniform_space =
    @prod.topological_space Ξ± Ξ² u.to_topological_space v.to_topological_space := rfl

end prod

section
open uniform_space function
variables {Ξ΄' : Type*} [uniform_space Ξ±] [uniform_space Ξ²] [uniform_space Ξ³] [uniform_space Ξ΄]
  [uniform_space Ξ΄']

local notation f `ββ` g := function.bicompr f g

/-- Uniform continuity for functions of two variables. -/
def uniform_continuousβ (f : Ξ± β Ξ² β Ξ³) := uniform_continuous (uncurry f)

lemma uniform_continuousβ_def (f : Ξ± β Ξ² β Ξ³) :
  uniform_continuousβ f β uniform_continuous (uncurry f) := iff.rfl

lemma uniform_continuousβ.uniform_continuous {f : Ξ± β Ξ² β Ξ³} (h : uniform_continuousβ f) :
  uniform_continuous (uncurry f) := h

lemma uniform_continuousβ_curry (f : Ξ± Γ Ξ² β Ξ³) :
  uniform_continuousβ (function.curry f) β uniform_continuous f :=
by rw [uniform_continuousβ, uncurry_curry]

lemma uniform_continuousβ.comp {f : Ξ± β Ξ² β Ξ³} {g : Ξ³ β Ξ΄}
  (hg : uniform_continuous g) (hf : uniform_continuousβ f) :
  uniform_continuousβ (g ββ f) :=
hg.comp hf

lemma uniform_continuousβ.bicompl {f : Ξ± β Ξ² β Ξ³} {ga : Ξ΄ β Ξ±} {gb : Ξ΄' β Ξ²}
  (hf : uniform_continuousβ f) (hga : uniform_continuous ga) (hgb : uniform_continuous gb) :
  uniform_continuousβ (bicompl f ga gb) :=
hf.uniform_continuous.comp (hga.prod_map hgb)

end

lemma to_topological_space_subtype [u : uniform_space Ξ±] {p : Ξ± β Prop} :
  @uniform_space.to_topological_space (subtype p) subtype.uniform_space =
    @subtype.topological_space Ξ± p u.to_topological_space := rfl

section sum
variables [uniform_space Ξ±] [uniform_space Ξ²]
open sum

/-- Uniformity on a disjoint union. Entourages of the diagonal in the union are obtained
by taking independently an entourage of the diagonal in the first part, and an entourage of
the diagonal in the second part. -/
def uniform_space.core.sum : uniform_space.core (Ξ± β Ξ²) :=
uniform_space.core.mk'
  (map (Ξ» p : Ξ± Γ Ξ±, (inl p.1, inl p.2)) (π€ Ξ±) β map (Ξ» p : Ξ² Γ Ξ², (inr p.1, inr p.2)) (π€ Ξ²))
  (Ξ» r β¨Hβ, Hββ© x, by cases x; [apply refl_mem_uniformity Hβ, apply refl_mem_uniformity Hβ])
  (Ξ» r β¨Hβ, Hββ©, β¨symm_le_uniformity Hβ, symm_le_uniformity Hββ©)
  (Ξ» r β¨HrΞ±, HrΞ²β©, begin
    rcases comp_mem_uniformity_sets HrΞ± with β¨tΞ±, htΞ±, HtΞ±β©,
    rcases comp_mem_uniformity_sets HrΞ² with β¨tΞ², htΞ², HtΞ²β©,
    refine β¨_,
      β¨mem_map_sets_iff.2 β¨tΞ±, htΞ±, subset_union_left _ _β©,
       mem_map_sets_iff.2 β¨tΞ², htΞ², subset_union_right _ _β©β©, _β©,
    rintros β¨_, _β© β¨z, β¨β¨a, bβ©, hab, β¨β©β© | β¨β¨a, bβ©, hab, β¨β©β©,
                       β¨β¨_, cβ©, hbc, β¨β©β© | β¨β¨_, cβ©, hbc, β¨β©β©β©,
    { have A : (a, c) β tΞ± β tΞ± := β¨b, hab, hbcβ©,
      exact HtΞ± A },
    { have A : (a, c) β tΞ² β tΞ² := β¨b, hab, hbcβ©,
      exact HtΞ² A }
  end)

/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage
of the diagonal. -/
lemma union_mem_uniformity_sum
  {a : set (Ξ± Γ Ξ±)} (ha : a β π€ Ξ±) {b : set (Ξ² Γ Ξ²)} (hb : b β π€ Ξ²) :
  ((Ξ» p : (Ξ± Γ Ξ±), (inl p.1, inl p.2)) '' a βͺ (Ξ» p : (Ξ² Γ Ξ²), (inr p.1, inr p.2)) '' b) β
    (@uniform_space.core.sum Ξ± Ξ² _ _).uniformity :=
β¨mem_map_sets_iff.2 β¨_, ha, subset_union_left _ _β©,
  mem_map_sets_iff.2 β¨_, hb, subset_union_right _ _β©β©

/- To prove that the topology defined by the uniform structure on the disjoint union coincides with
the disjoint union topology, we need two lemmas saying that open sets can be characterized by
the uniform structure -/
lemma uniformity_sum_of_open_aux {s : set (Ξ± β Ξ²)} (hs : is_open s) {x : Ξ± β Ξ²} (xs : x β s) :
  { p : ((Ξ± β Ξ²) Γ (Ξ± β Ξ²)) | p.1 = x β p.2 β s } β (@uniform_space.core.sum Ξ± Ξ² _ _).uniformity :=
begin
  cases x,
  { refine mem_sets_of_superset
      (union_mem_uniformity_sum (mem_nhds_uniformity_iff_right.1 (mem_nhds_sets hs.1 xs))
        univ_mem_sets)
      (union_subset _ _);
    rintro _ β¨β¨_, bβ©, h, β¨β©β© β¨β©,
    exact h rfl },
  { refine mem_sets_of_superset
      (union_mem_uniformity_sum univ_mem_sets (mem_nhds_uniformity_iff_right.1
        (mem_nhds_sets hs.2 xs)))
      (union_subset _ _);
    rintro _ β¨β¨a, _β©, h, β¨β©β© β¨β©,
    exact h rfl },
end

lemma open_of_uniformity_sum_aux {s : set (Ξ± β Ξ²)}
  (hs : βx β s, { p : ((Ξ± β Ξ²) Γ (Ξ± β Ξ²)) | p.1 = x β p.2 β s } β
    (@uniform_space.core.sum Ξ± Ξ² _ _).uniformity) :
  is_open s :=
begin
  split,
  { refine (@is_open_iff_mem_nhds Ξ± _ _).2 (Ξ» a ha, mem_nhds_uniformity_iff_right.2 _),
    rcases mem_map_sets_iff.1 (hs _ ha).1 with β¨t, ht, stβ©,
    refine mem_sets_of_superset ht _,
    rintro p pt rfl, exact st β¨_, pt, rflβ© rfl },
  { refine (@is_open_iff_mem_nhds Ξ² _ _).2 (Ξ» b hb, mem_nhds_uniformity_iff_right.2 _),
    rcases mem_map_sets_iff.1 (hs _ hb).2 with β¨t, ht, stβ©,
    refine mem_sets_of_superset ht _,
    rintro p pt rfl, exact st β¨_, pt, rflβ© rfl }
end

/- We can now define the uniform structure on the disjoint union -/
instance sum.uniform_space : uniform_space (Ξ± β Ξ²) :=
{ to_core := uniform_space.core.sum,
  is_open_uniformity := Ξ» s, β¨uniformity_sum_of_open_aux, open_of_uniformity_sum_auxβ© }

lemma sum.uniformity : π€ (Ξ± β Ξ²) =
    map (Ξ» p : Ξ± Γ Ξ±, (inl p.1, inl p.2)) (π€ Ξ±) β
    map (Ξ» p : Ξ² Γ Ξ², (inr p.1, inr p.2)) (π€ Ξ²) := rfl

end sum

end constructions

-- For a version of the Lebesgue number lemma assuming only a sequentially compact space,
-- see topology/sequences.lean

/-- Let `c : ΞΉ β set Ξ±` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x β s` its `n`-neighborhood is contained in some `c i`. -/
lemma lebesgue_number_lemma {Ξ± : Type u} [uniform_space Ξ±] {s : set Ξ±} {ΞΉ} {c : ΞΉ β set Ξ±}
  (hs : is_compact s) (hcβ : β i, is_open (c i)) (hcβ : s β β i, c i) :
  β n β π€ Ξ±, β x β s, β i, {y | (x, y) β n} β c i :=
begin
  let u := Ξ» n, {x | β i (m β π€ Ξ±), {y | (x, y) β m β n} β c i},
  have huβ : β n β π€ Ξ±, is_open (u n),
  { refine Ξ» n hn, is_open_uniformity.2 _,
    rintro x β¨i, m, hm, hβ©,
    rcases comp_mem_uniformity_sets hm with β¨m', hm', mm'β©,
    apply (π€ Ξ±).sets_of_superset hm',
    rintros β¨x, yβ© hp rfl,
    refine β¨i, m', hm', Ξ» z hz, h (monotone_comp_rel monotone_id monotone_const mm' _)β©,
    dsimp at hz β’, rw comp_rel_assoc,
    exact β¨y, hp, hzβ© },
  have huβ : s β β n β π€ Ξ±, u n,
  { intros x hx,
    rcases mem_Union.1 (hcβ hx) with β¨i, hβ©,
    rcases comp_mem_uniformity_sets (is_open_uniformity.1 (hcβ i) x h) with β¨m', hm', mm'β©,
    exact mem_bUnion hm' β¨i, _, hm', Ξ» y hy, mm' hy rflβ© },
  rcases hs.elim_finite_subcover_image huβ huβ with β¨b, bu, b_fin, b_coverβ©,
  refine β¨_, (bInter_mem_sets b_fin).2 bu, Ξ» x hx, _β©,
  rcases mem_bUnion_iff.1 (b_cover hx) with β¨n, bn, i, m, hm, hβ©,
  refine β¨i, Ξ» y hy, h _β©,
  exact prod_mk_mem_comp_rel (refl_mem_uniformity hm) (bInter_subset_of_mem bn hy)
end

/-- Let `c : set (set Ξ±)` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x β s` its `n`-neighborhood is contained in some `t β c`. -/
lemma lebesgue_number_lemma_sUnion {Ξ± : Type u} [uniform_space Ξ±] {s : set Ξ±} {c : set (set Ξ±)}
  (hs : is_compact s) (hcβ : β t β c, is_open t) (hcβ : s β ββ c) :
  β n β π€ Ξ±, β x β s, β t β c, β y, (x, y) β n β y β t :=
by rw sUnion_eq_Union at hcβ;
   simpa using lebesgue_number_lemma hs (by simpa) hcβ

/-!
### Expressing continuity properties in uniform spaces

We reformulate the various continuity properties of functions taking values in a uniform space
in terms of the uniformity in the target. Since the same lemmas (essentially with the same names)
also exist for metric spaces and emetric spaces (reformulating things in terms of the distance or
the edistance in the target), we put them in a namespace `uniform` here.

In the metric and emetric space setting, there are also similar lemmas where one assumes that
both the source and the target are metric spaces, reformulating things in terms of the distance
on both sides. These lemmas are generally written without primes, and the versions where only
the target is a metric space is primed. We follow the same convention here, thus giving lemmas
with primes.
-/

namespace uniform

variables [uniform_space Ξ±]

theorem tendsto_nhds_right {f : filter Ξ²} {u : Ξ² β Ξ±} {a : Ξ±} :
  tendsto u f (π a) β tendsto (Ξ» x, (a, u x)) f (π€ Ξ±)  :=
β¨Ξ» H, tendsto_left_nhds_uniformity.comp H,
Ξ» H s hs, by simpa [mem_of_nhds hs] using H (mem_nhds_uniformity_iff_right.1 hs)β©

theorem tendsto_nhds_left {f : filter Ξ²} {u : Ξ² β Ξ±} {a : Ξ±} :
  tendsto u f (π a) β tendsto (Ξ» x, (u x, a)) f (π€ Ξ±)  :=
β¨Ξ» H, tendsto_right_nhds_uniformity.comp H,
Ξ» H s hs, by simpa [mem_of_nhds hs] using H (mem_nhds_uniformity_iff_left.1 hs)β©

theorem continuous_at_iff'_right [topological_space Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} :
  continuous_at f b β tendsto (Ξ» x, (f b, f x)) (π b) (π€ Ξ±) :=
by rw [continuous_at, tendsto_nhds_right]

theorem continuous_at_iff'_left [topological_space Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} :
  continuous_at f b β tendsto (Ξ» x, (f x, f b)) (π b) (π€ Ξ±) :=
by rw [continuous_at, tendsto_nhds_left]

theorem continuous_at_iff_prod [topological_space Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} :
  continuous_at f b β tendsto (Ξ» x : Ξ² Γ Ξ², (f x.1, f x.2)) (π (b, b)) (π€ Ξ±) :=
β¨Ξ» H, le_trans (H.prod_map' H) (nhds_le_uniformity _),
  Ξ» H, continuous_at_iff'_left.2 $ H.comp $ tendsto_id.prod_mk_nhds tendsto_const_nhdsβ©

theorem continuous_within_at_iff'_right [topological_space Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} {s : set Ξ²} :
  continuous_within_at f s b β tendsto (Ξ» x, (f b, f x)) (π[s] b) (π€ Ξ±) :=
by rw [continuous_within_at, tendsto_nhds_right]

theorem continuous_within_at_iff'_left [topological_space Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} {s : set Ξ²} :
  continuous_within_at f s b β tendsto (Ξ» x, (f x, f b)) (π[s] b) (π€ Ξ±) :=
by rw [continuous_within_at, tendsto_nhds_left]

theorem continuous_on_iff'_right [topological_space Ξ²] {f : Ξ² β Ξ±} {s : set Ξ²} :
  continuous_on f s β β b β s, tendsto (Ξ» x, (f b, f x)) (π[s] b) (π€ Ξ±) :=
by simp [continuous_on, continuous_within_at_iff'_right]

theorem continuous_on_iff'_left [topological_space Ξ²] {f : Ξ² β Ξ±} {s : set Ξ²} :
  continuous_on f s β β b β s, tendsto (Ξ» x, (f x, f b)) (π[s] b) (π€ Ξ±) :=
by simp [continuous_on, continuous_within_at_iff'_left]

theorem continuous_iff'_right [topological_space Ξ²] {f : Ξ² β Ξ±} :
  continuous f β β b, tendsto (Ξ» x, (f b, f x)) (π b) (π€ Ξ±) :=
continuous_iff_continuous_at.trans $ forall_congr $ Ξ» b, tendsto_nhds_right

theorem continuous_iff'_left [topological_space Ξ²] {f : Ξ² β Ξ±} :
  continuous f β β b, tendsto (Ξ» x, (f x, f b)) (π b) (π€ Ξ±) :=
continuous_iff_continuous_at.trans $ forall_congr $ Ξ» b, tendsto_nhds_left

end uniform

lemma filter.tendsto.congr_uniformity {Ξ± Ξ²} [uniform_space Ξ²] {f g : Ξ± β Ξ²} {l : filter Ξ±} {b : Ξ²}
  (hf : tendsto f l (π b)) (hg : tendsto (Ξ» x, (f x, g x)) l (π€ Ξ²)) :
  tendsto g l (π b) :=
uniform.tendsto_nhds_right.2 $ (uniform.tendsto_nhds_right.1 hf).uniformity_trans hg

lemma uniform.tendsto_congr {Ξ± Ξ²} [uniform_space Ξ²] {f g : Ξ± β Ξ²} {l : filter Ξ±} {b : Ξ²}
  (hfg : tendsto (Ξ» x, (f x, g x)) l (π€ Ξ²)) :
  tendsto f l (π b) β tendsto g l (π b) :=
β¨Ξ» h, h.congr_uniformity hfg, Ξ» h, h.congr_uniformity hfg.uniformity_symmβ©
