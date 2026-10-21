/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.RepresentationTheory.Basic
public import Physlib.Meta.TODO.Basic
/-!
# Local gauge data

The jets of gauge transformations at a point, as the data a local Lagrangian sees.

## i. Overview

The full gauge group of a theory is some class of functions from spacetime to a global gauge
group `G₀` with Lie algebra `𝔤`; for the Standard Model `G₀ = SU(3) × SU(2) × U(1)`, ignoring
discrete quotients. Physicists are usually agnostic about which class, because a local
Lagrangian only sees how a gauge transformation acts on the fields and finitely many of their
derivatives at a point `x`, and that depends only on the Taylor series of the gauge transformation
at `x`. If every smooth function is an allowed gauge transformation — the one assumption made
about the class — then by Borel's theorem every Taylor series compatible with the group
arises, convergent or not. These Taylor series, the *jets* at `x`, form the group `GJ`, and
their infinitesimal counterparts the Lie algebra `𝔤J` over `ℝ`.

How best to present `GJ` depends on `G₀`, so it is taken as input rather than constructed.
For a matrix group such as `SU(2)`, the jet of a gauge transformation is a matrix with entries
in `SpaceTimeAlgebra`, the formal Taylor series at `x`. The Taylor series of a product is the
product of the Taylor series, so the group law is still matrix multiplication, and `GJ` is cut
out by the same equations `U† U = 1` and `det U = 1` read over `SpaceTimeAlgebra`; likewise
`𝔤J` is the traceless self-adjoint matrices over `SpaceTimeAlgebra` with the usual bracket
` ⁅A, B⁆ = i(AB − BA)`.


## ii. Key results

- `LocalGaugeData` : the structure.
- `LocalGaugeData.adjoint_bracket` : the adjoint action of `G₀` on `𝔤` is by Lie algebra
  automorphisms, from the jet-level law applied to constants.
- `LocalGaugeData.iteratedDeriv` : the iterated derivative `∂_s` on `𝔤J` along a multiset
  of directions, with `iteratedDeriv_cons`, `iteratedDeriv_add` and the iterated Leibniz
  rule `iteratedDeriv_bracket`.
- `LocalGaugeData.evalLie_iteratedDeriv_mulCoord` : the coordinate multiplication identity
- `LocalGaugeData.Hom` : a morphism of local gauge data, with `Hom.id` and `Hom.comp`.

## iii. Table of contents

- A. The structure
- B. Simple derived properties
- C. The iterated derivative on the jet Lie algebra
  - C.1. Commutativity of derivatives
  - C.2. Definition of the iterated derivative
  - C.3. Properties of the iterated derivative
- D. Morphisms
  - D.1. The adjoint action
  - D.2. Relation to iterated derivatives
  - D.3. Identity morphisms
  - D.4. Composition of morphisms

## iv. References

-/

@[expose] public section

/-!

## A. The structure

We package this local information of a gauge group into the structure `LocalGaugeData G₀ 𝔤 GJ 𝔤J`.
Alongside the four carriers, it records the operations that the transformation laws of gauge fields
and matter fields are built from, and the coordinates that place a jet around the base point.
It consists of:

* the inclusion of constants and evaluation at the base point, on the group and on the
  Lie algebra;
* the formal spacetime derivatives `deriv μ` on `𝔤J`, commuting, satisfying the Leibniz
  rule for the bracket, and killing constants;
* multiplication by the coordinates `mulCoord μ`, vanishing at the base point and central for
  the bracket, with `∂_μ (x_ν a) = x_ν ∂_μ a + δ_{μν} a`;
* the adjoint action of `GJ` on `𝔤J`, by Lie algebra automorphisms, evaluating at the base
  point to the adjoint action of `G₀` on `𝔤`;
* the Maurer–Cartan form `maurerCartan U μ = i (∂_μ U) U⁻¹`, with its cocycle law, its
  flatness equation `maurerCartan_structure` and the Leibniz rule `deriv_adjointJ` for the
  adjoint action.

-/

/-- Local gauge data. A gauge group `G₀` with Lie algebra `𝔤`, its group of jets `GJ` with
  Lie algebra of jets `𝔤J`, evaluation at the base point, formal derivatives, the adjoint
  action and the Maurer–Cartan form, subject to the identities used by the transformation
  laws of gauge and matter fields. -/
structure LocalGaugeData (G₀ : Type) [Group G₀] (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (GJ : Type) [Group GJ] (𝔤J : Type) [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J] where
  /-- Evaluation of a gauge jet at the base point. -/
  eval : GJ →* G₀
  /-- A constant gauge transformation as a jet. -/
  ofConstant : G₀ →* GJ
  eval_ofConstant : ∀ g, eval (ofConstant g) = g
  /-- Evaluation of a Lie algebra jet at the base point. -/
  evalLie : 𝔤J →ₗ⁅ℝ⁆ 𝔤
  /-- A constant Lie algebra element as a jet. -/
  ofConstantLie : 𝔤 →ₗ⁅ℝ⁆ 𝔤J
  evalLie_ofConstantLie : ∀ a, evalLie (ofConstantLie a) = a
  /-- The formal derivative in the direction `μ`. -/
  deriv : (Fin 1 ⊕ Fin 3) → 𝔤J →ₗ[ℝ] 𝔤J
  deriv_comm : ∀ (μ ν : Fin 1 ⊕ Fin 3) (a : 𝔤J), deriv μ (deriv ν a) = deriv ν (deriv μ a)
  deriv_bracket : ∀ (μ : Fin 1 ⊕ Fin 3) (x y : 𝔤J),
    deriv μ ⁅x, y⁆ = ⁅deriv μ x, y⁆ + ⁅x, deriv μ y⁆
  deriv_ofConstantLie : ∀ (μ : Fin 1 ⊕ Fin 3) (a : 𝔤), deriv μ (ofConstantLie a) = 0
  /-- Multiplication of a jet by the spacetime coordinate `x_μ`. -/
  mulCoord : (Fin 1 ⊕ Fin 3) → 𝔤J →ₗ[ℝ] 𝔤J
  /-- The Leibniz rule for a coordinate: `∂_μ (x_ν a) = x_ν ∂_μ a + δ_{μν} a`. -/
  deriv_mulCoord : ∀ (μ ν : Fin 1 ⊕ Fin 3) (a : 𝔤J),
    deriv μ (mulCoord ν a) = mulCoord ν (deriv μ a) + if μ = ν then a else 0
  /-- A multiple of a coordinate vanishes at the base point. -/
  evalLie_mulCoord : ∀ (μ : Fin 1 ⊕ Fin 3) (a : 𝔤J), evalLie (mulCoord μ a) = 0
  /-- Multiplication by a coordinate commutes with the bracket. -/
  mulCoord_bracket : ∀ (μ : Fin 1 ⊕ Fin 3) (a b : 𝔤J), ⁅mulCoord μ a, b⁆ = mulCoord μ ⁅a, b⁆
  /-- The adjoint action of the jet group on the jet Lie algebra. -/
  adjointJ : Representation ℝ GJ 𝔤J
  adjointJ_bracket : ∀ (U : GJ) (x y : 𝔤J), adjointJ U ⁅x, y⁆ = ⁅adjointJ U x, adjointJ U y⁆
  /-- The adjoint representation of the value group on its Lie algebra. -/
  adjoint : Representation ℝ G₀ 𝔤
  /-- At the base point the adjoint action of a jet is the adjoint action of its value. -/
  evalLie_adjointJ : ∀ (U : GJ) (x : 𝔤J), evalLie (adjointJ U x) = adjoint (eval U) (evalLie x)
  /-- The Maurer–Cartan form `i (∂_μ U) U⁻¹` of a gauge jet. -/
  maurerCartan : GJ → (Fin 1 ⊕ Fin 3) → 𝔤J
  /-- A constant gauge transformation has vanishing Maurer–Cartan form: it has no
    spacetime dependence to differentiate. -/
  maurerCartan_ofConstant : ∀ (g : G₀) (μ : Fin 1 ⊕ Fin 3), maurerCartan (ofConstant g) μ = 0
  /-- The Maurer–Cartan form is a cocycle for the adjoint action. -/
  maurerCartan_cocycle : ∀ (U V : GJ) (μ : Fin 1 ⊕ Fin 3),
    maurerCartan (U * V) μ = maurerCartan U μ + adjointJ U (maurerCartan V μ)
  /-- The Maurer–Cartan form is flat. -/
  maurerCartan_structure : ∀ (U : GJ) (μ ν : Fin 1 ⊕ Fin 3),
    deriv μ (maurerCartan U ν) - deriv ν (maurerCartan U μ)
      + ⁅maurerCartan U μ, maurerCartan U ν⁆ = 0
  /-- The Leibniz rule for the adjoint action. -/
  deriv_adjointJ : ∀ (U : GJ) (μ : Fin 1 ⊕ Fin 3) (x : 𝔤J),
    deriv μ (adjointJ U x) = adjointJ U (deriv μ x) - ⁅maurerCartan U μ, adjointJ U x⁆

namespace LocalGaugeData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J)

TODO "Add a constructor for LocalGaugeData from a Lie group and its Lie algebra"

TODO "For U(1) and SU(n), prove that taking Taylor series gives a group isomorphism between
  smooth local gauge transformations modulo agreement of all derivatives at the base point
  and the corresponding formal gauge-jet group."

/-!

## B. Simple derived properties

-/

/-- Every global gauge transformation is the value of a jet, namely its constant jet. -/
lemma eval_surjective : Function.Surjective jets.eval :=
  Function.LeftInverse.surjective jets.eval_ofConstant

lemma ofConstant_injective : Function.Injective jets.ofConstant :=
  Function.LeftInverse.injective jets.eval_ofConstant

lemma evalLie_surjective : Function.Surjective jets.evalLie :=
  Function.LeftInverse.surjective jets.evalLie_ofConstantLie

lemma ofConstantLie_injective : Function.Injective jets.ofConstantLie :=
  Function.LeftInverse.injective jets.evalLie_ofConstantLie

lemma adjoint_bracket (g : G₀) (a b : 𝔤) :
    jets.adjoint g ⁅a, b⁆ = ⁅jets.adjoint g a, jets.adjoint g b⁆ := by
  have h := jets.evalLie_adjointJ (jets.ofConstant g)
  rw [jets.eval_ofConstant] at h
  rw [← jets.evalLie_ofConstantLie ⁅a, b⁆, ← h, LieHom.map_lie jets.ofConstantLie,
    jets.adjointJ_bracket, LieHom.map_lie, h, h, jets.evalLie_ofConstantLie,
    jets.evalLie_ofConstantLie]

lemma deriv_adjointJ_ofConstant (g : G₀) (μ : Fin 1 ⊕ Fin 3) (x : 𝔤J) :
    jets.deriv μ (jets.adjointJ (jets.ofConstant g) x) =
      jets.adjointJ (jets.ofConstant g) (jets.deriv μ x) := by
  rw [jets.deriv_adjointJ, jets.maurerCartan_ofConstant, zero_lie, sub_zero]

/-!

## C. The iterated derivative on the jet Lie algebra

-/

/-!

### C.1. Commutativity of derivatives

-/

/-- Post-composition with `deriv` is right-commutative. -/
instance instRightCommutativeCompDeriv : RightCommutative
    (fun (D : 𝔤J →ₗ[ℝ] 𝔤J) (μ : Fin 1 ⊕ Fin 3) => D.comp (jets.deriv μ)) where
  right_comm D μ ν := by
    refine LinearMap.ext fun a => ?_
    exact congrArg D (jets.deriv_comm μ ν a)

/-!

### C.2. Definition of the iterated derivative

-/

/-- The iterated formal derivative on the jet Lie algebra. -/
noncomputable def iteratedDeriv (μs : Multiset (Fin 1 ⊕ Fin 3)) : 𝔤J →ₗ[ℝ] 𝔤J :=
  μs.foldl (fun D μ => D.comp (jets.deriv μ)) LinearMap.id

/-!

### C.3. Properties of the iterated derivative

-/

@[simp]
lemma iteratedDeriv_zero : jets.iteratedDeriv (0 : Multiset (Fin 1 ⊕ Fin 3)) = LinearMap.id := by
  simp [iteratedDeriv]

lemma iteratedDeriv_cons (μ : Fin 1 ⊕ Fin 3) (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    jets.iteratedDeriv (μ ::ₘ μs) = (jets.deriv μ).comp (jets.iteratedDeriv μs) := by
  have h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (D : 𝔤J →ₗ[ℝ] 𝔤J),
      s.foldl (fun D μ => D.comp (jets.deriv μ)) D = D.comp (jets.iteratedDeriv s) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro D; simp [iteratedDeriv]
    | cons κ t ih =>
        intro D
        rw [iteratedDeriv, Multiset.foldl_cons, Multiset.foldl_cons, ih, ih]
        simp [LinearMap.comp_assoc]
  rw [iteratedDeriv, Multiset.foldl_cons, h]
  simp

/-- The iterated derivative is additive in the multiset. -/
lemma iteratedDeriv_add (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    jets.iteratedDeriv (s + t) = (jets.iteratedDeriv s).comp (jets.iteratedDeriv t) := by
  induction s using Multiset.induction_on with
  | empty => simp [iteratedDeriv_zero]
  | cons μ s ih =>
      rw [Multiset.cons_add, iteratedDeriv_cons, iteratedDeriv_cons, ih,
        LinearMap.comp_assoc]

@[simp]
lemma iteratedDeriv_singleton (μ : Fin 1 ⊕ Fin 3) :
    jets.iteratedDeriv ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = jets.deriv μ := by
  rw [show ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ 0 from rfl, iteratedDeriv_cons,
    iteratedDeriv_zero, LinearMap.comp_id]

lemma iteratedDeriv_cons_eq_comp_deriv (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    jets.iteratedDeriv (μ ::ₘ s) = (jets.iteratedDeriv s).comp (jets.deriv μ) := by
  rw [show (μ ::ₘ s : Multiset (Fin 1 ⊕ Fin 3)) = s + {μ} from by
      rw [add_comm, Multiset.singleton_add],
    iteratedDeriv_add, iteratedDeriv_singleton]

/-- The iterated Leibniz rule for the bracket. -/
lemma iteratedDeriv_bracket (s : Multiset (Fin 1 ⊕ Fin 3)) (a b : 𝔤J) :
    jets.iteratedDeriv s ⁅a, b⁆ =
      (s.antidiagonal.map fun p =>
        ⁅jets.iteratedDeriv p.1 a, jets.iteratedDeriv p.2 b⁆).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.antidiagonal_zero]
  | cons κ s ih =>
      rw [iteratedDeriv_cons, LinearMap.comp_apply, ih, map_multiset_sum,
        Multiset.map_map,
        Multiset.map_congr rfl (fun p hp => by
          rw [Function.comp_apply, jets.deriv_bracket,
            show jets.deriv κ (jets.iteratedDeriv p.1 a)
                = jets.iteratedDeriv (κ ::ₘ p.1) a from by
              rw [iteratedDeriv_cons]; rfl,
            show jets.deriv κ (jets.iteratedDeriv p.2 b)
                = jets.iteratedDeriv (κ ::ₘ p.2) b from by
              rw [iteratedDeriv_cons]; rfl]),
        Multiset.sum_map_add]
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      abel

lemma iteratedDeriv_ofConstantLie_of_ne_zero {p : Multiset (Fin 1 ⊕ Fin 3)} (hp : p ≠ 0)
    (a : 𝔤) : jets.iteratedDeriv p (jets.ofConstantLie a) = 0 := by
  induction p using Multiset.induction_on with
  | empty => exact absurd rfl hp
  | cons μ t ih =>
    rw [iteratedDeriv_cons, LinearMap.comp_apply]
    rcases eq_or_ne t 0 with rfl | ht
    · rw [iteratedDeriv_zero, LinearMap.id_apply, deriv_ofConstantLie]
    · rw [ih ht, map_zero]

lemma iteratedDeriv_adjointJ_ofConstant (g : G₀) (s : Multiset (Fin 1 ⊕ Fin 3)) (x : 𝔤J) :
    jets.iteratedDeriv s (jets.adjointJ (jets.ofConstant g) x) =
      jets.adjointJ (jets.ofConstant g) (jets.iteratedDeriv s x) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons μ s ih => simp [iteratedDeriv_cons, ih, deriv_adjointJ_ofConstant]

lemma evalLie_iteratedDeriv_mulCoord (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (a : 𝔤J) :
    jets.evalLie (jets.iteratedDeriv s (jets.mulCoord μ a)) =
      s.count μ • jets.evalLie (jets.iteratedDeriv (s.erase μ) a) := by
  induction s using Multiset.induction_on generalizing a with
  | empty => simp [jets.evalLie_mulCoord]
  | cons ν s ih =>
    rw [iteratedDeriv_cons_eq_comp_deriv, LinearMap.comp_apply, jets.deriv_mulCoord, map_add,
      map_add, ih, ← LinearMap.comp_apply (jets.iteratedDeriv _),
      ← iteratedDeriv_cons_eq_comp_deriv]
    obtain rfl | hνμ := eq_or_ne ν μ
    · by_cases hν : ν ∈ s <;> simp_all [Multiset.cons_erase, add_smul]
    · simp [hνμ, Multiset.count_cons_of_ne hνμ.symm, Multiset.erase_cons_tail s hνμ]

/-!

## D. Morphisms

-/

variable {G₀' : Type} [Group G₀'] {𝔤' : Type} [LieRing 𝔤'] [LieAlgebra ℝ 𝔤']
  {GJ' : Type} [Group GJ'] {𝔤J' : Type} [LieRing 𝔤J'] [LieAlgebra ℝ 𝔤J']

/-- A morphism of local gauge data.

  `Hom` is the standard name for a morphism in Lean. -/
structure Hom (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) (jets' : LocalGaugeData G₀' 𝔤' GJ' 𝔤J') where
  /-- The map of gauge groups. -/
  group : G₀ →* G₀'
  /-- The map of jet groups. -/
  groupJ : GJ →* GJ'
  eval_groupJ : ∀ U, jets'.eval (groupJ U) = group (jets.eval U)
  groupJ_ofConstant : ∀ g, groupJ (jets.ofConstant g) = jets'.ofConstant (group g)
  /-- The map of Lie algebras. -/
  lie : 𝔤 →ₗ⁅ℝ⁆ 𝔤'
  /-- The map of Lie algebras of jets. -/
  lieJ : 𝔤J →ₗ⁅ℝ⁆ 𝔤J'
  lieJ_ofConstantLie : ∀ c, lieJ (jets.ofConstantLie c) = jets'.ofConstantLie (lie c)
  evalLie_lieJ : ∀ a, jets'.evalLie (lieJ a) = lie (jets.evalLie a)
  lieJ_deriv : ∀ μ a, lieJ (jets.deriv μ a) = jets'.deriv μ (lieJ a)
  lieJ_mulCoord : ∀ μ a, lieJ (jets.mulCoord μ a) = jets'.mulCoord μ (lieJ a)
  lieJ_adjointJ : ∀ U a, lieJ (jets.adjointJ U a) = jets'.adjointJ (groupJ U) (lieJ a)
  lieJ_maurerCartan : ∀ U μ, lieJ (jets.maurerCartan U μ) = jets'.maurerCartan (groupJ U) μ

TODO "Add the constructor for `Hom` from a Lie group homomorphism."

namespace Hom

variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {jets' : LocalGaugeData G₀' 𝔤' GJ' 𝔤J'}
  (f : Hom jets jets')

/-!

### D.1. The adjoint action

-/

/-- A morphism intertwines the adjoint actions of the gauge groups. -/
lemma lie_adjoint (g : G₀) (x : 𝔤) :
    f.lie (jets.adjoint g x) = jets'.adjoint (f.group g) (f.lie x) := by
  have h := jets.evalLie_adjointJ (jets.ofConstant g) (jets.ofConstantLie x)
  rw [jets.eval_ofConstant, jets.evalLie_ofConstantLie] at h
  rw [← h, ← f.evalLie_lieJ, f.lieJ_adjointJ, f.groupJ_ofConstant, f.lieJ_ofConstantLie,
    jets'.evalLie_adjointJ, jets'.eval_ofConstant, jets'.evalLie_ofConstantLie]

/-!

### D.2. Relation to iterated derivatives

-/

/-- A morphism commutes with iterated derivatives. -/
lemma lieJ_iteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) (a : 𝔤J) :
    f.lieJ (jets.iteratedDeriv s a) = jets'.iteratedDeriv s (f.lieJ a) := by
  induction s using Multiset.induction_on generalizing a with
  | empty => simp
  | cons μ t ih =>
    rw [iteratedDeriv_cons, iteratedDeriv_cons, LinearMap.comp_apply, LinearMap.comp_apply,
      f.lieJ_deriv, ih]

/-!

### D.3. Identity morphisms

-/

/-- The identity morphism of local gauge data. -/
protected def id (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) : Hom jets jets where
  group := MonoidHom.id G₀
  groupJ := MonoidHom.id GJ
  eval_groupJ _ := rfl
  groupJ_ofConstant _ := rfl
  lie := LieHom.id
  lieJ := LieHom.id
  lieJ_ofConstantLie _ := rfl
  evalLie_lieJ _ := rfl
  lieJ_deriv _ _ := rfl
  lieJ_mulCoord _ _ := rfl
  lieJ_adjointJ _ _ := rfl
  lieJ_maurerCartan _ _ := rfl

/-!

### D.4. Composition of morphisms

-/

variable {G₀'' : Type} [Group G₀''] {𝔤'' : Type} [LieRing 𝔤''] [LieAlgebra ℝ 𝔤'']
  {GJ'' : Type} [Group GJ''] {𝔤J'' : Type} [LieRing 𝔤J''] [LieAlgebra ℝ 𝔤J'']
  {jets'' : LocalGaugeData G₀'' 𝔤'' GJ'' 𝔤J''}

/-- The composite `g ∘ f` of morphisms of local gauge data. -/
def comp (g : Hom jets' jets'') : Hom jets jets'' where
  group := g.group.comp f.group
  groupJ := g.groupJ.comp f.groupJ
  eval_groupJ U := by simp [g.eval_groupJ, f.eval_groupJ]
  groupJ_ofConstant c := by simp [f.groupJ_ofConstant, g.groupJ_ofConstant]
  lie := g.lie.comp f.lie
  lieJ := g.lieJ.comp f.lieJ
  lieJ_ofConstantLie c := by simp [f.lieJ_ofConstantLie, g.lieJ_ofConstantLie]
  evalLie_lieJ a := by simp [f.evalLie_lieJ, g.evalLie_lieJ]
  lieJ_deriv μ a := by simp [f.lieJ_deriv, g.lieJ_deriv]
  lieJ_mulCoord μ a := by simp [f.lieJ_mulCoord, g.lieJ_mulCoord]
  lieJ_adjointJ U a := by simp [f.lieJ_adjointJ, g.lieJ_adjointJ]
  lieJ_maurerCartan U μ := by simp [f.lieJ_maurerCartan, g.lieJ_maurerCartan]

end Hom

end LocalGaugeData
