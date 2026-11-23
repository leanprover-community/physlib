/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.Adjoint
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.MaurerCartan
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.Prod
/-!
# The jet operations of a global gauge group

The evaluation, derivatives, coordinates and adjoint actions on the jets of a global gauge group.

## i. Overview

A global gauge group `G` has gauge jets, the invertible matrices of jets with value in the
group and Maurer–Cartan form a Lie algebra jet, and Lie algebra jets, the matrices of jets with
every base-point derivative in the Lie algebra. This file gives the operations on them that the
transformation laws of gauge fields and matter fields are built from, as definitions on `G`.
Evaluation of a Lie algebra jet at the base point `G.evalLie` and the inclusion of constants
`G.ofConstantLie` are the entrywise constant coefficient and constant embedding. The derivative
`G.derivJ μ` and multiplication by a coordinate `G.mulCoordJ μ` act entrywise, `G.iteratedDerivJ`
is the iterated derivative, and the adjoint actions `G.adjointJ` of the gauge jets on the Lie
algebra jets and `G.adjointRep` of the group on its Lie algebra are conjugation `U A U⁻¹`. The
Maurer–Cartan form is `G.maurerCartan U μ = (∂_μ U) U⁻¹`. The laws these operations satisfy are
identities of matrices of jets. They include the Maurer–Cartan cocycle law and structure
equation `∂_μ ω_ν − ∂_ν ω_μ = [ω_μ, ω_ν]`, and the Leibniz rule
`∂_μ (U A U⁻¹) = U (∂_μ A) U⁻¹ + [ω_μ, U A U⁻¹]` for the adjoint action. For a compact group
inside the unitary group the hermitian generators of physics are `a = −i X`, with the bracket
`i (a b − b a)` and the Maurer–Cartan form `i (∂_μ U) U⁻¹`.

The jets of a global gauge group are determined by their Taylor data. A Lie algebra jet is
determined by its base-point derivatives, and a gauge jet with vanishing Maurer–Cartan form
is constant. Any Taylor data in `𝔤` are those of a Lie algebra jet, and any Lie algebra jet
`A` vanishing at the base point is the radial component `∑_μ x_μ ω_μ` of the Maurer–Cartan
form of the gauge jet solving `E U = −A U`, `U(0) = 1`. These facts are proved about gauge
jets and Lie algebra jets in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.Jet` and
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.MaurerCartan`, and assembled
here.

## ii. Key results

- `GlobalGaugeGroup.evalLie`, `GlobalGaugeGroup.ofConstantLie`, `GlobalGaugeGroup.derivJ`,
  `GlobalGaugeGroup.mulCoordJ`, `GlobalGaugeGroup.iteratedDerivJ`, `GlobalGaugeGroup.adjointJ`,
  `GlobalGaugeGroup.adjointRep` : the operations on the jets.
- `GlobalGaugeGroup.maurerCartan_cocycle`, `GlobalGaugeGroup.maurerCartan_structure`,
  `GlobalGaugeGroup.derivJ_adjointJ` : the laws of the Maurer–Cartan form.
- `GlobalGaugeGroup.ext_of_evalLie_iteratedDerivJ`,
  `GlobalGaugeGroup.exists_evalLie_iteratedDerivJ_eq` : a Lie algebra jet is determined by its
  base-point derivatives, and every Taylor datum is realised.

## iii. Table of contents

- A. Evaluation and constants on Lie algebra jets
- B. Derivatives and coordinates
  - B.1. The iterated derivative
- C. The adjoint actions
- D. The Maurer–Cartan form
  - D.1. First consequences of the laws
- E. Determination by Taylor data

## iv. References

* None.

-/

@[expose] public section

open Matrix MvPowerSeries SpaceTimeAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. Evaluation and constants on Lie algebra jets

-/

/-- Evaluation of a Lie algebra jet at the base point, the entrywise constant coefficient. -/
noncomputable def evalLie : G.jetLieSubalgebra →ₗ⁅ℝ⁆ G.lieSubalgebra where
  toFun A := ⟨(constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A.1, A.2 0⟩
  map_add' A B := Subtype.ext (map_add _ _ _)
  map_smul' r A := Subtype.ext (Matrix.ext fun i j => constantCoeff_real_smul r _)
  map_lie' {A B} := Subtype.ext (by
    show (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (A.1 * B.1 - B.1 * A.1) = _
    rw [map_sub, map_mul, map_mul]
    rfl)

@[simp]
lemma evalLie_val (A : G.jetLieSubalgebra) :
    (G.evalLie A).1 = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A.1 := rfl

/-- A constant Lie algebra element as a Lie algebra jet, the entrywise constant embedding. -/
noncomputable def ofConstantLie : G.lieSubalgebra →ₗ⁅ℝ⁆ G.jetLieSubalgebra where
  toFun a := ⟨(C : ℂ →+* SpaceTimeAlgebra).mapMatrix a.1, G.mapMatrix_C_mem_jetLieAlgebra a.2⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (Matrix.ext fun i j => C_real_smul r _)
  map_lie' {a b} := Subtype.ext (by
    show (C : ℂ →+* SpaceTimeAlgebra).mapMatrix (a.1 * b.1 - b.1 * a.1) = _
    rw [map_sub, map_mul, map_mul]
    rfl)

@[simp]
lemma ofConstantLie_val (a : G.lieSubalgebra) :
    (G.ofConstantLie a).1 = (C : ℂ →+* SpaceTimeAlgebra).mapMatrix a.1 := rfl

/-- Evaluating the constant Lie algebra jet of `a` at the base point gives back `a`. -/
@[simp]
lemma evalLie_ofConstantLie (a : G.lieSubalgebra) : G.evalLie (G.ofConstantLie a) = a :=
  Subtype.ext (Matrix.ext fun i j => by
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_C])

/-- Every Lie algebra element is the value of a Lie algebra jet, namely its constant jet. -/
lemma evalLie_surjective : Function.Surjective G.evalLie :=
  Function.LeftInverse.surjective G.evalLie_ofConstantLie

/-!

## B. Derivatives and coordinates

-/

/-- The formal derivative `∂_μ` of a Lie algebra jet in the spacetime direction `μ`, taken
  entrywise. -/
noncomputable def derivJ (μ : Fin 1 ⊕ Fin 3) :
    G.jetLieSubalgebra →ₗ[ℝ] G.jetLieSubalgebra where
  toFun A := ⟨A.1.map (pderiv μ), G.map_pderiv_mem_jetLieAlgebra A.2 μ⟩
  map_add' A B := Subtype.ext (Matrix.ext fun i j => map_add (pderiv μ) (A.1 i j) (B.1 i j))
  map_smul' r _ := Subtype.ext (Matrix.ext fun _ _ => pderiv_real_smul μ r _)

@[simp]
lemma derivJ_val (μ : Fin 1 ⊕ Fin 3) (A : G.jetLieSubalgebra) :
    (G.derivJ μ A).1 = A.1.map (pderiv μ) := rfl

/-- The formal derivatives commute. -/
lemma derivJ_comm (μ ν : Fin 1 ⊕ Fin 3) (A : G.jetLieSubalgebra) :
    G.derivJ μ (G.derivJ ν A) = G.derivJ ν (G.derivJ μ A) :=
  Subtype.ext (Matrix.ext fun _ _ => SpaceTimeAlgebra.pderiv_comm μ ν _)

/-- The Leibniz rule for the bracket of Lie algebra jets. -/
lemma derivJ_bracket (μ : Fin 1 ⊕ Fin 3) (A B : G.jetLieSubalgebra) :
    G.derivJ μ ⁅A, B⁆ = ⁅G.derivJ μ A, B⁆ + ⁅A, G.derivJ μ B⁆ :=
  Subtype.ext (by
    show (A.1 * B.1 - B.1 * A.1).map (pderiv μ) =
      (A.1.map (pderiv μ) * B.1 - B.1 * A.1.map (pderiv μ)) +
        (A.1 * B.1.map (pderiv μ) - B.1.map (pderiv μ) * A.1)
    rw [map_pderiv_sub, matrix_map_pderiv_mul, matrix_map_pderiv_mul]
    abel)

/-- A constant Lie algebra jet has vanishing derivative. -/
@[simp]
lemma derivJ_ofConstantLie (μ : Fin 1 ⊕ Fin 3) (a : G.lieSubalgebra) :
    G.derivJ μ (G.ofConstantLie a) = 0 :=
  Subtype.ext (map_pderiv_mapMatrix_C μ a.1)

/-- Multiplication of a Lie algebra jet by the spacetime coordinate `x_μ`. -/
noncomputable def mulCoordJ (μ : Fin 1 ⊕ Fin 3) :
    G.jetLieSubalgebra →ₗ[ℝ] G.jetLieSubalgebra where
  toFun A := ⟨(X μ : SpaceTimeAlgebra) • A.1, G.X_smul_mem_jetLieAlgebra μ A.2⟩
  map_add' _ _ := Subtype.ext (smul_add _ _ _)
  map_smul' r _ := Subtype.ext (smul_comm _ r _)

@[simp]
lemma mulCoordJ_val (μ : Fin 1 ⊕ Fin 3) (A : G.jetLieSubalgebra) :
    (G.mulCoordJ μ A).1 = (X μ : SpaceTimeAlgebra) • A.1 := rfl

/-- The Leibniz rule for a coordinate, `∂_μ (x_ν A) = x_ν ∂_μ A + δ_{μν} A`. -/
lemma derivJ_mulCoordJ (μ ν : Fin 1 ⊕ Fin 3) (A : G.jetLieSubalgebra) :
    G.derivJ μ (G.mulCoordJ ν A) = G.mulCoordJ ν (G.derivJ μ A) + if μ = ν then A else 0 := by
  split_ifs with h
  · subst h
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    show pderiv μ ((X μ : SpaceTimeAlgebra) * A.1 i j) =
      (X μ : SpaceTimeAlgebra) * pderiv μ (A.1 i j) + A.1 i j
    rw [Derivation.leibniz, pderiv_X_self, smul_eq_mul, smul_eq_mul, mul_one, add_comm]
  · refine Subtype.ext (Matrix.ext fun i j => ?_)
    show pderiv μ ((X ν : SpaceTimeAlgebra) * A.1 i j) =
      (X ν : SpaceTimeAlgebra) * pderiv μ (A.1 i j) + 0
    rw [Derivation.leibniz, pderiv_X_of_ne (Ne.symm h), smul_zero, add_zero, smul_eq_mul,
      add_zero]

/-- A multiple of a coordinate vanishes at the base point. -/
@[simp]
lemma evalLie_mulCoordJ (μ : Fin 1 ⊕ Fin 3) (A : G.jetLieSubalgebra) :
    G.evalLie (G.mulCoordJ μ A) = 0 :=
  Subtype.ext (Matrix.ext fun i j => by
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply])

/-!

### B.1. The iterated derivative

-/

/-- Post-composition with `derivJ` is right-commutative. -/
instance instRightCommutativeCompDerivJ : RightCommutative
    (fun (D : G.jetLieSubalgebra →ₗ[ℝ] G.jetLieSubalgebra) (μ : Fin 1 ⊕ Fin 3) =>
      D.comp (G.derivJ μ)) where
  right_comm D μ ν := LinearMap.ext fun a => congrArg D (G.derivJ_comm μ ν a)

/-- The iterated formal derivative on the Lie algebra jets, the product of `derivJ` over a
  multiset of directions. -/
noncomputable def iteratedDerivJ (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    G.jetLieSubalgebra →ₗ[ℝ] G.jetLieSubalgebra :=
  μs.foldl (fun D μ => D.comp (G.derivJ μ)) LinearMap.id

@[simp]
lemma iteratedDerivJ_zero :
    G.iteratedDerivJ (0 : Multiset (Fin 1 ⊕ Fin 3)) = LinearMap.id := by
  simp [iteratedDerivJ]

lemma iteratedDerivJ_cons (μ : Fin 1 ⊕ Fin 3) (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    G.iteratedDerivJ (μ ::ₘ μs) = (G.derivJ μ).comp (G.iteratedDerivJ μs) := by
  have h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (D : G.jetLieSubalgebra →ₗ[ℝ] G.jetLieSubalgebra),
      s.foldl (fun D μ => D.comp (G.derivJ μ)) D = D.comp (G.iteratedDerivJ s) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro D; simp [iteratedDerivJ]
    | cons κ t ih =>
        intro D
        rw [iteratedDerivJ, Multiset.foldl_cons, Multiset.foldl_cons, ih, ih]
        simp [LinearMap.comp_assoc]
  rw [iteratedDerivJ, Multiset.foldl_cons, h]
  simp

/-- The iterated derivative is additive in the multiset. -/
lemma iteratedDerivJ_add (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    G.iteratedDerivJ (s + t) = (G.iteratedDerivJ s).comp (G.iteratedDerivJ t) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons μ s ih =>
      rw [Multiset.cons_add, iteratedDerivJ_cons, iteratedDerivJ_cons, ih, LinearMap.comp_assoc]

@[simp]
lemma iteratedDerivJ_singleton (μ : Fin 1 ⊕ Fin 3) :
    G.iteratedDerivJ ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = G.derivJ μ := by
  rw [show ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ 0 from rfl, iteratedDerivJ_cons,
    iteratedDerivJ_zero, LinearMap.comp_id]

/-- The first derivative in a multiset may be taken first rather than last. -/
lemma iteratedDerivJ_cons_eq_comp_derivJ (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    G.iteratedDerivJ (μ ::ₘ s) = (G.iteratedDerivJ s).comp (G.derivJ μ) := by
  rw [show (μ ::ₘ s : Multiset (Fin 1 ⊕ Fin 3)) = s + {μ} from by
      rw [add_comm, Multiset.singleton_add],
    iteratedDerivJ_add, iteratedDerivJ_singleton]

/-- The iterated Leibniz rule for the bracket. -/
lemma iteratedDerivJ_bracket (s : Multiset (Fin 1 ⊕ Fin 3)) (a b : G.jetLieSubalgebra) :
    G.iteratedDerivJ s ⁅a, b⁆ =
      (s.antidiagonal.map fun p => ⁅G.iteratedDerivJ p.1 a, G.iteratedDerivJ p.2 b⁆).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.antidiagonal_zero]
  | cons κ s ih =>
      rw [iteratedDerivJ_cons, LinearMap.comp_apply, ih, map_multiset_sum, Multiset.map_map,
        Multiset.map_congr rfl (fun p hp => by
          rw [Function.comp_apply, G.derivJ_bracket,
            show G.derivJ κ (G.iteratedDerivJ p.1 a) = G.iteratedDerivJ (κ ::ₘ p.1) a from by
              rw [iteratedDerivJ_cons]; rfl,
            show G.derivJ κ (G.iteratedDerivJ p.2 b) = G.iteratedDerivJ (κ ::ₘ p.2) b from by
              rw [iteratedDerivJ_cons]; rfl]),
        Multiset.sum_map_add]
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      abel

/-- The iterated derivative is the entrywise iterated formal derivative. -/
lemma iteratedDerivJ_val (s : Multiset (Fin 1 ⊕ Fin 3)) (A : G.jetLieSubalgebra) :
    (G.iteratedDerivJ s A).1 = A.1.map fun f => iteratedPDeriv s f := by
  induction s using Multiset.induction_on generalizing A with
  | empty =>
    rw [iteratedDerivJ_zero, LinearMap.id_apply]
    ext i j : 1
    simp [Matrix.map_apply]
  | cons μ t ih =>
    rw [iteratedDerivJ_cons, LinearMap.comp_apply, derivJ_val, ih, Matrix.map_map]
    ext i j : 1
    simp only [Matrix.map_apply, Function.comp_apply, SpaceTimeAlgebra.iteratedPDeriv_cons]
    exact (SpaceTimeAlgebra.iteratedPDeriv_pderiv t μ _).symm

/-- The base-point value of the iterated derivative of a Lie algebra jet is its base-point
  derivative. -/
lemma evalLie_iteratedDerivJ_val (s : Multiset (Fin 1 ⊕ Fin 3)) (A : G.jetLieSubalgebra) :
    (G.evalLie (G.iteratedDerivJ s A)).1 = derivValueMatrix s A.1 := by
  rw [evalLie_val, iteratedDerivJ_val, RingHom.mapMatrix_apply, Matrix.map_map]
  rfl

/-- Every iterated derivative of a constant Lie algebra jet vanishes. -/
lemma iteratedDerivJ_ofConstantLie_of_ne_zero {p : Multiset (Fin 1 ⊕ Fin 3)} (hp : p ≠ 0)
    (a : G.lieSubalgebra) : G.iteratedDerivJ p (G.ofConstantLie a) = 0 := by
  induction p using Multiset.induction_on with
  | empty => exact absurd rfl hp
  | cons μ t ih =>
    rw [iteratedDerivJ_cons, LinearMap.comp_apply]
    rcases eq_or_ne t 0 with rfl | ht
    · rw [iteratedDerivJ_zero, LinearMap.id_apply, derivJ_ofConstantLie]
    · rw [ih ht, map_zero]

/-- The base-point value of an iterated derivative of a multiple of a coordinate. -/
lemma evalLie_iteratedDerivJ_mulCoordJ (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (a : G.jetLieSubalgebra) :
    G.evalLie (G.iteratedDerivJ s (G.mulCoordJ μ a)) =
      s.count μ • G.evalLie (G.iteratedDerivJ (s.erase μ) a) := by
  induction s using Multiset.induction_on generalizing a with
  | empty => simp
  | cons ν s ih =>
    rw [iteratedDerivJ_cons_eq_comp_derivJ, LinearMap.comp_apply, G.derivJ_mulCoordJ, map_add,
      map_add, ih, ← LinearMap.comp_apply (G.iteratedDerivJ _),
      ← iteratedDerivJ_cons_eq_comp_derivJ]
    obtain rfl | hνμ := eq_or_ne ν μ
    · by_cases hν : ν ∈ s <;> simp_all [Multiset.cons_erase, add_smul]
    · simp [hνμ, Multiset.count_cons_of_ne hνμ.symm, Multiset.erase_cons_tail s hνμ]

/-!

## C. The adjoint actions

-/

/-- The adjoint action `A ↦ U A U⁻¹` of the gauge jets on the Lie algebra jets. -/
noncomputable def adjointJ : Representation ℝ G.gaugeJetGroup G.jetLieSubalgebra where
  toFun U :=
    { toFun A := ⟨U.1.1 * A.1 * (U.1⁻¹).1, G.adjoint_mem_jetLieAlgebra U A.2⟩
      map_add' A B := Subtype.ext (by simp [mul_add, add_mul])
      map_smul' r A := Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun A => Subtype.ext (by simp)
  map_mul' U V := LinearMap.ext fun A => Subtype.ext (by
    simp [_root_.mul_inv_rev, mul_assoc])

@[simp]
lemma adjointJ_val (U : G.gaugeJetGroup) (A : G.jetLieSubalgebra) :
    (G.adjointJ U A).1 = U.1.1 * A.1 * (U.1⁻¹).1 := rfl

/-- The adjoint action `a ↦ g a g⁻¹` of the group on its Lie algebra. -/
noncomputable def adjointRep : Representation ℝ G.group G.lieSubalgebra where
  toFun g :=
    { toFun a := ⟨g.1.1 * a.1 * (g.1⁻¹).1,
        conj_mem_lieAlgebraOfIsClosed (hH := G.isClosed) g a.2⟩
      map_add' a b := Subtype.ext (by simp [mul_add, add_mul])
      map_smul' r a := Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun a => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun a => Subtype.ext (by
    simp [_root_.mul_inv_rev, mul_assoc])

@[simp]
lemma adjointRep_val (g : G.group) (a : G.lieSubalgebra) :
    (G.adjointRep g a).1 = g.1.1 * a.1 * (g.1⁻¹).1 := rfl

/-- The adjoint action of a gauge jet is by Lie algebra automorphisms. -/
lemma adjointJ_bracket (U : G.gaugeJetGroup) (A B : G.jetLieSubalgebra) :
    G.adjointJ U ⁅A, B⁆ = ⁅G.adjointJ U A, G.adjointJ U B⁆ :=
  Subtype.ext (by
    have hconj (P Q : Matrix κ κ SpaceTimeAlgebra) :
        (U.1.1 * P * (U.1⁻¹).1) * (U.1.1 * Q * (U.1⁻¹).1) = U.1.1 * (P * Q) * (U.1⁻¹).1 := by
      simp only [mul_assoc]
      rw [← mul_assoc (U.1⁻¹).1 U.1.1, Units.inv_mul, one_mul]
    show U.1.1 * (A.1 * B.1 - B.1 * A.1) * (U.1⁻¹).1 =
      (U.1.1 * A.1 * (U.1⁻¹).1) * (U.1.1 * B.1 * (U.1⁻¹).1) -
        (U.1.1 * B.1 * (U.1⁻¹).1) * (U.1.1 * A.1 * (U.1⁻¹).1)
    rw [hconj, hconj, mul_sub, sub_mul])

/-- At the base point the adjoint action of a gauge jet is the adjoint action of its value. -/
lemma evalLie_adjointJ (U : G.gaugeJetGroup) (A : G.jetLieSubalgebra) :
    G.evalLie (G.adjointJ U A) = G.adjointRep (G.evalGaugeJet U) (G.evalLie A) :=
  Subtype.ext (by
    show (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (U.1.1 * A.1 * (U.1⁻¹).1) =
      (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U.1.1 *
        (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A.1 *
          (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (U.1⁻¹).1
    rw [map_mul, map_mul])

/-- At the base point, the adjoint action of a gauge jet on a constant is the adjoint action of
  its value. -/
lemma evalLie_adjointJ_ofConstantLie (U : G.gaugeJetGroup) (a : G.lieSubalgebra) :
    G.evalLie (G.adjointJ U (G.ofConstantLie a)) = G.adjointRep (G.evalGaugeJet U) a := by
  rw [G.evalLie_adjointJ, G.evalLie_ofConstantLie]

/-!

## D. The Maurer–Cartan form

-/

/-- The Maurer–Cartan form is a cocycle for the adjoint action,
  `ω_μ(U V) = ω_μ(U) + U ω_μ(V) U⁻¹`. -/
lemma maurerCartan_cocycle (U V : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) :
    G.maurerCartan (U * V) μ = G.maurerCartan U μ + G.adjointJ U (G.maurerCartan V μ) :=
  Subtype.ext (G.maurerCartan_mul U V μ)

/-- The Maurer–Cartan structure equation `∂_μ ω_ν − ∂_ν ω_μ = [ω_μ, ω_ν]` in the Lie algebra
  jets. -/
lemma maurerCartan_structure (U : G.gaugeJetGroup) (μ ν : Fin 1 ⊕ Fin 3) :
    G.derivJ μ (G.maurerCartan U ν) - G.derivJ ν (G.maurerCartan U μ) =
      ⁅G.maurerCartan U μ, G.maurerCartan U ν⁆ :=
  Subtype.ext (G.map_pderiv_maurerCartan_sub U μ ν)

/-- The Leibniz rule for the adjoint action,
  `∂_μ (U A U⁻¹) = U (∂_μ A) U⁻¹ + [ω_μ, U A U⁻¹]`. -/
lemma derivJ_adjointJ (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) (A : G.jetLieSubalgebra) :
    G.derivJ μ (G.adjointJ U A) =
      G.adjointJ U (G.derivJ μ A) + ⁅G.maurerCartan U μ, G.adjointJ U A⁆ :=
  Subtype.ext (by
    -- The derivative of `U⁻¹` is `−U⁻¹ (∂_μ U) U⁻¹`, and the rest is bookkeeping.
    set V := U.1.1 with hV
    set W := (U.1⁻¹).1 with hW
    have hWV : W * V = 1 := Units.inv_mul _
    have hq : W.map (pderiv μ) = -(W * V.map (pderiv μ) * W) :=
      map_pderiv_of_mul_eq_one μ (Units.mul_inv _) hWV
    show (V * A.1 * W).map (pderiv μ) = V * A.1.map (pderiv μ) * W +
      ((V.map (pderiv μ) * W) * (V * A.1 * W) - (V * A.1 * W) * (V.map (pderiv μ) * W))
    rw [matrix_map_pderiv_mul, matrix_map_pderiv_mul, hq]
    simp only [mul_neg, add_mul, ← mul_assoc]
    rw [mul_assoc (V.map (pderiv μ)) W V, hWV, mul_one]
    abel)

/-!

### D.1. First consequences of the laws

-/

/-- The Maurer–Cartan form of an inverse, `ω_μ(U⁻¹) = − Ad_{U⁻¹} ω_μ(U)`, the cocycle law
  applied to `U⁻¹ U = 1`. -/
lemma maurerCartan_inv_adjointJ (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) :
    G.maurerCartan U⁻¹ μ = -G.adjointJ U⁻¹ (G.maurerCartan U μ) := by
  have h := G.maurerCartan_cocycle U⁻¹ U μ
  rw [inv_mul_cancel, G.maurerCartan_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- One derivative of the adjoint action on a constant is the bracket with the Maurer–Cartan
  form, the Leibniz rule `derivJ_adjointJ` with the constant's derivative killed. -/
lemma derivJ_adjointJ_ofConstantLie (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3)
    (a : G.lieSubalgebra) :
    G.derivJ μ (G.adjointJ U (G.ofConstantLie a)) =
      ⁅G.maurerCartan U μ, G.adjointJ U (G.ofConstantLie a)⁆ := by
  rw [G.derivJ_adjointJ, G.derivJ_ofConstantLie, map_zero, zero_add]

/-- The Maurer–Cartan form of a conjugate, by the cocycle law, the conjugating jet
  contributes its own form and its transport by the conjugate. -/
lemma maurerCartan_conj (g U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) :
    G.maurerCartan (g * U * g⁻¹) μ =
      G.maurerCartan g μ + G.adjointJ g (G.maurerCartan U μ)
        - G.adjointJ (g * U * g⁻¹) (G.maurerCartan g μ) := by
  rw [G.maurerCartan_cocycle (g * U) g⁻¹, G.maurerCartan_cocycle g U,
    G.maurerCartan_inv_adjointJ, map_neg, map_mul G.adjointJ (g * U) g⁻¹, mul_apply_eq_comp,
    sub_eq_add_neg]

/-- The base-point Taylor data of a bracket is determined by that of its arguments.
  If the base-point values of the iterated derivatives of `a` and `b` along sub-multisets
  of `w` agree with those of `a'` and `b'`, then so do those of the brackets, the iterated
  Leibniz rule expands the bracket over the antidiagonal of `w`, whose parts are all
  sub-multisets of `w`. -/
lemma evalLie_iteratedDerivJ_bracket_congr (w : Multiset (Fin 1 ⊕ Fin 3))
    (a b a' b' : G.jetLieSubalgebra)
    (ha : ∀ p ≤ w, G.evalLie (G.iteratedDerivJ p a) = G.evalLie (G.iteratedDerivJ p a'))
    (hb : ∀ p ≤ w, G.evalLie (G.iteratedDerivJ p b) = G.evalLie (G.iteratedDerivJ p b')) :
    G.evalLie (G.iteratedDerivJ w ⁅a, b⁆) = G.evalLie (G.iteratedDerivJ w ⁅a', b'⁆) := by
  rw [iteratedDerivJ_bracket, iteratedDerivJ_bracket, map_multiset_sum, map_multiset_sum,
    Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  simp only [Function.comp_apply]
  rw [LieHom.map_lie, LieHom.map_lie, ha p.1 (Multiset.fst_le_of_mem_antidiagonal hp),
    hb p.2 (Multiset.snd_le_of_mem_antidiagonal hp)]

/-!

## E. Determination by Taylor data

A Lie algebra jet is determined by its base-point derivatives, a gauge jet with vanishing
Maurer–Cartan form is constant
(`GlobalGaugeGroup.eq_gaugeJetOfConstant_of_maurerCartan_eq_zero`), every family of Taylor data
in the Lie algebra is that of a Lie algebra jet, and every Lie algebra jet vanishing at the base
point is the radial component of the Maurer–Cartan form of a gauge jet with value one
(`GlobalGaugeGroup.exists_sum_X_smul_maurerCartan_eq`).

-/

/-- A Lie algebra jet is determined by the base-point values of its iterated derivatives. -/
lemma ext_of_evalLie_iteratedDerivJ {A B : G.jetLieSubalgebra}
    (h : ∀ s, G.evalLie (G.iteratedDerivJ s A) = G.evalLie (G.iteratedDerivJ s B)) : A = B :=
  Subtype.ext <| matrix_ext_of_derivValueMatrix fun s => by
    rw [← evalLie_iteratedDerivJ_val, ← evalLie_iteratedDerivJ_val, h s]

/-- Every family of Taylor data in the Lie algebra is the family of base-point values of the
  iterated derivatives of a Lie algebra jet. -/
lemma exists_evalLie_iteratedDerivJ_eq (c : Multiset (Fin 1 ⊕ Fin 3) → G.lieSubalgebra) :
    ∃ A : G.jetLieSubalgebra, ∀ s, G.evalLie (G.iteratedDerivJ s A) = c s :=
  ⟨⟨taylorMatrix fun s => (c s).1, G.taylorMatrix_mem_jetLieAlgebra fun s => (c s).2⟩,
    fun s => Subtype.ext (by
      rw [evalLie_iteratedDerivJ_val]
      exact map_constantCoeff_iteratedPDeriv_taylorMatrix _ s)⟩

end GlobalGaugeGroup
