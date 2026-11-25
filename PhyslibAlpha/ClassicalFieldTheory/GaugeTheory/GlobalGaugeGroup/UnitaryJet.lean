/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.MaurerCartan
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.U1
/-!
# The gauge jets of unitary gauge groups

The gauge jets of `SU(n)` and `U(1)` are unitary at every order.

## i. Overview

When every element of a global gauge group is unitary, its generators are anti-hermitian, the
derivative at `t = 0` of `exp (t X)† exp (t X) = 1`. The Maurer–Cartan form `ω_μ = (∂_μ U) U⁻¹`
of a gauge jet is a Lie algebra jet, so each of its base-point derivatives is anti-hermitian,
and so `ω_μ† = −ω_μ` as a matrix of jets. Then `U† U` has vanishing derivatives,
`∂_μ (U† U) = (ω_μ U)† U + U† ω_μ U = 0`, so it is the constant `1` of its value. Thus
every gauge jet of `SU(n)` or `U(1)` is a unitary matrix of jets, with `U⁻¹ = U†`.

For `U(1)` this makes every gauge jet the scalar matrix of a unitary jet.

## ii. Key results

- `GlobalGaugeGroup.star_eq_neg_of_mem_lieAlgebra` : the generators of a unitary global gauge
  group are anti-hermitian.
- `GlobalGaugeGroup.star_mul_self_gaugeJet` : a gauge jet of a unitary global gauge group is
  unitary.
- `GlobalGaugeGroup.SU.star_mul_self`, `GlobalGaugeGroup.SU.mul_star_self` : the gauge jets of
  `SU(n)` are unitary matrices of jets.
- `GlobalGaugeGroup.U1.unitaryJet` : the unitary jet of a gauge jet of `U(1)`.
- `GlobalGaugeGroup.U1.gaugeJet_eq_scalar` : every gauge jet of `U(1)` is a scalar matrix.

## iii. Table of contents

- A. Generators of unitary groups are anti-hermitian
- B. Lie algebra jets of unitary groups are anti-hermitian
- C. Gauge jets of unitary groups are unitary
- D. The gauge jets of SU(n)
- E. The gauge jets of U(1)

## iv. References

* None.

-/

@[expose] public section

open Matrix MvPowerSeries SpaceTimeAlgebra NormedSpace

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. Generators of unitary groups are anti-hermitian

-/

/-- The generators of a global gauge group all of whose elements are unitary are
  anti-hermitian. The conjugate transpose of `exp (t X)` is `exp (t X†)` and is the inverse
  `exp (−t X)`, so the two one-parameter families have the same derivative at `t = 0`. -/
lemma star_eq_neg_of_mem_lieAlgebra (hG : ∀ g ∈ G.group, star (g : Matrix κ κ ℂ) * g = 1)
    {X : Matrix κ κ ℂ} (hX : X ∈ G.lieAlgebra) : star X = -X := by
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  have key : ∀ t : ℝ, exp (t • star X) = exp (t • -X) := fun t => by
    obtain ⟨g, hg⟩ := hX t
    have h1 : exp (t • star X) * exp (t • X) = 1 := by
      have := hG g.1 g.2
      rwa [show (g.1 : Matrix κ κ ℂ) = exp (t • X) from hg, star_eq_conjTranspose,
        ← Matrix.exp_conjTranspose, ← star_eq_conjTranspose, star_smul, star_trivial] at this
    have h2 : exp (t • X) * exp (t • -X) = 1 := by
      rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_right,
        add_neg_cancel, NormedSpace.exp_zero]
    calc exp (t • star X) = exp (t • star X) * (exp (t • X) * exp (t • -X)) := by rw [h2, mul_one]
      _ = exp (t • -X) := by rw [← mul_assoc, h1, one_mul]
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (star X) 0
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0
  have h1' := h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (key t).symm)
  simpa using h1'.unique h2

/-!

## B. Lie algebra jets of unitary groups are anti-hermitian

-/

/-- The base-point derivatives of the conjugate transpose of a matrix of jets are the
  conjugate transposes of its base-point derivatives. -/
lemma derivValueMatrix_star (s : Multiset (Fin 1 ⊕ Fin 3)) (M : Matrix κ κ SpaceTimeAlgebra) :
    derivValueMatrix s (star M) = star (derivValueMatrix s M) := by
  induction s using Multiset.induction_on generalizing M with
  | empty => exact mapMatrix_constantCoeff_star M
  | cons μ t ih => rw [derivValueMatrix_cons, derivValueMatrix_cons, ← star_map_pderiv, ih]

/-- A Lie algebra jet of a global gauge group all of whose elements are unitary is
  anti-hermitian as a matrix of jets. -/
lemma star_eq_neg_of_mem_jetLieAlgebra (hG : ∀ g ∈ G.group, star (g : Matrix κ κ ℂ) * g = 1)
    {A : Matrix κ κ SpaceTimeAlgebra} (hA : A ∈ G.jetLieAlgebra) : star A = -A := by
  refine matrix_ext_of_derivValueMatrix fun s => ?_
  rw [derivValueMatrix_star, G.star_eq_neg_of_mem_lieAlgebra hG (hA s)]
  simpa using (derivValueMatrix_real_smul s (-1) A).symm

/-!

## C. Gauge jets of unitary groups are unitary

-/

/-- A gauge jet of a global gauge group all of whose elements are unitary is a unitary
  matrix of jets, `U† U = 1`. The product `U† U` has vanishing derivatives, since the
  Maurer–Cartan form is anti-hermitian, so it is the constant of its value. -/
lemma star_mul_self_gaugeJet (hG : ∀ g ∈ G.group, star (g : Matrix κ κ ℂ) * g = 1)
    (U : G.gaugeJetGroup) :
    star (U.1 : Matrix κ κ SpaceTimeAlgebra) * (U.1 : Matrix κ κ SpaceTimeAlgebra) = 1 := by
  set A := (U.1 : Matrix κ κ SpaceTimeAlgebra)
  have hω := fun μ => G.star_eq_neg_of_mem_jetLieAlgebra hG (U.2.2 μ)
  have hder (μ : Fin 1 ⊕ Fin 3) : A.map (pderiv μ) =
      (A.map (pderiv μ) * (↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra)) * A := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  have hd (μ : Fin 1 ⊕ Fin 3) : (star A * A).map (pderiv μ) = 0 := by
    rw [matrix_map_pderiv_mul, ← star_map_pderiv, hder μ, star_mul, hω μ]
    simp only [Matrix.mul_neg, Matrix.neg_mul, mul_assoc]
    exact neg_add_cancel _
  have hc : star A * A = (C : ℂ →+* SpaceTimeAlgebra).mapMatrix
      ((constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (star A * A)) := by
    refine Matrix.ext fun i j => ?_
    exact SpaceTimeAlgebra.eq_C_of_pderiv_eq_zero fun μ => congrArg (fun M => M i j) (hd μ)
  rw [hc, map_mul, mapMatrix_constantCoeff_star]
  have h := hG _ U.2.1
  rw [unitsEval_val] at h
  rw [h, map_one]

/-- The inverse of a gauge jet of a global gauge group all of whose elements are unitary is
  its conjugate transpose. -/
lemma star_eq_inv_gaugeJet (hG : ∀ g ∈ G.group, star (g : Matrix κ κ ℂ) * g = 1)
    (U : G.gaugeJetGroup) :
    star (U.1 : Matrix κ κ SpaceTimeAlgebra) = (↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra) := by
  calc star (U.1 : Matrix κ κ SpaceTimeAlgebra)
      = star (U.1 : Matrix κ κ SpaceTimeAlgebra) *
        ((U.1 : Matrix κ κ SpaceTimeAlgebra) * (↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra)) := by
        rw [Units.mul_inv, mul_one]
    _ = (↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra) := by
        rw [← mul_assoc, G.star_mul_self_gaugeJet hG U, one_mul]

/-!

## D. The gauge jets of SU(n)

-/

/-- The elements of `SU(n)` are unitary, `g† g = 1`. -/
lemma SU.star_mul_self_val {n : ℕ} {g : GeneralLinearGroup (Fin n) ℂ}
    (hg : g ∈ (SU n).group) : star (g : Matrix (Fin n) (Fin n) ℂ) * g = 1 :=
  mem_unitaryGroup_iff'.1 (mem_specialUnitaryGroup_iff.1 (mem_SU_iff.1 hg)).1

/-- A gauge jet of `SU(n)` is a unitary matrix of jets, `U† U = 1`. -/
lemma SU.star_mul_self {n : ℕ} (U : (SU n).gaugeJetGroup) :
    star (U.1 : Matrix (Fin n) (Fin n) SpaceTimeAlgebra) * U.1 = 1 :=
  (SU n).star_mul_self_gaugeJet (fun _ hg => SU.star_mul_self_val hg) U

/-- A gauge jet of `SU(n)` is a unitary matrix of jets, `U U† = 1`. -/
lemma SU.mul_star_self {n : ℕ} (U : (SU n).gaugeJetGroup) :
    (U.1 : Matrix (Fin n) (Fin n) SpaceTimeAlgebra) * star U.1 = 1 :=
  mul_eq_one_comm.1 (SU.star_mul_self U)

/-- The inverse of a gauge jet of `SU(n)` is its conjugate transpose. -/
lemma SU.star_eq_inv {n : ℕ} (U : (SU n).gaugeJetGroup) :
    star (U.1 : Matrix (Fin n) (Fin n) SpaceTimeAlgebra) =
      (↑U.1⁻¹ : Matrix (Fin n) (Fin n) SpaceTimeAlgebra) :=
  (SU n).star_eq_inv_gaugeJet (fun _ hg => SU.star_mul_self_val hg) U

/-!

## E. The gauge jets of U(1)

-/

/-- The elements of `U(1)` are unitary, `g† g = 1`. -/
lemma U1.star_mul_self_val {g : GeneralLinearGroup (Fin 1) ℂ} (hg : g ∈ U1.group) :
    star (g : Matrix (Fin 1) (Fin 1) ℂ) * g = 1 :=
  mem_unitaryGroup_iff'.1 (mem_U1_iff_mem_unitaryGroup.1 hg)

/-- A gauge jet of `U(1)` is a unitary matrix of jets, `U† U = 1`. -/
lemma U1.star_mul_self (U : U1.gaugeJetGroup) :
    star (U.1 : Matrix (Fin 1) (Fin 1) SpaceTimeAlgebra) * U.1 = 1 :=
  U1.star_mul_self_gaugeJet (fun _ hg => U1.star_mul_self_val hg) U

/-- The inverse of a gauge jet of `U(1)` is its conjugate transpose. -/
lemma U1.star_eq_inv (U : U1.gaugeJetGroup) :
    star (U.1 : Matrix (Fin 1) (Fin 1) SpaceTimeAlgebra) =
      (↑U.1⁻¹ : Matrix (Fin 1) (Fin 1) SpaceTimeAlgebra) :=
  U1.star_eq_inv_gaugeJet (fun _ hg => U1.star_mul_self_val hg) U

/-- The unitary jet of a gauge jet of `U(1)`, its only matrix entry. -/
def U1.unitaryJet (U : U1.gaugeJetGroup) : unitary SpaceTimeAlgebra :=
  ⟨(U.1 : Matrix (Fin 1) (Fin 1) SpaceTimeAlgebra) 0 0, by
    have h := congrFun (congrFun (U1.star_mul_self U) 0) 0
    simp [Matrix.mul_apply, Matrix.star_apply] at h
    exact ⟨h, by simpa [mul_comm] using h⟩⟩

/-- Every gauge jet of `U(1)` is the scalar matrix of its unitary jet. -/
lemma U1.gaugeJet_eq_scalar (U : U1.gaugeJetGroup) :
    (U.1 : Matrix (Fin 1) (Fin 1) SpaceTimeAlgebra) =
      Matrix.scalar (Fin 1) (U1.unitaryJet U : SpaceTimeAlgebra) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [U1.unitaryJet]

end GlobalGaugeGroup
