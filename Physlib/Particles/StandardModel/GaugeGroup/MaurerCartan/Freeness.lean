/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Relativity.JetRing.Matrix
/-!
# Freeness of the Standard Model jets

## i. Overview

A local-gauge-data package is `Free` when its jets are honest formal power series in the
spacetime coordinates: every family of base-point Taylor data is realized by an element of
the jet Lie algebra (Taylor completeness), and every element vanishing at the base point
is the radial component `∑_μ x_μ ω_μ(U)` of the Maurer–Cartan form of some pure jet
(radial integrability). The general theory then makes the symmetrized Maurer–Cartan data
free coordinates on the pure jets, `LocalGaugeData.symmetrizedMaurerCartanCoeff_bijective`,
which is what the classification of gauge invariants uses.

Both properties are statements about power series, proved here from the matrix
definitions. Taylor completeness is the construction of a power series from its Taylor
coefficients, entry by entry. Radial integrability is the solution of the Euler system
`E U = −i ρ U`, `U(0) = 1` for a prescribed `ρ`, factor by factor by
`JetRing.exists_matrix_eulerTransport`, with unitarity and unit determinant from the Euler
vanishing principle; then `∑_μ x_μ · i (∂_μ U) U† = ρ`. The same integration technique,
applied to the full structural equation, shows that every flat jet 1-form is the
Maurer–Cartan form of a pure jet, `exists_maurerCartanForm_eq_of_structure`.

## ii. Key results

- `StandardModel.exists_maurerCartanForm_eq_of_structure` : every flat jet 1-form is the
  Maurer–Cartan form of a pure jet.
- `StandardModel.taylorJet`, `StandardModel.eval_iteratedDeriv_taylorJet` : Taylor
  completeness of the jet gauge algebra.
- `StandardModel.exists_radial_eq` : radial integrability of the jet gauge group.
- `StandardModel.instFreeLocalGaugeData` : the package is free.

## iii. Table of contents

- A. Integrating the structural equation
- B. Taylor completeness
- C. Radial integrability

-/

@[expose] public section

namespace StandardModel

open MvPowerSeries JetGaugeAlgebra JetRing

/-!

## A. Integrating the structural equation

-/

/-- Every flat jet 1-form is the Maurer–Cartan form of a pure jet: the converse of the
  structural equation. The jet is the parallel transport
  `exists_deriv_eq_of_maurerCartanForm_structure`, and unitarity turns
  `∂_μ U = −i ω_μ U` into `ω_μ = i (∂_μ U) U⁻¹`. -/
lemma exists_maurerCartanForm_eq_of_structure
    (ω : (Fin 1 ⊕ Fin 3) → JetGaugeAlgebra)
    (hω : ∀ μ ν, deriv μ (ω ν) - deriv ν (ω μ) + ⁅ω μ, ω ν⁆ = 0) :
    ∃ U ∈ localGaugeData.truncationKer 0, maurerCartanForm U = ω := by
  obtain ⟨U, hU0, hU⟩ := exists_deriv_eq_of_maurerCartanForm_structure ω hω
  refine ⟨U, localGaugeData.mem_truncationKer_zero_iff.mpr hU0, funext fun μ => ?_⟩
  have hu3 : U.1.1 * star U.1.1 = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hu2 : U.2.1.1 * star U.2.1.1 = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hu1 : U.2.2.1 * star U.2.2.1 = 1 := (Unitary.mem_iff.mp U.2.2.2).2
  refine ext_of_matrix ?_ ?_ ?_
  · rw [maurerCartanForm_toSU3Matrix,
      show U.1.1.map (pderiv ℂ μ) = (-Complex.I) • (ω μ).toSU3Matrix * U.1.1 from
        congrArg (fun p => p.1) (hU μ),
      smul_mul_assoc, smul_mul_assoc, mul_assoc, hu3, mul_one, smul_smul]
    simp
  · rw [maurerCartanForm_toSU2Matrix,
      show U.2.1.1.map (pderiv ℂ μ) = (-Complex.I) • (ω μ).toSU2Matrix * U.2.1.1 from
        congrArg (fun p => p.2.1) (hU μ),
      smul_mul_assoc, smul_mul_assoc, mul_assoc, hu2, mul_one, smul_smul]
    simp
  · rw [maurerCartanForm_toU1Value,
      show pderiv ℂ μ U.2.2.1 = (-Complex.I) • (ω μ).toU1Value * U.2.2.1 from
        congrArg (fun p => p.2.2) (hU μ),
      smul_mul_assoc, smul_mul_assoc, mul_assoc, hu1, mul_one, smul_smul]
    simp

/-!

## B. Taylor completeness

-/

/-- The power series with prescribed base-point Taylor data `f`: the coefficient at the
  monomial `m` is `f` at the multiset of `m`, divided by the factorials of `m`. -/
noncomputable def taylorSeries (f : Multiset (Fin 1 ⊕ Fin 3) → ℂ) : JetRing :=
  fun m => ((∏ ν, Nat.factorial (m ν) : ℕ) : ℂ)⁻¹ * f (Finsupp.toMultiset m)

lemma coeff_taylorSeries (f : Multiset (Fin 1 ⊕ Fin 3) → ℂ) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff m (taylorSeries f) = ((∏ ν, Nat.factorial (m ν) : ℕ) : ℂ)⁻¹ * f (Finsupp.toMultiset m) :=
  rfl

lemma star_taylorSeries (f : Multiset (Fin 1 ⊕ Fin 3) → ℂ) :
    star (taylorSeries f) = taylorSeries fun s => star (f s) := by
  ext m
  rw [JetRing.coeff_star, coeff_taylorSeries, coeff_taylorSeries, star_mul', star_inv₀,
    star_natCast]

lemma taylorSeries_sum {ι : Type} (t : Finset ι) (f : ι → Multiset (Fin 1 ⊕ Fin 3) → ℂ) :
    taylorSeries (fun s => ∑ i ∈ t, f i s) = ∑ i ∈ t, taylorSeries (f i) := by
  ext m
  simp only [coeff_taylorSeries, map_sum, Finset.mul_sum]

/-- The base-point Taylor data of `taylorSeries f` are `f`. -/
lemma constantCoeff_foldl_pderiv_taylorSeries (f : Multiset (Fin 1 ⊕ Fin 3) → ℂ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    constantCoeff (s.foldl (fun h ρ => pderiv ℂ ρ h) (taylorSeries f)) = f s := by
  have hfac : ((∏ ν, Nat.factorial (s.count ν) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.factorial_ne_zero _)
  rw [constantCoeff_foldl_pderiv, coeff_taylorSeries, Multiset.toFinsupp_toMultiset,
    show (∏ ν, Nat.factorial (s.toFinsupp ν)) = ∏ ν, Nat.factorial (s.count ν) from
      Finset.prod_congr rfl fun ν _ => by rw [Multiset.toFinsupp_apply],
    ← mul_assoc, mul_inv_cancel₀ hfac, one_mul]

/-- The matrix of jets with prescribed base-point Taylor data `M`, entrywise. -/
noncomputable def taylorMatrix {κ : Type} (M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ) :
    Matrix κ κ JetRing :=
  Matrix.of fun i j => taylorSeries fun s => M s i j

lemma taylorMatrix_apply {κ : Type} (M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ) (i j : κ) :
    taylorMatrix M i j = taylorSeries fun s => M s i j :=
  rfl

lemma star_taylorMatrix {κ : Type} {M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ}
    (hM : ∀ s, star (M s) = M s) : star (taylorMatrix M) = taylorMatrix M := by
  ext i j : 1
  rw [Matrix.star_apply, taylorMatrix_apply, taylorMatrix_apply, star_taylorSeries]
  exact congrArg taylorSeries (funext fun s => by rw [← Matrix.star_apply, hM s])

lemma trace_taylorMatrix {κ : Type} [Fintype κ] {M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ}
    (hM : ∀ s, (M s).trace = 0) : (taylorMatrix M).trace = 0 := by
  have h : ∀ s, ∑ i, M s i i = 0 := fun s => hM s
  simp only [Matrix.trace, Matrix.diag_apply, taylorMatrix_apply, ← taylorSeries_sum, h]
  ext m
  simp [coeff_taylorSeries]

/-- The jet gauge algebra element with prescribed base-point Taylor data `c`, built
  entrywise from `taylorSeries`. Hermiticity and tracelessness are inherited from the
  values of `c`. -/
noncomputable def taylorJet (c : Multiset (Fin 1 ⊕ Fin 3) → GaugeAlgebra) : JetGaugeAlgebra :=
  ofMatrixProd
    (taylorMatrix fun s => (c s).toSU3Matrix, taylorMatrix fun s => (c s).toSU2Matrix,
      taylorSeries fun s => (c s).toU1Value)
    ⟨star_taylorMatrix fun s => (c s).1.2.1, trace_taylorMatrix fun s => (c s).1.2.2⟩
    ⟨star_taylorMatrix fun s => (c s).2.1.2.1, trace_taylorMatrix fun s => (c s).2.1.2.2⟩
    (by rw [star_taylorSeries]; exact congrArg taylorSeries (funext fun s => (c s).2.2.2))

@[simp]
lemma taylorJet_toSU3Matrix (c : Multiset (Fin 1 ⊕ Fin 3) → GaugeAlgebra) :
    (taylorJet c).toSU3Matrix = taylorMatrix fun s => (c s).toSU3Matrix :=
  rfl

@[simp]
lemma taylorJet_toSU2Matrix (c : Multiset (Fin 1 ⊕ Fin 3) → GaugeAlgebra) :
    (taylorJet c).toSU2Matrix = taylorMatrix fun s => (c s).toSU2Matrix :=
  rfl

@[simp]
lemma taylorJet_toU1Value (c : Multiset (Fin 1 ⊕ Fin 3) → GaugeAlgebra) :
    (taylorJet c).toU1Value = taylorSeries fun s => (c s).toU1Value :=
  rfl

/-- Taylor completeness: the base-point Taylor data of `taylorJet c` are `c`. -/
theorem eval_iteratedDeriv_taylorJet (c : Multiset (Fin 1 ⊕ Fin 3) → GaugeAlgebra)
    (s : Multiset (Fin 1 ⊕ Fin 3)) : eval (iteratedDeriv s (taylorJet c)) = c s := by
  refine GaugeAlgebra.ext_of_matrix ?_ ?_ ?_
  · ext i j
    rw [eval_iteratedDeriv_toSU3Matrix, Matrix.map_apply, taylorJet_toSU3Matrix,
      taylorMatrix_apply, constantCoeff_foldl_pderiv_taylorSeries]
  · ext i j
    rw [eval_iteratedDeriv_toSU2Matrix, Matrix.map_apply, taylorJet_toSU2Matrix,
      taylorMatrix_apply, constantCoeff_foldl_pderiv_taylorSeries]
  · rw [eval_iteratedDeriv_toU1Value, taylorJet_toU1Value, constantCoeff_foldl_pderiv_taylorSeries]

/-!

## C. Radial integrability

-/

/-- The `su(3)` component of the radial Maurer–Cartan component `∑_μ x_μ ω_μ(U)`. -/
lemma radial_toSU3Matrix (U : JetGaugeGroupI) :
    (localGaugeData.radial U).toSU3Matrix =
      ∑ μ, (X μ : JetRing) • (Complex.I • (U.1.1.map (pderiv ℂ μ) * star U.1.1)) := by
  rw [LocalGaugeData.radial, toSU3Matrix_sum]
  simp only [localGaugeData_coord, localGaugeData_maurerCartan,
    coord_toSU3Matrix, maurerCartanForm_toSU3Matrix]

/-- The `su(2)` component of the radial Maurer–Cartan component. -/
lemma radial_toSU2Matrix (U : JetGaugeGroupI) :
    (localGaugeData.radial U).toSU2Matrix =
      ∑ μ, (X μ : JetRing) • (Complex.I • (U.2.1.1.map (pderiv ℂ μ) * star U.2.1.1)) := by
  rw [LocalGaugeData.radial, toSU2Matrix_sum]
  simp only [localGaugeData_coord, localGaugeData_maurerCartan,
    coord_toSU2Matrix, maurerCartanForm_toSU2Matrix]

/-- The `u(1)` component of the radial Maurer–Cartan component. -/
lemma radial_toU1Value (U : JetGaugeGroupI) :
    (localGaugeData.radial U).toU1Value =
      ∑ μ, (X μ : JetRing) • (Complex.I • (pderiv ℂ μ U.2.2.1 * star U.2.2.1)) := by
  rw [LocalGaugeData.radial, toU1Value_sum]
  simp only [localGaugeData_coord, localGaugeData_maurerCartan,
    coord_toU1Value, maurerCartanForm_toU1Value, smul_eq_mul]

/-- The factorwise construction behind radial integrability: for every hermitian matrix
  `P` of jets vanishing at the base point there is a unitary Euler transport `V` based at
  `1` whose radial Maurer–Cartan component `∑_μ x_μ · i (∂_μ V) V†` is `P`; and `V` has
  unit determinant when `P` is traceless. -/
lemma exists_eulerTransport_of_radial {κ : Type} [Fintype κ] [DecidableEq κ]
    (P : Matrix κ κ JetRing) (hP0 : ∀ i j, constantCoeff (P i j) = 0) (hPstar : star P = P) :
    ∃ V : Matrix κ κ JetRing,
      (constantCoeff : JetRing →+* ℂ).mapMatrix V = 1 ∧
      V * star V = 1 ∧
      (P.trace = 0 →
        (∀ (M : Matrix κ κ JetRing) (μ : Fin 1 ⊕ Fin 3),
          pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace) → V.det = 1) ∧
      ∑ μ, (X μ : JetRing) • (Complex.I • (V.map (pderiv ℂ μ) * star V)) = P := by
  have hR0 : ∀ i j, constantCoeff (((-Complex.I) • P) i j) = 0 := fun i j => by
    rw [Matrix.smul_apply, ← coeff_zero_eq_constantCoeff, map_smul,
      coeff_zero_eq_constantCoeff, hP0, smul_zero]
  have hRstar : star ((-Complex.I) • P) = -((-Complex.I) • P) := by
    rw [star_smul, hPstar]
    simp
  obtain ⟨V, hV0, hEV⟩ := exists_matrix_eulerTransport ((-Complex.I) • P) hR0
  have hVu : V * star V = 1 := eulerTransport_mul_star hRstar hR0 hV0 hEV
  refine ⟨V, hV0, hVu, fun hPtr hjac =>
    eulerTransport_det hjac (by rw [Matrix.trace_smul, hPtr, smul_zero]) hV0 hEV, ?_⟩
  calc ∑ μ, (X μ : JetRing) • (Complex.I • (V.map (pderiv ℂ μ) * star V))
      = Complex.I • ((∑ μ, (X μ : JetRing) • V.map (pderiv ℂ μ)) * star V) := by
        rw [Finset.sum_mul, Finset.smul_sum]
        exact Finset.sum_congr rfl fun μ _ => by
          rw [Matrix.smul_mul, smul_comm Complex.I]
    _ = P := by
        rw [hEV, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc, hVu, mul_one, smul_smul]
        simp

/-- Radial integrability: every element of the jet gauge algebra vanishing at the base
  point is the radial Maurer–Cartan component of a pure jet, assembled factor by factor
  from `exists_eulerTransport_of_radial`. -/
theorem exists_radial_eq (ρ : JetGaugeAlgebra) (hρ : eval ρ = 0) :
    ∃ U : localGaugeData.truncationKer 0, localGaugeData.radial U.1 = ρ := by
  classical
  have h₃ : ∀ i j, constantCoeff (ρ.toSU3Matrix i j) = 0 := fun i j => by
    rw [← eval_toSU3Matrix_apply, hρ]
    simp
  have h₂ : ∀ i j, constantCoeff (ρ.toSU2Matrix i j) = 0 := fun i j => by
    rw [← eval_toSU2Matrix_apply, hρ]
    simp
  have h₁ : constantCoeff ρ.toU1Value = 0 := by
    rw [← eval_toU1Value_eq, hρ]
    simp
  obtain ⟨V₃, hV₃0, hV₃u, hdet₃, hrad₃⟩ :=
    exists_eulerTransport_of_radial ρ.toSU3Matrix h₃ ρ.1.2.1
  obtain ⟨V₂, hV₂0, hV₂u, hdet₂, hrad₂⟩ :=
    exists_eulerTransport_of_radial ρ.toSU2Matrix h₂ ρ.2.1.2.1
  obtain ⟨V₁, hV₁0, hV₁u, _, hrad₁⟩ :=
    exists_eulerTransport_of_radial (κ := Fin 1) (Matrix.of fun _ _ => ρ.toU1Value)
      (fun _ _ => h₁) (Matrix.ext fun _ _ => ρ.2.2.2)
  have hd₃ : V₃.det = 1 := hdet₃ (show ρ.toSU3Matrix.trace = 0 from ρ.1.2.2) jacobi_fin3
  have hd₂ : V₂.det = 1 := hdet₂ (show ρ.toSU2Matrix.trace = 0 from ρ.2.1.2.2) jacobi_fin2
  have hu1 : V₁ 0 0 * star (V₁ 0 0) = 1 := by
    simpa [Matrix.mul_apply] using congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hV₁u
  have hu0 : constantCoeff (V₁ 0 0) = 1 := by
    simpa using congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hV₁0
  have hrad₁' : ∑ μ, (X μ : JetRing) •
      (Complex.I • (pderiv ℂ μ (V₁ 0 0) * star (V₁ 0 0))) = ρ.toU1Value := by
    have h := congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hrad₁
    simpa [Matrix.sum_apply, Matrix.mul_apply] using h
  refine ⟨⟨(⟨V₃, Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨Matrix.mem_unitaryGroup_iff.mpr hV₃u, hd₃⟩⟩,
      ⟨V₂, Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨Matrix.mem_unitaryGroup_iff.mpr hV₂u, hd₂⟩⟩,
      ⟨V₁ 0 0, Unitary.mem_iff.mpr ⟨by rw [mul_comm]; exact hu1, hu1⟩⟩),
    localGaugeData.mem_truncationKer_zero_iff.mpr
      (Prod.ext (Subtype.ext hV₃0) (Prod.ext (Subtype.ext hV₂0) (Subtype.ext hu0)))⟩, ?_⟩
  refine ext_of_matrix ?_ ?_ ?_
  · rw [radial_toSU3Matrix]
    exact hrad₃
  · rw [radial_toSU2Matrix]
    exact hrad₂
  · rw [radial_toU1Value]
    exact hrad₁'

/-- The Standard Model package is free: Taylor completeness is `eval_iteratedDeriv_taylorJet`
  and radial integrability is `exists_radial_eq`. The symmetrized Maurer–Cartan data are
  therefore free coordinates on its pure jets, by the general
  `LocalGaugeData.symmetrizedMaurerCartanCoeff_bijective`. -/
instance instFreeLocalGaugeData : localGaugeData.Free where
  toFaithful := inferInstance
  exists_evalLie_iteratedDeriv_eq c := ⟨taylorJet c, eval_iteratedDeriv_taylorJet c⟩
  exists_radial_eq ρ hρ := exists_radial_eq ρ hρ

end StandardModel
