/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Truncation
public import Physlib.Particles.StandardModel.GaugeAlgebra.JetGaugeAlgebra
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Particles.LagrangianTheory.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Physlib.Mathematics.MvPolynomialTranslation
public import Mathlib.Algebra.MvPolynomial.Derivation
/-!
# The Maurer–Cartan forms and the truncation kernels
-/

@[expose] public section
namespace StandardModel
open MvPowerSeries JetGaugeAlgebra JetRing
/-- Projecting onto the zeroth truncation kernel does not change the Maurer–Cartan
  form: by the cocycle law, right-multiplication by a constant gauge transformation
  drops out. -/
lemma maurerCartanForm_truncationProjZero (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanForm (JetGaugeGroupI.truncationProjZero U : JetGaugeGroupI) μ =
      maurerCartanForm U μ := by
  rw [show (JetGaugeGroupI.truncationProjZero U : JetGaugeGroupI) =
      U * (JetGaugeGroupI.ofConstant U.eval)⁻¹ from rfl,
    ← map_inv, maurerCartanForm_cocycle, maurerCartanForm_ofConstant]
  simp

/-- A pure jet is determined by its Maurer–Cartan form: on the kernel of the zeroth
  truncation, `U ↦ ω(U)` is injective. By the cocycle and inverse laws
  `ω(V⁻¹ U) = Ad_{V⁻¹}(ω(U) − ω(V)) = 0`, so `V⁻¹ U` is a constant jet, and purity
  of `U` and `V` forces that constant to be the identity. -/
lemma maurerCartanForm_injOn_truncationKer_zero {U V : JetGaugeGroupI}
    (hU : U ∈ JetGaugeGroupI.truncationKer 0) (hV : V ∈ JetGaugeGroupI.truncationKer 0)
    (h : maurerCartanForm U = maurerCartanForm V) : U = V := by
  have h1 : maurerCartanForm (V⁻¹ * U) = 0 := by
    funext μ
    rw [maurerCartanForm_cocycle, maurerCartanForm_inv, congrFun h μ]
    simp
  obtain ⟨c, hc⟩ := (maurerCartanForm_eq_zero_iff_ofConstant _).mp h1
  have hc1 : c = 1 := by
    have he := congrArg JetGaugeGroupI.eval hc
    rw [map_mul, map_inv, JetGaugeGroupI.mem_truncationKer_zero_iff.mp hU,
      JetGaugeGroupI.mem_truncationKer_zero_iff.mp hV, JetGaugeGroupI.eval_ofConstant] at he
    simpa using he.symm
  rw [hc1, map_one] at hc
  exact (inv_mul_eq_one.mp hc).symm

lemma exists_maurerCartanForm_eq_of_structure
    (ω : (Fin 1 ⊕ Fin 3) → JetGaugeAlgebra)
    (hω : ∀ μ ν, deriv μ (ω ν) - deriv ν (ω μ) + ⁅ω μ, ω ν⁆ = 0) :
    ∃ U ∈ JetGaugeGroupI.truncationKer 0, maurerCartanForm U = ω := by
  obtain ⟨U, hU0, hU⟩ := exists_deriv_eq_of_maurerCartanForm_structure ω hω
  refine ⟨U, JetGaugeGroupI.mem_truncationKer_zero_iff.mpr hU0, funext fun μ => ?_⟩
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

## Freeness: injectivity of the symmetrized Maurer–Cartan data

-/

/-- The symmetrized Maurer–Cartan data of a pure jet: the base-point values of its
  symmetrized Maurer–Cartan forms, indexed by nonempty multisets of directions.
  Total symmetry is automatic from the multiset indexing. -/
noncomputable def symmetrizedMaurerCartanCoeff (U : JetGaugeGroupI.truncationKer 0)
    (r : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0}) : GaugeAlgebra :=
  eval (symmetrizedMaurerCartanForm U.1 r.1)

/-- Freeness, injectivity half: a pure jet is determined by its symmetrized
  Maurer–Cartan data. The symmetrized data determine all Maurer–Cartan Taylor data
  by strong induction with `eval_iteratedDeriv_maurerCartanForm_eq_of_symmetrized_eq`,
  hence the Maurer–Cartan form itself by Taylor determinacy, hence the pure jet by
  `maurerCartanForm_injOn_truncationKer_zero`. -/
lemma symmetrizedMaurerCartanCoeff_injective : Function.Injective symmetrizedMaurerCartanCoeff := by
  intro U V h
  -- the hypothesis extends to all multisets, the empty one trivially
  have hsym : ∀ r, eval (symmetrizedMaurerCartanForm U.1 r) =
      eval (symmetrizedMaurerCartanForm V.1 r) := by
    intro r
    by_cases hr : r = 0
    · subst hr
      simp
    · exact congrFun h ⟨r, hr⟩
  -- all Maurer–Cartan Taylor data agree, by strong induction on the number of directions
  have hall : ∀ (n : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card = n →
      eval (iteratedDeriv s (maurerCartanForm U.1 μ)) =
        eval (iteratedDeriv s (maurerCartanForm V.1 μ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro s μ hs
        exact eval_iteratedDeriv_maurerCartanForm_eq_of_symmetrized_eq U.1 V.1 n hsym
          (fun p ν hp => ih p.card hp p ν rfl) s μ hs
  -- hence the Maurer–Cartan forms agree, by Taylor determinacy
  have hmc : maurerCartanForm U.1 = maurerCartanForm V.1 := by
    funext μ
    exact ext_of_eval_iteratedDeriv fun s => hall s.card s μ rfl
  exact Subtype.ext (maurerCartanForm_injOn_truncationKer_zero U.2 V.2 hmc)

/-!

## The symmetrized data through the radial Maurer–Cartan component

-/

lemma symmetrizedMaurerCartanCoeff_apply (U : JetGaugeGroupI.truncationKer 0)
    (x : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0}) :
    symmetrizedMaurerCartanCoeff U x = eval (symmetrizedMaurerCartanForm U.1 x.1) := rfl

lemma symmetrizedMaurerCartanCoeff_toSU3_eq (U : JetGaugeGroupI.truncationKer 0)
    (P : Matrix (Fin 3) (Fin 3) JetRing)
    (hrad : ∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU3Matrix = P)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0) (i j : Fin 3) :
    (symmetrizedMaurerCartanCoeff U ⟨r, hr⟩).toSU3Matrix i j =
      (1/(Multiset.card r : ℝ)) • (((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) *
        coeff (Multiset.toFinsupp r) (P i j)) := by
  have hentry : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU3Matrix i j)) =
      P i j := by
    have h1 : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU3Matrix i j)) =
        (∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU3Matrix) i j := by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun μ _ => rfl
    rw [h1, hrad]
  rw [symmetrizedMaurerCartanCoeff_apply, eval_symmetrizedMaurerCartanForm_toSU3_apply,
    sum_constantCoeff_foldl_erase, hentry]

lemma symmetrizedMaurerCartanCoeff_toSU2_eq (U : JetGaugeGroupI.truncationKer 0)
    (P : Matrix (Fin 2) (Fin 2) JetRing)
    (hrad : ∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU2Matrix = P)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0) (i j : Fin 2) :
    (symmetrizedMaurerCartanCoeff U ⟨r, hr⟩).toSU2Matrix i j =
      (1/(Multiset.card r : ℝ)) • (((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) *
        coeff (Multiset.toFinsupp r) (P i j)) := by
  have hentry : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU2Matrix i j)) =
      P i j := by
    have h1 : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU2Matrix i j)) =
        (∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU2Matrix) i j := by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun μ _ => rfl
    rw [h1, hrad]
  rw [symmetrizedMaurerCartanCoeff_apply, eval_symmetrizedMaurerCartanForm_toSU2_apply,
    sum_constantCoeff_foldl_erase, hentry]

lemma symmetrizedMaurerCartanCoeff_toU1_eq (U : JetGaugeGroupI.truncationKer 0)
    (p : JetRing)
    (hrad : ∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toU1Value = p)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0) :
    (symmetrizedMaurerCartanCoeff U ⟨r, hr⟩).toU1Value =
      (1/(Multiset.card r : ℝ)) • (((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) *
        coeff (Multiset.toFinsupp r) p) := by
  rw [symmetrizedMaurerCartanCoeff_apply, eval_symmetrizedMaurerCartanForm_toU1Value,
    sum_constantCoeff_foldl_erase, hrad]

/-!

## Freeness: surjectivity of the symmetrized Maurer–Cartan data

-/

/-- Freeness, surjectivity half: every prescribed family of symmetrized Maurer–Cartan
  data is realized by a pure jet. The radial component `ρ := ∑ μ x_μ ω_μ` of the
  Maurer–Cartan form carries exactly the symmetrized data, so it suffices to solve the
  radial (Euler) system `E U = −i ρ U`, `U(0) = 1` for a prescribed `ρ`; this is done
  factorwise by `exists_matrix_eulerTransport`, with unitarity and determinant one from
  the Euler vanishing principle. -/
lemma symmetrizedMaurerCartanCoeff_surjective :
    Function.Surjective symmetrizedMaurerCartanCoeff := by
  classical
  intro c
  -- the factorwise construction: a unitary Euler transport with prescribed radial data
  have hcore : ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
      (E : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0} → Matrix κ κ ℂ),
      (∀ x, star (E x) = E x) →
      ∃ V P : Matrix κ κ JetRing,
        (constantCoeff : JetRing →+* ℂ).mapMatrix V = 1 ∧
        V * star V = 1 ∧
        (∑ μ, (X μ : JetRing) • (Complex.I • (V.map (pderiv ℂ μ) * star V)) = P) ∧
        ((∀ x, (E x).trace = 0) →
          (∀ (M : Matrix κ κ JetRing) (μ : Fin 1 ⊕ Fin 3),
            pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace) → V.det = 1) ∧
        (∀ (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0) (i j : κ),
          coeff (Multiset.toFinsupp r) (P i j) =
            (((Multiset.card r : ℕ) : ℂ) /
              ((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ)) * E ⟨r, hr⟩ i j) := by
    intro κ _ _ E hEstar
    set P : Matrix κ κ JetRing := Matrix.of fun i j =>
      show JetRing from fun m =>
        if h : Finsupp.toMultiset m = 0 then 0
        else (((Finsupp.degree m : ℕ) : ℂ) / ((∏ ν, Nat.factorial (m ν) : ℕ) : ℂ)) *
          E ⟨Finsupp.toMultiset m, h⟩ i j with hP
    have hPcoeff : ∀ (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) (i j : κ), coeff m (P i j) =
        if h : Finsupp.toMultiset m = 0 then 0
        else (((Finsupp.degree m : ℕ) : ℂ) / ((∏ ν, Nat.factorial (m ν) : ℕ) : ℂ)) *
          E ⟨Finsupp.toMultiset m, h⟩ i j := fun _ _ _ => rfl
    have hP0 : ∀ i j, constantCoeff (P i j) = 0 := fun i j => by
      rw [← coeff_zero_eq_constantCoeff, hPcoeff, dif_pos (by simp)]
    have hPstar : star P = P := by
      ext i j : 1
      ext m
      rw [Matrix.star_apply, JetRing.coeff_star, hPcoeff, hPcoeff]
      split_ifs with h
      · simp
      · rw [star_mul', show star (E ⟨Finsupp.toMultiset m, h⟩ j i)
            = E ⟨Finsupp.toMultiset m, h⟩ i j from by
          conv_rhs => rw [← hEstar ⟨Finsupp.toMultiset m, h⟩]
          exact (Matrix.star_apply _ _ _).symm,
          star_div₀, star_natCast, star_natCast]
    have hR0 : ∀ i j, constantCoeff (((-Complex.I) • P) i j) = 0 := fun i j => by
      rw [Matrix.smul_apply, ← coeff_zero_eq_constantCoeff, map_smul,
        coeff_zero_eq_constantCoeff, hP0, smul_zero]
    have hRstar : star ((-Complex.I) • P) = -((-Complex.I) • P) := by
      rw [star_smul, hPstar]
      simp
    obtain ⟨V, hV0, hEV⟩ := exists_matrix_eulerTransport ((-Complex.I) • P) hR0
    have hVu : V * star V = 1 := eulerTransport_mul_star hRstar hR0 hV0 hEV
    refine ⟨V, P, hV0, hVu, ?_, ?_, ?_⟩
    · calc ∑ μ, (X μ : JetRing) • (Complex.I • (V.map (pderiv ℂ μ) * star V))
          = Complex.I • ((∑ μ, (X μ : JetRing) • V.map (pderiv ℂ μ)) * star V) := by
            rw [Finset.sum_mul, Finset.smul_sum]
            exact Finset.sum_congr rfl fun μ _ => by
              rw [Matrix.smul_mul, smul_comm Complex.I]
        _ = P := by
            rw [hEV, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc, hVu, mul_one,
              smul_smul]
            simp
    · intro hEtr hjac
      have hPtr : P.trace = 0 := by
        ext m
        rw [show coeff m P.trace = ∑ i, coeff m (P i i) from by
            rw [show P.trace = ∑ i, P i i from rfl, map_sum],
          map_zero, Finset.sum_congr rfl fun i _ => hPcoeff m i i]
        by_cases h : Finsupp.toMultiset m = 0
        · simp [h]
        · simp only [dif_neg h]
          rw [← Finset.mul_sum,
            show (∑ i, E ⟨Finsupp.toMultiset m, h⟩ i i) = (E ⟨Finsupp.toMultiset m, h⟩).trace
              from rfl,
            hEtr, mul_zero]
      have hRtr : ((-Complex.I) • P).trace = 0 := by
        rw [Matrix.trace_smul, hPtr, smul_zero]
      exact eulerTransport_det hjac hRtr hV0 hEV
    · intro r hr i j
      have hround : Finsupp.toMultiset (Multiset.toFinsupp r) = r := by simp
      rw [hPcoeff, dif_neg (show ¬Finsupp.toMultiset (Multiset.toFinsupp r) = 0 from by
          rw [hround]; exact hr),
        show (∏ ν, Nat.factorial ((Multiset.toFinsupp r) ν)) = ∏ ν, Nat.factorial (r.count ν)
          from Finset.prod_congr rfl fun ν _ => by rw [Multiset.toFinsupp_apply],
        degree_toFinsupp_eq_card]
      exact congrArg (fun x => (((Multiset.card r : ℕ) : ℂ) /
        ((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ)) * E x i j) (Subtype.ext hround)
  -- apply the construction on each factor
  obtain ⟨V₃, P₃, hV₃0, hV₃u, hrad₃, hdet₃, hcoeff₃⟩ :=
    hcore (Fin 3) (fun x => (c x).toSU3Matrix)
      (fun x => show star (c x).toSU3Matrix = (c x).toSU3Matrix from (c x).1.2.1)
  obtain ⟨V₂, P₂, hV₂0, hV₂u, hrad₂, hdet₂, hcoeff₂⟩ :=
    hcore (Fin 2) (fun x => (c x).toSU2Matrix)
      (fun x => show star (c x).toSU2Matrix = (c x).toSU2Matrix from (c x).2.1.2.1)
  obtain ⟨V₁, P₁, hV₁0, hV₁u, hrad₁, _, hcoeff₁⟩ :=
    hcore (Fin 1) (fun x => Matrix.of fun _ _ => (c x).toU1Value)
      (fun x => Matrix.ext fun _ _ => (c x).2.2.2)
  have hd₃ : V₃.det = 1 := hdet₃
    (fun x => show ((c x).toSU3Matrix).trace = 0 from (c x).1.2.2) jacobi_fin3
  have hd₂ : V₂.det = 1 := hdet₂
    (fun x => show ((c x).toSU2Matrix).trace = 0 from (c x).2.1.2.2) jacobi_fin2
  have hu1 : V₁ 0 0 * star (V₁ 0 0) = 1 := by
    simpa [Matrix.mul_apply] using congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hV₁u
  have hu0 : constantCoeff (V₁ 0 0) = 1 := by
    simpa using congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hV₁0
  -- the scalar radial identity for the `U(1)` factor
  have hrad₁' : ∑ μ, (X μ : JetRing) •
      (Complex.I • (pderiv ℂ μ (V₁ 0 0) * star (V₁ 0 0))) = P₁ 0 0 := by
    have h := congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hrad₁
    simpa [Matrix.sum_apply, Matrix.mul_apply] using h
  refine ⟨⟨(⟨V₃, Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨Matrix.mem_unitaryGroup_iff.mpr hV₃u, hd₃⟩⟩,
      ⟨V₂, Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨Matrix.mem_unitaryGroup_iff.mpr hV₂u, hd₂⟩⟩,
      ⟨V₁ 0 0, Unitary.mem_iff.mpr ⟨by rw [mul_comm]; exact hu1, hu1⟩⟩),
    JetGaugeGroupI.mem_truncationKer_zero_iff.mpr
      (Prod.ext (Subtype.ext hV₃0) (Prod.ext (Subtype.ext hV₂0) (Subtype.ext hu0)))⟩, ?_⟩
  funext x
  obtain ⟨r, hr⟩ := x
  have hcard : ((Multiset.card r : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun hc => hr (Multiset.card_eq_zero.mp hc)
  have hfacne : ((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.factorial_ne_zero _)
  have hfacne' : (∏ ν, ((Nat.factorial (r.count ν) : ℕ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  refine GaugeAlgebra.ext_of_matrix ?_ ?_ ?_
  · ext i j : 1
    rw [symmetrizedMaurerCartanCoeff_toSU3_eq _ P₃
        (by simp only [maurerCartanForm_toSU3Matrix]; exact hrad₃) r hr i j,
      hcoeff₃ r hr i j, Complex.real_smul]
    push_cast
    field_simp
  · ext i j : 1
    rw [symmetrizedMaurerCartanCoeff_toSU2_eq _ P₂
        (by simp only [maurerCartanForm_toSU2Matrix]; exact hrad₂) r hr i j,
      hcoeff₂ r hr i j, Complex.real_smul]
    push_cast
    field_simp
  · rw [symmetrizedMaurerCartanCoeff_toU1_eq _ (P₁ 0 0)
        (by simp only [maurerCartanForm_toU1Value]; exact hrad₁') r hr,
      hcoeff₁ r hr 0 0, Complex.real_smul, Matrix.of_apply]
    push_cast
    field_simp


/-- **Maurer–Cartan triangularity**: a pure jet whose symmetrized Maurer–Cartan
  coefficients vanish up to order `n` lies in the `n`-th truncation kernel. -/
lemma mem_truncationKer_of_symmetrizedMaurerCartanCoeff_eq_zero
    (U : JetGaugeGroupI.truncationKer 0) (n : ℕ)
    (h : ∀ (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0), r.card ≤ n →
      symmetrizedMaurerCartanCoeff U ⟨r, hr⟩ = 0) :
    U.1 ∈ JetGaugeGroupI.truncationKer n := by
  classical
  -- Step 1: the base-point Maurer–Cartan Taylor data vanish below order `n`, by
  -- strong induction with the symmetrization defect formula.
  have hall : ∀ (k : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3),
      s.card = k → k < n → eval (iteratedDeriv s (maurerCartanForm U.1 μ)) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s μ hs hk
      rw [iteratedDeriv_maurerCartanForm_eq_symmetrized_add U.1 s μ, map_add, map_smul]
      have h1 : eval (symmetrizedMaurerCartanForm U.1 (μ ::ₘ s)) = 0 := by
        have hle : (μ ::ₘ s).card ≤ n := by rw [Multiset.card_cons, hs]; omega
        have h2 := h (μ ::ₘ s) (Multiset.cons_ne_zero) hle
        rwa [symmetrizedMaurerCartanCoeff_apply] at h2
      have h2 : eval ((s.map fun ν => iteratedDeriv (s.erase ν)
          ⁅maurerCartanForm U.1 μ, maurerCartanForm U.1 ν⁆).sum) = 0 := by
        rw [map_multiset_sum, Multiset.map_map]
        refine Multiset.sum_eq_zero fun x hx => ?_
        obtain ⟨ν, hν, rfl⟩ := Multiset.mem_map.mp hx
        have hzero : ∀ (ρ : Fin 1 ⊕ Fin 3) (p : Multiset (Fin 1 ⊕ Fin 3)),
            p ≤ s.erase ν → eval (iteratedDeriv p (maurerCartanForm U.1 ρ)) =
              eval (iteratedDeriv p (0 : JetGaugeAlgebra)) := by
          intro ρ p hp
          have hcard : p.card < k := by
            have h3 := Multiset.card_le_card hp
            have h4 := Multiset.card_erase_add_one hν
            omega
          rw [ih p.card hcard p ρ rfl (hcard.trans hk), map_zero, map_zero]
        simp only [Function.comp_apply]
        rw [eval_iteratedDeriv_bracket_congr (s.erase ν) _ _ 0 0 (hzero μ) (hzero ν)]
        simp
      rw [h1, h2]
      simp
  -- Step 2: the Taylor coefficients of the Maurer–Cartan form components vanish in
  -- all degrees below `n`.
  have hfac : ∀ s : Multiset (Fin 1 ⊕ Fin 3),
      ((∏ ν, Nat.factorial (s.count ν) : ℕ) : ℂ) ≠ 0 := fun s =>
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.factorial_ne_zero _)
  have hround : ∀ m : (Fin 1 ⊕ Fin 3) →₀ ℕ,
      Multiset.toFinsupp (Finsupp.toMultiset m) = m := fun m => by simp
  have hcardm : ∀ m : (Fin 1 ⊕ Fin 3) →₀ ℕ,
      (Finsupp.toMultiset m).card = Finsupp.degree m := fun m => by
    rw [← degree_toFinsupp_eq_card, hround]
  have hω3 : ∀ (ρ : Fin 1 ⊕ Fin 3) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree m < n →
      ∀ i j, coeff m ((maurerCartanForm U.1 ρ).toSU3Matrix i j) = 0 := by
    intro ρ m hm i j
    have h0 := hall (Finsupp.toMultiset m).card (Finsupp.toMultiset m) ρ rfl
      (by rw [hcardm m]; exact hm)
    have h1 := congrArg (fun a => GaugeAlgebra.toSU3Matrix a i j) h0
    simp only [GaugeAlgebra.zero_toSU3Matrix, Matrix.zero_apply] at h1
    rw [eval_toSU3Matrix_apply, iteratedDeriv_toSU3Matrix, Matrix.map_apply,
      constantCoeff_foldl_pderiv, hround] at h1
    exact (mul_eq_zero.mp h1).resolve_left (hfac _)
  have hω2 : ∀ (ρ : Fin 1 ⊕ Fin 3) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree m < n →
      ∀ i j, coeff m ((maurerCartanForm U.1 ρ).toSU2Matrix i j) = 0 := by
    intro ρ m hm i j
    have h0 := hall (Finsupp.toMultiset m).card (Finsupp.toMultiset m) ρ rfl
      (by rw [hcardm m]; exact hm)
    have h1 := congrArg (fun a => GaugeAlgebra.toSU2Matrix a i j) h0
    simp only [GaugeAlgebra.zero_toSU2Matrix, Matrix.zero_apply] at h1
    rw [eval_toSU2Matrix_apply, iteratedDeriv_toSU2Matrix, Matrix.map_apply,
      constantCoeff_foldl_pderiv, hround] at h1
    exact (mul_eq_zero.mp h1).resolve_left (hfac _)
  have hω1 : ∀ (ρ : Fin 1 ⊕ Fin 3) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree m < n →
      coeff m ((maurerCartanForm U.1 ρ).toU1Value) = 0 := by
    intro ρ m hm
    have h0 := hall (Finsupp.toMultiset m).card (Finsupp.toMultiset m) ρ rfl
      (by rw [hcardm m]; exact hm)
    have h1 := congrArg GaugeAlgebra.toU1Value h0
    simp only [GaugeAlgebra.zero_toU1Value] at h1
    rw [eval_toU1Value_eq, iteratedDeriv_toU1Value, constantCoeff_foldl_pderiv,
      hround] at h1
    exact (mul_eq_zero.mp h1).resolve_left (hfac _)
  -- Step 3: the Euler operator toolkit. A product with a factor whose coefficients
  -- vanish below degree `n` has vanishing coefficients below degree `n` ...
  have hmul : ∀ (w v : JetRing),
      (∀ q : (Fin 1 ⊕ Fin 3) →₀ ℕ, Finsupp.degree q < n → coeff q w = 0) →
      ∀ q : (Fin 1 ⊕ Fin 3) →₀ ℕ, Finsupp.degree q < n → coeff q (w * v) = 0 := by
    intro w v hw q hq
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpq : p.1 + p.2 = q := Finset.mem_antidiagonal.mp hp
    have hdeg : Finsupp.degree p.1 ≤ Finsupp.degree q := by
      rw [← hpq, map_add]
      exact Nat.le_add_right _ _
    rw [hw p.1 (lt_of_le_of_lt hdeg hq), zero_mul]
  -- ... and a jet whose derivatives have vanishing coefficients below degree `n` has
  -- vanishing coefficients in all nonzero degrees up to `n`, by the Euler identity.
  have hvanish : ∀ f : JetRing,
      (∀ (ρ : Fin 1 ⊕ Fin 3) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree q < n →
        coeff q (pderiv ℂ ρ f) = 0) →
      ∀ p : (Fin 1 ⊕ Fin 3) →₀ ℕ, p ≠ 0 → Finsupp.degree p ≤ n → coeff p f = 0 := by
    intro f hf p hp hpn
    have h1 := JetRing.coeff_sum_X_smul_pderiv f p
    have h2 : coeff p (∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ f) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun ρ _ => ?_
      rw [JetRing.coeff_X_smul]
      split_ifs with hle
      · refine hf ρ _ ?_
        have hd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        rw [map_add, Finsupp.degree_single] at hd
        omega
      · rfl
    rw [h2] at h1
    have hne : ((Finsupp.degree p : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr fun hc => hp ((Finsupp.degree_eq_zero_iff p).mp hc)
    exact (mul_eq_zero.mp h1.symm).resolve_left hne
  -- the radial derivative relation `∂_μ U = (−i ω_μ) U` on each factor
  have hstar3 : star U.1.1.1 * U.1.1.1 = 1 := by
    have h1 := (Matrix.mem_specialUnitaryGroup_iff.mp U.1.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff'] at h1
  have hstar2 : star U.1.2.1.1 * U.1.2.1.1 = 1 := by
    have h1 := (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff'] at h1
  have hstar1 : star U.1.2.2.1 * U.1.2.2.1 = 1 := (Unitary.mem_iff.mp U.1.2.2.2).1
  have hd3 : ∀ ρ, U.1.1.1.map (pderiv ℂ ρ) =
      ((-Complex.I) • (maurerCartanForm U.1 ρ).toSU3Matrix) * U.1.1.1 := by
    intro ρ
    rw [maurerCartanForm_toSU3Matrix, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, mul_assoc, hstar3, mul_one]
  have hd2 : ∀ ρ, U.1.2.1.1.map (pderiv ℂ ρ) =
      ((-Complex.I) • (maurerCartanForm U.1 ρ).toSU2Matrix) * U.1.2.1.1 := by
    intro ρ
    rw [maurerCartanForm_toSU2Matrix, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, mul_assoc, hstar2, mul_one]
  have hd1 : ∀ ρ, pderiv ℂ ρ U.1.2.2.1 =
      ((-Complex.I) • (maurerCartanForm U.1 ρ).toU1Value) * U.1.2.2.1 := by
    intro ρ
    rw [maurerCartanForm_toU1Value, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, mul_assoc, hstar1, mul_one]
  -- coefficient vanishing for the entries of `U` in nonzero degree up to `n`
  have hU3 : ∀ (i j : Fin 3) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ), p ≠ 0 →
      Finsupp.degree p ≤ n → coeff p (U.1.1.1 i j) = 0 := by
    intro i j p hp hpn
    refine hvanish _ (fun ρ q hq => ?_) p hp hpn
    have h1 : pderiv ℂ ρ (U.1.1.1 i j) =
        (((-Complex.I) • (maurerCartanForm U.1 ρ).toSU3Matrix) * U.1.1.1) i j := by
      rw [← hd3 ρ, Matrix.map_apply]
    rw [h1, Matrix.mul_apply, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    refine hmul _ _ (fun q' hq' => ?_) q hq
    rw [Matrix.smul_apply, map_smul, hω3 ρ q' hq' i k, smul_zero]
  have hU2 : ∀ (i j : Fin 2) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ), p ≠ 0 →
      Finsupp.degree p ≤ n → coeff p (U.1.2.1.1 i j) = 0 := by
    intro i j p hp hpn
    refine hvanish _ (fun ρ q hq => ?_) p hp hpn
    have h1 : pderiv ℂ ρ (U.1.2.1.1 i j) =
        (((-Complex.I) • (maurerCartanForm U.1 ρ).toSU2Matrix) * U.1.2.1.1) i j := by
      rw [← hd2 ρ, Matrix.map_apply]
    rw [h1, Matrix.mul_apply, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    refine hmul _ _ (fun q' hq' => ?_) q hq
    rw [Matrix.smul_apply, map_smul, hω2 ρ q' hq' i k, smul_zero]
  have hU1 : ∀ p : (Fin 1 ⊕ Fin 3) →₀ ℕ, p ≠ 0 → Finsupp.degree p ≤ n →
      coeff p U.1.2.2.1 = 0 := by
    intro p hp hpn
    refine hvanish _ (fun ρ q hq => ?_) p hp hpn
    rw [hd1 ρ]
    refine hmul _ _ (fun q' hq' => ?_) q hq
    rw [map_smul, hω1 ρ q' hq', smul_zero]
  -- assemble: agreement with the identity jet in all degrees up to `n`
  have heval : U.1.eval = 1 := JetGaugeGroupI.eval_coe_of_mem_truncationKer_zero U
  rw [JetGaugeGroupI.mem_truncationKer_iff]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show U.1.1.1.map (JetRing.truncation n) =
      (1 : Matrix (Fin 3) (Fin 3) JetRing).map (JetRing.truncation n)
    ext i j : 1
    simp only [Matrix.map_apply]
    ext m
    by_cases hm : Finsupp.degree m ≤ n
    · rw [JetRing.coeff_truncation_of_le hm, JetRing.coeff_truncation_of_le hm]
      rcases eq_or_ne m 0 with rfl | hm0
      · have h3 := congrArg (fun p => (p.1 : Matrix (Fin 3) (Fin 3) ℂ) i j) heval
        simpa [JetGaugeGroupI.eval, JetGaugeGroupI.evalSU, RingHom.mapMatrix_apply,
          Matrix.map_apply, Matrix.one_apply, apply_ite constantCoeff,
          coeff_zero_eq_constantCoeff] using h3
      · rw [hU3 i j m hm0 hm]
        rcases eq_or_ne i j with rfl | hij
        · rw [Matrix.one_apply_eq, coeff_one, if_neg hm0]
        · rw [Matrix.one_apply_ne hij, map_zero]
    · rw [JetRing.coeff_truncation_of_gt (not_le.mp hm),
        JetRing.coeff_truncation_of_gt (not_le.mp hm)]
  · show U.1.2.1.1.map (JetRing.truncation n) =
      (1 : Matrix (Fin 2) (Fin 2) JetRing).map (JetRing.truncation n)
    ext i j : 1
    simp only [Matrix.map_apply]
    ext m
    by_cases hm : Finsupp.degree m ≤ n
    · rw [JetRing.coeff_truncation_of_le hm, JetRing.coeff_truncation_of_le hm]
      rcases eq_or_ne m 0 with rfl | hm0
      · have h3 := congrArg (fun p => (p.2.1 : Matrix (Fin 2) (Fin 2) ℂ) i j) heval
        simpa [JetGaugeGroupI.eval, JetGaugeGroupI.evalSU, RingHom.mapMatrix_apply,
          Matrix.map_apply, Matrix.one_apply, apply_ite constantCoeff,
          coeff_zero_eq_constantCoeff] using h3
      · rw [hU2 i j m hm0 hm]
        rcases eq_or_ne i j with rfl | hij
        · rw [Matrix.one_apply_eq, coeff_one, if_neg hm0]
        · rw [Matrix.one_apply_ne hij, map_zero]
    · rw [JetRing.coeff_truncation_of_gt (not_le.mp hm),
        JetRing.coeff_truncation_of_gt (not_le.mp hm)]
  · show JetRing.truncation n U.1.2.2.1 = JetRing.truncation n (1 : JetRing)
    ext m
    by_cases hm : Finsupp.degree m ≤ n
    · rw [JetRing.coeff_truncation_of_le hm, JetRing.coeff_truncation_of_le hm]
      rcases eq_or_ne m 0 with rfl | hm0
      · have h3 := congrArg (fun p => (p.2.2 : ℂ)) heval
        simpa [JetGaugeGroupI.eval, JetGaugeGroupI.evalU1,
          coeff_zero_eq_constantCoeff] using h3
      · rw [hU1 m hm0 hm, coeff_one, if_neg hm0]
    · rw [JetRing.coeff_truncation_of_gt (not_le.mp hm),
        JetRing.coeff_truncation_of_gt (not_le.mp hm)]

end StandardModel
