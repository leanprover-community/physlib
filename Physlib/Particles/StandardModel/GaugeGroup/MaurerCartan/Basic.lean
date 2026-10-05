/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.JetGaugeGroup.Basic
public import Physlib.Particles.StandardModel.GaugeAlgebra.JetGaugeAlgebra
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.Modules.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeDerivAlgebra
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Physlib.Mathematics.MvPolynomialTranslation
public import Mathlib.Algebra.MvPolynomial.Derivation
/-!
# The Maurer–Cartan forms of the jet gauge group

The Maurer-Cartan form is a map
`ω : JetGaugeGroupI → (Fin 1 ⊕ Fin 3) → JetGaugeAlgebra`
defined as `ω_μ(U) := i (∂_μ U) U†`.

We will use `ω^a_ν` to denote the `a`-th component of the Maurer–Cartan form in the
basis of the jet Lie algebra, and `f^a_{b c}` to denote the structure constants of the
jet Lie algebra in that basis.

It satisfies the following properties, proved here from the matrix definition:
- *Cocycle law*: `ω_μ(UV) = ω_μ(U) + U ω_μ(V) U†`
- *Value on the identity*: `ω_μ(1) = 0`
- *Value on constant gauge transformations*: `ω_μ(U₀) = 0`
- *Structural equation*: `∂_μ ω^a_ν(U) − ∂_ν ω^a_μ(U) = ∑_{b c} f^a_{b c} · ω^b_μ(U) · ω^c_ν(U)`

These four are exactly the Maurer–Cartan laws of a local gauge data package. What follows
from them alone — the value on inverses, the symmetrized Maurer–Cartan form and the
determination of `ω` by its symmetrized base-point data — is proved once, for any package,
in `Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MaurerCartan`, and read back at
`StandardModel.localGaugeData` in
`Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData`. What remains here is what the
matrix definition itself gives: the vanishing of `ω` exactly on constant jets.

-/

@[expose] public section
namespace StandardModel
open MvPowerSeries JetGaugeAlgebra

/-!

## The Maurer–Cartan form of the jet gauge group

-/

/-- The Maurer–Cartan form `ω_μ(U) := i (∂_μ U) U⁻¹` of the jet gauge group, valued
  in the jet gauge algebra. -/
noncomputable def maurerCartanForm (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) : JetGaugeAlgebra :=
  JetGaugeAlgebra.ofMatrixProd (Complex.I • (JetGaugeGroupI.deriv μ U * (U⁻¹).toVal))
    ⟨JetGaugeGroupI.star_deriv_mul_inv_toVal_SU3 μ U,
      JetGaugeGroupI.deriv_mul_inv_toVal_SU3_traceless μ U⟩
    ⟨JetGaugeGroupI.star_deriv_mul_inv_toVal_SU2 μ U,
      JetGaugeGroupI.deriv_mul_inv_toVal_SU2_traceless μ U⟩
    (JetGaugeGroupI.star_deriv_mul_inv_toVal_U1 μ U)

@[simp]
lemma maurerCartanForm_toSU3Matrix (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (maurerCartanForm U μ).toSU3Matrix =
      Complex.I • (U.1.1.map (pderiv μ) * star U.1.1) := rfl

@[simp]
lemma maurerCartanForm_toSU2Matrix (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (maurerCartanForm U μ).toSU2Matrix =
      Complex.I • (U.2.1.1.map (pderiv μ) * star U.2.1.1) := rfl

@[simp]
lemma maurerCartanForm_toU1Value (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (maurerCartanForm U μ).toU1Value =
      Complex.I • (pderiv μ U.2.2.1 * star U.2.2.1) := rfl

@[simp]
lemma maurerCartanForm_one : maurerCartanForm (1 : JetGaugeGroupI) = 0 := by
  ext <;> simp [maurerCartanForm,JetGaugeGroupI.deriv_one]

lemma maurerCartanForm_ofConstant (U₀ : GaugeGroupI) :
    maurerCartanForm (JetGaugeGroupI.ofConstant U₀) = 0 := by
  ext <;> simp [maurerCartanForm,JetGaugeGroupI.deriv_ofConstant]

lemma maurerCartanForm_cocycle (U V : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanForm (U * V) μ = maurerCartanForm U μ + adjoint U (maurerCartanForm V μ) := by
  have h1 : V.toVal * (V⁻¹).toVal = 1 := by
    rw [show V.toVal * (V⁻¹).toVal = (V * V⁻¹).toVal from rfl, mul_inv_cancel]; rfl
  have key : Complex.I • (JetGaugeGroupI.deriv μ (U * V) * ((U * V)⁻¹).toVal) =
      Complex.I • (JetGaugeGroupI.deriv μ U * (U⁻¹).toVal) +
        U.toVal * (Complex.I • (JetGaugeGroupI.deriv μ V * (V⁻¹).toVal)) * (U⁻¹).toVal := by
    rw [show ((U * V)⁻¹).toVal = (V⁻¹).toVal * (U⁻¹).toVal from by rw [mul_inv_rev]; rfl,
      JetGaugeGroupI.deriv_mul, add_mul, smul_add, mul_smul_comm, smul_mul_assoc]
    congr 1
    · rw [mul_assoc (JetGaugeGroupI.deriv μ U), ← mul_assoc V.toVal, h1, one_mul]
    · simp [mul_assoc]
  refine ext_of_matrix (congrArg (fun p => p.1) key) (congrArg (fun p => p.2.1) key) ?_
  have h22 : (maurerCartanForm (U * V) μ).toU1Value =
      (maurerCartanForm U μ).toU1Value +
        U.2.2.1 * (maurerCartanForm V μ).toU1Value * star U.2.2.1 :=
    congrArg (fun p => p.2.2) key
  rw [h22, mul_comm (U.2.2.1 : SpaceTimeAlgebra) ((maurerCartanForm V μ).toU1Value), mul_assoc,
    (Unitary.mem_iff.mp U.2.2.2).2, mul_one]
  rfl

lemma deriv_zero_of_maurerCartanForm_zero (U : JetGaugeGroupI) (h : maurerCartanForm U = 0) :
    ∀ μ, U.deriv μ = 0 := by
  intro μ
  have h1 : maurerCartanForm U μ = 0 := congrFun h μ
  -- extract the underlying value triple of the vanishing algebra element
  have h2 : Complex.I • (JetGaugeGroupI.deriv μ U * (U⁻¹).toVal) = 0 :=
    Prod.ext (congrArg (fun a => a.1.1) h1)
      (Prod.ext (congrArg (fun a => a.2.1.1) h1) (congrArg (fun a => a.2.2.1) h1))
  -- cancel the scalar `i`
  have hml : (-Complex.I) * Complex.I = 1 := by simp [neg_mul, Complex.I_mul_I]
  have h3 : JetGaugeGroupI.deriv μ U * (U⁻¹).toVal = 0 := by
    have h4 := congrArg (fun X => (-Complex.I) • X) h2
    simpa [smul_smul, hml] using h4
  -- cancel `U⁻¹` on the right
  have h5 : (U⁻¹).toVal * U.toVal = 1 := by
    rw [show (U⁻¹).toVal * U.toVal = (U⁻¹ * U).toVal from rfl, inv_mul_cancel]
    rfl
  calc JetGaugeGroupI.deriv μ U
      = JetGaugeGroupI.deriv μ U * ((U⁻¹).toVal * U.toVal) := by rw [h5, mul_one]
    _ = JetGaugeGroupI.deriv μ U * (U⁻¹).toVal * U.toVal := by rw [mul_assoc]
    _ = 0 := by rw [h3, zero_mul]

lemma maurerCartanForm_eq_zero_iff_ofConstant (U : JetGaugeGroupI) :
    maurerCartanForm U = 0 ↔ ∃ c, U = JetGaugeGroupI.ofConstant c := by
  constructor
  · intro h
    -- Step 1: all first derivatives of `U` vanish.
    have hderiv := deriv_zero_of_maurerCartanForm_zero U h
    -- Step 2: a jet with vanishing first derivatives is the constant jet of its value.
    have hconst : ∀ f : SpaceTimeAlgebra, (∀ μ, pderiv μ f = 0) → f = C (constantCoeff f) := by
      intro f hf
      refine pderiv.ext (fun i => ?_) ?_
      · rw [hf i, pderiv_C]
      · rw [constantCoeff_C]
    refine ⟨U.eval, Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))⟩
    · show U.1.1 = ((JetGaugeGroupI.ofConstant U.eval).1 : Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra)
      ext i j : 1
      exact hconst (U.1.1 i j) fun μ => by
        simpa [JetGaugeGroupI.deriv, Matrix.map_apply] using
          congrArg (fun p => (p.1 : Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra) i j) (hderiv μ)
    · show U.2.1.1 =
          ((JetGaugeGroupI.ofConstant U.eval).2.1 : Matrix (Fin 2) (Fin 2) SpaceTimeAlgebra)
      ext i j : 1
      exact hconst (U.2.1.1 i j) fun μ => by
        simpa [JetGaugeGroupI.deriv, Matrix.map_apply] using
          congrArg (fun p => (p.2.1 : Matrix (Fin 2) (Fin 2) SpaceTimeAlgebra) i j) (hderiv μ)
    · show U.2.2.1 = ((JetGaugeGroupI.ofConstant U.eval).2.2 : SpaceTimeAlgebra)
      exact hconst U.2.2.1 fun μ => congrArg (fun p => (p.2.2 : SpaceTimeAlgebra)) (hderiv μ)
  · rintro ⟨c, rfl⟩
    exact maurerCartanForm_ofConstant c

/-!

## The structural equation

-/

/-- The structural (Maurer–Cartan) equation, basis-independently: the Maurer–Cartan
  form is flat,

  `∂_μ ω_ν − ∂_ν ω_μ + ⁅ω_μ, ω_ν⁆ = 0`.

  In components with respect to a basis of the jet gauge algebra this is
  `∂_μ ω^a_ν − ∂_ν ω^a_μ = ∑_{b c} f^a_{b c} · ω^b_μ · ω^c_ν`. On each matrix
  factor the second-derivative terms cancel by symmetry of mixed partials, the
  derivative of `A†` is rewritten through the differentiated unitarity relation,
  and the surviving first-order terms form the commutator; on the abelian `U(1)`
  factor the commutator is absent and only the symmetry of mixed partials
  remains. -/
lemma maurerCartanForm_structure (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    deriv μ (maurerCartanForm U ν) - deriv ν (maurerCartanForm U μ) +
      ⁅maurerCartanForm U μ, maurerCartanForm U ν⁆ = 0 := by
  -- pulling the scalar `i` out of the entrywise formal derivative
  have hmap : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : Fin 1 ⊕ Fin 3) (c : ℂ)
      (M : Matrix κ κ SpaceTimeAlgebra), (c • M).map (pderiv ρ) = c • M.map (pderiv ρ) :=
    fun _ _ _ _ _ _ => Matrix.ext fun _ _ => Derivation.map_smul _ _ _
  -- the matrix-level structural identity, generic in the size of the factor
  have key : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ SpaceTimeAlgebra),
      A * star A = 1 →
      (A.map (pderiv ν) * star A).map (pderiv μ) -
        (A.map (pderiv μ) * star A).map (pderiv ν) =
      A.map (pderiv μ) * star A * (A.map (pderiv ν) * star A) -
        A.map (pderiv ν) * star A * (A.map (pderiv μ) * star A) := by
    intro κ _ _ A hU
    have hleib : ∀ (ρ : Fin 1 ⊕ Fin 3) (M N : Matrix κ κ SpaceTimeAlgebra),
        (M * N).map (pderiv ρ) = M.map (pderiv ρ) * N + M * N.map (pderiv ρ) := by
      intro ρ M N
      ext i j : 1
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
        Derivation.leibniz, smul_eq_mul]
      exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
    -- the derivative of `A†` through differentiated unitarity
    have hq : ∀ ρ : Fin 1 ⊕ Fin 3,
        (star A).map (pderiv ρ) = -(star A * A.map (pderiv ρ) * star A) := by
      intro ρ
      have h1 : A * (star A).map (pderiv ρ) = -(A.map (pderiv ρ) * star A) :=
        eq_neg_of_add_eq_zero_right (by
          rw [← hleib ρ A (star A), hU]
          exact Matrix.ext fun i j => by
            simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ρ)])
      calc (star A).map (pderiv ρ)
          = star A * A * (star A).map (pderiv ρ) := by
            rw [mul_eq_one_comm.mp hU, one_mul]
        _ = -(star A * A.map (pderiv ρ) * star A) := by
            rw [mul_assoc, h1, mul_neg, ← mul_assoc]
    rw [hleib μ (A.map (pderiv ν)) (star A), hleib ν (A.map (pderiv μ)) (star A),
      show (A.map (pderiv ν)).map (pderiv μ) = (A.map (pderiv μ)).map (pderiv ν)
        from Matrix.ext fun _ _ => SpaceTimeAlgebra.pderiv_comm μ ν _, hq μ, hq ν]
    simp only [mul_neg, ← mul_assoc]
    abel
  -- the abelian `U(1)` identity: no commutator, pure symmetry of mixed partials
  have keyU1 : pderiv μ (pderiv ν U.2.2.1 * star U.2.2.1) =
      pderiv ν (pderiv μ U.2.2.1 * star U.2.2.1) := by
    have hu : U.2.2.1 * star U.2.2.1 = 1 := (Unitary.mem_iff.mp U.2.2.2).2
    have hstar : ∀ ρ : Fin 1 ⊕ Fin 3, pderiv ρ (star U.2.2.1) =
        -(star U.2.2.1 * pderiv ρ U.2.2.1 * star U.2.2.1) := by
      intro ρ
      have h0 : pderiv ρ (U.2.2.1 * star U.2.2.1) = 0 := by rw [hu, pderiv_one]
      rw [Derivation.leibniz] at h0
      simp only [smul_eq_mul] at h0
      linear_combination star U.2.2.1 * h0 -
        pderiv ρ (star U.2.2.1) * ((mul_comm _ _).trans hu)
    simp only [Derivation.leibniz, smul_eq_mul]
    rw [hstar μ, hstar ν, SpaceTimeAlgebra.pderiv_comm μ ν]
    ring
  refine ext_of_matrix ?_ ?_ ?_ <;>
    simp only [add_toSU3Matrix, add_toSU2Matrix, add_toU1Value, sub_toSU3Matrix,
      sub_toSU2Matrix, sub_toU1Value, deriv_toSU3Matrix, deriv_toSU2Matrix,
      deriv_toU1Value, bracket_toSU3Matrix, bracket_toSU2Matrix, bracket_toU1Value,
      maurerCartanForm_toSU3Matrix, maurerCartanForm_toSU2Matrix,
      maurerCartanForm_toU1Value, zero_toSU3Matrix, zero_toSU2Matrix, zero_toU1Value,
      hmap, smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul, Derivation.map_smul,
      add_zero]
  · rw [← smul_sub, ← smul_add, key _ U.1.1
      (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1)]
    exact smul_eq_zero_of_right _ (by abel)
  · rw [← smul_sub, ← smul_add, key _ U.2.1.1
      (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1)]
    exact smul_eq_zero_of_right _ (by abel)
  · rw [keyU1, sub_self]

/-!

## The derivative of the adjoint action

-/

/-- The constant inclusion has vanishing formal derivative: constants have no
  spacetime dependence. -/
@[simp]
lemma JetGaugeAlgebra.deriv_ofConstant (μ : Fin 1 ⊕ Fin 3) (a : GaugeAlgebra) :
    deriv μ (ofConstant a) = 0 := by
  ext <;> simp [Matrix.map_apply, pderiv_C]

/-- The formal derivative intertwines the adjoint action through the Maurer–Cartan
  form: `∂_μ (Ad_U x) = Ad_U (∂_μ x) − ⁅ω_μ(U), Ad_U x⁆`. On the matrix factors this
  is the Leibniz rule with the derivative of `U†` rewritten through the
  differentiated unitarity relation; on the abelian `u(1)` factor the adjoint action
  is trivial and the bracket is absent. -/
lemma deriv_adjointMap (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) (x : JetGaugeAlgebra) :
    deriv μ (adjointMap U x) =
      adjointMap U (deriv μ x) - ⁅maurerCartanForm U μ, adjointMap U x⁆ := by
  have hleib : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (M N : Matrix κ κ SpaceTimeAlgebra),
      (M * N).map (pderiv μ) = M.map (pderiv μ) * N + M * N.map (pderiv μ) := by
    intro κ _ _ M N
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have key : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (V X : Matrix κ κ SpaceTimeAlgebra),
      V * star V = 1 →
      (V * X * star V).map (pderiv μ) =
        V * X.map (pderiv μ) * star V -
        Complex.I • (Complex.I • (V.map (pderiv μ) * star V) * (V * X * star V) -
          (V * X * star V) * (Complex.I • (V.map (pderiv μ) * star V))) := by
    intro κ _ _ V X hV
    have hVV : star V * V = 1 := mul_eq_one_comm.mp hV
    have hq : (star V).map (pderiv μ) = -(star V * V.map (pderiv μ) * star V) := by
      have h1 : V * (star V).map (pderiv μ) = -(V.map (pderiv μ) * star V) :=
        eq_neg_of_add_eq_zero_right (by
          rw [← hleib _ V (star V), hV]
          exact Matrix.ext fun i j => by
            simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv μ)])
      calc (star V).map (pderiv μ)
          = star V * V * (star V).map (pderiv μ) := by rw [hVV, one_mul]
        _ = -(star V * V.map (pderiv μ) * star V) := by
            rw [mul_assoc, h1, mul_neg, ← mul_assoc]
    rw [hleib _ (V * X) (star V), hleib _ V X, hq]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_smul, Complex.I_mul_I,
      neg_one_smul, sub_neg_eq_add, add_mul, mul_neg, ← mul_assoc]
    rw [mul_assoc (V.map (pderiv μ)) (star V) V, hVV, mul_one]
    abel
  refine ext_of_matrix ?_ ?_ ?_
  · simpa only [deriv_toSU3Matrix, adjointMap_toSU3Matrix, sub_toSU3Matrix,
      bracket_toSU3Matrix, maurerCartanForm_toSU3Matrix] using
      key _ U.1.1 x.toSU3Matrix (Matrix.mem_unitaryGroup_iff.mp
        (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1)
  · simpa only [deriv_toSU2Matrix, adjointMap_toSU2Matrix, sub_toSU2Matrix,
      bracket_toSU2Matrix, maurerCartanForm_toSU2Matrix] using
      key _ U.2.1.1 x.toSU2Matrix (Matrix.mem_unitaryGroup_iff.mp
        (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1)
  · simp

end StandardModel
