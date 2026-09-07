/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
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
# Truncation of the Jet gauge group

-/

@[expose] public section

open MvPowerSeries

namespace StandardModel

namespace JetGaugeGroupI

/-- The `n`-th truncation of a jet of a gauge transformation: componentwise, all
  Taylor coefficients of total degree greater than `n` are set to zero.

  This is a plain function into the underlying matrix data, not a homomorphism
  into `JetGaugeGroupI`: deleting the coefficients above order `n` breaks both
  unitarity and multiplicativity at the orders between `n + 1` and `2 n` — the
  relations `U U† = 1` and `(U V)_m = ∑ U_p V_q` at those orders depend on the
  deleted coefficients. The homomorphic packaging of truncation is the quotient
  of `JetGaugeGroupI` by the normal subgroup of jets agreeing with `1` up to
  order `n`, not a self-map. -/
noncomputable def truncation (n : ℕ) (U : JetGaugeGroupI) :
    Matrix (Fin 3) (Fin 3) JetRing × Matrix (Fin 2) (Fin 2) JetRing × JetRing :=
  (U.1.1.map (JetRing.truncation n), U.2.1.1.map (JetRing.truncation n),
    JetRing.truncation n U.2.2.1)

/-- Truncation of the identity jet is the identity value triple. -/
@[simp]
lemma truncation_one (n : ℕ) : truncation n (1 : JetGaugeGroupI) = 1 :=
  Prod.ext (Matrix.map_one _ (JetRing.truncation_zero n) (JetRing.truncation_one n))
    (Prod.ext (Matrix.map_one _ (JetRing.truncation_zero n) (JetRing.truncation_one n))
      (JetRing.truncation_one n))

/-!

## The kernel of truncation

-/


/-- The subgroup of jets agreeing with the identity up to order `n`: the kernel of
  the `n`-th truncation. These form the natural descending filtration of
  `JetGaugeGroupI` whose quotients are the finite-order jet groups; the `n = 0`
  member is the pure jet gauge group. -/
noncomputable def truncationKer (n : ℕ) : Subgroup JetGaugeGroupI where
  carrier := {U | truncation n U = truncation n 1}
  one_mem' := rfl
  mul_mem' {a b} ha hb := by
    have ha3 : a.1.1.map (JetRing.truncation n) =
        (1 : Matrix (Fin 3) (Fin 3) JetRing).map (JetRing.truncation n) :=
      congrArg (fun p => p.1) ha
    have hb3 : b.1.1.map (JetRing.truncation n) =
        (1 : Matrix (Fin 3) (Fin 3) JetRing).map (JetRing.truncation n) :=
      congrArg (fun p => p.1) hb
    have ha2 : a.2.1.1.map (JetRing.truncation n) =
        (1 : Matrix (Fin 2) (Fin 2) JetRing).map (JetRing.truncation n) :=
      congrArg (fun p => p.2.1) ha
    have hb2 : b.2.1.1.map (JetRing.truncation n) =
        (1 : Matrix (Fin 2) (Fin 2) JetRing).map (JetRing.truncation n) :=
      congrArg (fun p => p.2.1) hb
    have ha1 : JetRing.truncation n a.2.2.1 = JetRing.truncation n 1 :=
      congrArg (fun p => p.2.2) ha
    have hb1 : JetRing.truncation n b.2.2.1 = JetRing.truncation n 1 :=
      congrArg (fun p => p.2.2) hb
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show (a.1.1 * b.1.1).map (JetRing.truncation n) =
        (1 : Matrix (Fin 3) (Fin 3) JetRing).map (JetRing.truncation n)
      rw [JetRing.matrix_truncation_mul_congr ha3 hb3, one_mul]
    · show (a.2.1.1 * b.2.1.1).map (JetRing.truncation n) =
        (1 : Matrix (Fin 2) (Fin 2) JetRing).map (JetRing.truncation n)
      rw [JetRing.matrix_truncation_mul_congr ha2 hb2, one_mul]
    · show JetRing.truncation n (a.2.2.1 * b.2.2.1) = JetRing.truncation n 1
      rw [JetRing.truncation_mul_congr ha1 hb1, one_mul]
  inv_mem' {a} ha := by
    have ha3 : a.1.1.map (JetRing.truncation n) =
        (1 : Matrix (Fin 3) (Fin 3) JetRing).map (JetRing.truncation n) :=
      congrArg (fun p => p.1) ha
    have ha2 : a.2.1.1.map (JetRing.truncation n) =
        (1 : Matrix (Fin 2) (Fin 2) JetRing).map (JetRing.truncation n) :=
      congrArg (fun p => p.2.1) ha
    have ha1 : JetRing.truncation n a.2.2.1 = JetRing.truncation n 1 :=
      congrArg (fun p => p.2.2) ha
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show (star a.1.1).map (JetRing.truncation n) =
        (1 : Matrix (Fin 3) (Fin 3) JetRing).map (JetRing.truncation n)
      rw [JetRing.matrix_truncation_star, ha3, ← JetRing.matrix_truncation_star, star_one]
    · show (star a.2.1.1).map (JetRing.truncation n) =
        (1 : Matrix (Fin 2) (Fin 2) JetRing).map (JetRing.truncation n)
      rw [JetRing.matrix_truncation_star, ha2, ← JetRing.matrix_truncation_star, star_one]
    · show JetRing.truncation n (star a.2.2.1) = JetRing.truncation n 1
      rw [JetRing.truncation_star, ha1, ← JetRing.truncation_star, star_one]

lemma mem_truncationKer_iff {n : ℕ} {U : JetGaugeGroupI} :
    U ∈ truncationKer n ↔ truncation n U = truncation n 1 := Iff.rfl

/-- Membership in the kernel of truncation, stated against the identity value. -/
lemma mem_truncationKer_iff_eq_one {n : ℕ} {U : JetGaugeGroupI} :
    U ∈ truncationKer n ↔ truncation n U = 1 := by
  rw [mem_truncationKer_iff, truncation_one]

/-- The kernel of truncation is normal: conjugating a jet that agrees with `1` up
  to order `n` leaves it agreeing with `1` up to order `n`, since to that order
  the conjugation collapses to `g * g⁻¹ = 1` by unitarity. -/
instance truncationKer_normal (n : ℕ) : (truncationKer n).Normal where
  conj_mem a ha g := by
    have ha3 : a.1.1.map (JetRing.truncation n) =
        (1 : Matrix (Fin 3) (Fin 3) JetRing).map (JetRing.truncation n) :=
      congrArg (fun p => p.1) ha
    have ha2 : a.2.1.1.map (JetRing.truncation n) =
        (1 : Matrix (Fin 2) (Fin 2) JetRing).map (JetRing.truncation n) :=
      congrArg (fun p => p.2.1) ha
    have ha1 : JetRing.truncation n a.2.2.1 = JetRing.truncation n 1 :=
      congrArg (fun p => p.2.2) ha
    have hg3 : g.1.1 * star g.1.1 = 1 := by
      have h := (Matrix.mem_specialUnitaryGroup_iff.mp g.1.2).1
      rwa [Matrix.mem_unitaryGroup_iff] at h
    have hg2 : g.2.1.1 * star g.2.1.1 = 1 := by
      have h := (Matrix.mem_specialUnitaryGroup_iff.mp g.2.1.2).1
      rwa [Matrix.mem_unitaryGroup_iff] at h
    have hg1 : g.2.2.1 * star g.2.2.1 = 1 := (Unitary.mem_iff.mp g.2.2.2).2
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show ((g.1.1 * a.1.1) * star g.1.1).map (JetRing.truncation n) =
        (1 : Matrix (Fin 3) (Fin 3) JetRing).map (JetRing.truncation n)
      rw [JetRing.matrix_truncation_mul_congr
        (JetRing.matrix_truncation_mul_congr rfl ha3) rfl, mul_one, hg3]
    · show ((g.2.1.1 * a.2.1.1) * star g.2.1.1).map (JetRing.truncation n) =
        (1 : Matrix (Fin 2) (Fin 2) JetRing).map (JetRing.truncation n)
      rw [JetRing.matrix_truncation_mul_congr
        (JetRing.matrix_truncation_mul_congr rfl ha2) rfl, mul_one, hg2]
    · show JetRing.truncation n ((g.2.2.1 * a.2.2.1) * star g.2.2.1) =
        JetRing.truncation n 1
      rw [JetRing.truncation_mul_congr (JetRing.truncation_mul_congr rfl ha1) rfl,
        mul_one, hg1]

/-!

## The zeroth truncation kernel: the pure jet gauge group

The kernel of the zeroth truncation consists of the jets whose value at the base
point is the identity — what was previously called the pure jet gauge group.

-/

/-- Membership in the zeroth truncation kernel is having identity value at the
  base point. -/
lemma mem_truncationKer_zero_iff {U : JetGaugeGroupI} :
    U ∈ truncationKer 0 ↔ U.eval = 1 := by
  rw [mem_truncationKer_iff]
  constructor
  · intro h
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · ext i j : 1
      have h3 := congrArg (fun p => (p.1 : Matrix (Fin 3) (Fin 3) JetRing) i j) h
      simpa [eval, evalSU, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.one_apply, apply_ite constantCoeff] using
        JetRing.truncation_zero_eq_iff.mp h3
    · ext i j : 1
      have h2 := congrArg (fun p => (p.2.1 : Matrix (Fin 2) (Fin 2) JetRing) i j) h
      simpa [eval, evalSU, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.one_apply, apply_ite constantCoeff] using
        JetRing.truncation_zero_eq_iff.mp h2
    · simpa [eval, evalU1] using
        JetRing.truncation_zero_eq_iff.mp (congrArg (fun p => (p.2.2 : JetRing)) h)
  · intro h
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show U.1.1.map (JetRing.truncation 0) =
        (1 : Matrix (Fin 3) (Fin 3) JetRing).map (JetRing.truncation 0)
      ext i j : 1
      refine JetRing.truncation_zero_eq_iff.mpr ?_
      have h3 := congrArg (fun p => (p.1 : Matrix (Fin 3) (Fin 3) ℂ) i j) h
      simpa [eval, evalSU, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.one_apply, apply_ite constantCoeff] using h3
    · show U.2.1.1.map (JetRing.truncation 0) =
        (1 : Matrix (Fin 2) (Fin 2) JetRing).map (JetRing.truncation 0)
      ext i j : 1
      refine JetRing.truncation_zero_eq_iff.mpr ?_
      have h2 := congrArg (fun p => (p.2.1 : Matrix (Fin 2) (Fin 2) ℂ) i j) h
      simpa [eval, evalSU, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.one_apply, apply_ite constantCoeff] using h2
    · show JetRing.truncation 0 U.2.2.1 = JetRing.truncation 0 (1 : JetRing)
      refine JetRing.truncation_zero_eq_iff.mpr ?_
      simpa [eval, evalU1] using congrArg (fun p => (p.2.2 : ℂ)) h

@[simp]
lemma eval_coe_of_mem_truncationKer_zero (U : truncationKer 0) : U.1.eval = 1 :=
  mem_truncationKer_zero_iff.mp U.2

lemma self_mul_ofConstant_eval_mem (U : JetGaugeGroupI) :
    U * (JetGaugeGroupI.ofConstant U.eval)⁻¹ ∈ truncationKer 0 := by
  rw [mem_truncationKer_zero_iff]
  simp

/-!

## The projection onto the zeroth truncation kernel

-/

/-- The projection from `JetGaugeGroupI` onto the kernel of the zeroth truncation,
  stripping the constant part: `U ↦ U · (U₀)⁻¹`. This is not a group homomorphism;
  it is the group-level cocycle of the semidirect splitting of `JetGaugeGroupI`
  by the constant jets. -/
noncomputable def truncationProjZero (U : JetGaugeGroupI) : truncationKer 0 :=
  ⟨U * (JetGaugeGroupI.ofConstant U.eval)⁻¹, self_mul_ofConstant_eval_mem U⟩

lemma truncationProjZero_surjective : Function.Surjective truncationProjZero := by
  intro V
  refine ⟨V.1, Subtype.ext ?_⟩
  have h1 : V.1.eval = 1 := mem_truncationKer_zero_iff.mp V.2
  simp [truncationProjZero, h1]

lemma truncationProjZero_eq_one_iff_constant {U : JetGaugeGroupI} :
    truncationProjZero U = 1 ↔ ∃ c, U = .ofConstant c := by
  constructor
  · intro h
    refine ⟨U.eval, ?_⟩
    have h1 : U * (JetGaugeGroupI.ofConstant U.eval)⁻¹ = 1 := congrArg Subtype.val h
    exact mul_inv_eq_one.mp h1
  · rintro ⟨c, rfl⟩
    apply Subtype.ext
    simp [truncationProjZero]

lemma truncationProjZero_ofConstant (c : GaugeGroupI) :
    truncationProjZero (JetGaugeGroupI.ofConstant c) = 1 := by
  rw [truncationProjZero_eq_one_iff_constant]
  exact ⟨c, rfl⟩

lemma eq_truncationProjZero_mul_ofConstant (U : JetGaugeGroupI) :
    U = truncationProjZero U * JetGaugeGroupI.ofConstant U.eval := by
  simp [truncationProjZero]

end JetGaugeGroupI
end StandardModel
