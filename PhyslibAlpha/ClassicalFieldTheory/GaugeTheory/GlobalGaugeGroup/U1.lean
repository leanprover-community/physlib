/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.Basic
public import PhyslibAlpha.Mathematics.ForMathlib.DataStructures.Matrix.Scalar
public import Physlib.Mathematics.ForMathlib.DataStructures.Matrix.LieTrace
/-!
# The global gauge group U(1)

The group of phases, as a global gauge group.

## i. Overview

The gauge group of electromagnetism, and of weak hypercharge in the Standard Model, is
`U(1)`. It is the group of complex numbers of modulus one, the phases `e^{iθ}`, acting on a
charged field by multiplication. As a global gauge group it is the group of unitary `1 × 1`
complex matrices, and an invertible `1 × 1` matrix lies in it exactly when its entry has
modulus one.

Its generators are the anti-hermitian `1 × 1` matrices, the imaginary numbers `i θ`, whose
exponentials `e^{i t θ}` are phases. The hermitian generator of physics is the real charge
`θ`.

## ii. Key results

- `GlobalGaugeGroup.U1` : the global gauge group `U(1)`.
- `GlobalGaugeGroup.mem_U1_iff` : an invertible `1 × 1` matrix lies in `U(1)` exactly when
  its entry has modulus one.
- `GlobalGaugeGroup.mem_lieAlgebra_U1` : anti-hermitian `1 × 1` matrices are generators of
  `U(1)`.
- `GlobalGaugeGroup.exists_eq_I_smul_scalar_of_mem_lieAlgebra_U1` : generators of `U(1)` are
  imaginary scalars.

## iii. Table of contents

- A. The group U(1)
- B. Elements as phases
- C. The Lie algebra of U(1)

## iv. References

* None.

-/

@[expose] public section

open Matrix

namespace GlobalGaugeGroup

/-!

## A. The group U(1)

-/

/-- The global gauge group `U(1)`, the unitary `1 × 1` complex matrices. -/
def U1 : GlobalGaugeGroup (Fin 1) :=
  ofSubmonoid (unitaryGroup (Fin 1) ℂ) isClosed_unitary

lemma mem_U1_iff_mem_unitaryGroup {g : GeneralLinearGroup (Fin 1) ℂ} :
    g ∈ U1.group ↔ (g : Matrix (Fin 1) (Fin 1) ℂ) ∈ unitaryGroup (Fin 1) ℂ :=
  mem_ofSubmonoid_iff_of_star_mem le_rfl fun _ hA => Unitary.star_mem hA

/-!

## B. Elements as phases

-/

/-- An invertible `1 × 1` matrix lies in `U(1)` exactly when its entry is a phase, of
  modulus one. -/
lemma mem_U1_iff {g : GeneralLinearGroup (Fin 1) ℂ} :
    g ∈ U1.group ↔ ‖(g : Matrix (Fin 1) (Fin 1) ℂ) 0 0‖ = 1 := by
  rw [mem_U1_iff_mem_unitaryGroup, mem_unitaryGroup_iff']
  have h : star (g : Matrix (Fin 1) (Fin 1) ℂ) * g = 1 ↔
      starRingEnd ℂ ((g : Matrix (Fin 1) (Fin 1) ℂ) 0 0) * (g : Matrix (Fin 1) (Fin 1) ℂ) 0 0
        = 1 := by
    refine ⟨fun h => by simpa [Matrix.mul_apply] using congrFun (congrFun h 0) 0,
      fun h => Matrix.ext fun i j => ?_⟩
    fin_cases i
    fin_cases j
    simpa [Matrix.mul_apply] using h
  rw [h, Complex.conj_mul']
  norm_cast
  exact pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero

/-- The phases are the elements of the global gauge group `U(1)`, as scalar `1 × 1`
  matrices. -/
noncomputable def U1.groupEquiv : unitary ℂ ≃* U1.group where
  toFun u := ⟨⟨scalar (Fin 1) (u : ℂ), scalar (Fin 1) (star (u : ℂ)),
      by rw [← map_mul, Unitary.mul_star_self_of_mem u.2, map_one],
      by rw [← map_mul, Unitary.star_mul_self_of_mem u.2, map_one]⟩,
    mem_U1_iff_mem_unitaryGroup.2 (mem_unitaryGroup_iff.2 (by
      show scalar (Fin 1) (u : ℂ) * star (scalar (Fin 1) (u : ℂ)) = 1
      rw [star_scalar, ← map_mul, Unitary.mul_star_self_of_mem u.2, map_one]))⟩
  invFun g := ⟨(g.1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0, by
    have hg := mem_unitaryGroup_iff.1 (mem_U1_iff_mem_unitaryGroup.1 g.2)
    have h : (g.1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 * star ((g.1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0)
        = 1 := by simpa [Matrix.mul_apply] using congrFun (congrFun hg 0) 0
    exact Unitary.mem_iff.2 ⟨(mul_comm _ _).trans h, h⟩⟩
  left_inv u := Subtype.ext (by simp)
  right_inv g := Subtype.ext (Units.ext (Matrix.ext fun i j => by
    fin_cases i; fin_cases j; simp))
  map_mul' u v := Subtype.ext (Units.ext (map_mul _ _ _))

@[simp]
lemma U1.groupEquiv_val (u : unitary ℂ) :
    (((U1.groupEquiv u : U1.group) : GeneralLinearGroup (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ) =
      scalar (Fin 1) (u : ℂ) := rfl

/-!

## C. The Lie algebra of U(1)

-/

/-- An anti-hermitian `1 × 1` matrix is a generator of `U(1)`. Its exponential is unitary,
  with conjugate transpose the exponential of `−X`. -/
lemma mem_lieAlgebra_U1 {X : Matrix (Fin 1) (Fin 1) ℂ} (hX : star X = -X) :
    X ∈ U1.lieAlgebra := by
  intro t
  have hY : star (t • X) = -(t • X) := by rw [star_smul, hX, star_trivial, smul_neg]
  have hu : NormedSpace.exp (t • X) * star (NormedSpace.exp (t • X)) = 1 := by
    rw [star_eq_conjTranspose, ← Matrix.exp_conjTranspose, ← star_eq_conjTranspose, hY,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  exact ⟨⟨(isUnit_exp (t • X)).unit, mem_U1_iff_mem_unitaryGroup.2
    (mem_unitaryGroup_iff.2 hu)⟩, rfl⟩

/-- A generator of `U(1)` is an imaginary scalar `i a` with `a` real. The entry of `exp (X)` is
  `exp (x)` and has modulus one, so `x` has vanishing real part. -/
lemma exists_eq_I_smul_scalar_of_mem_lieAlgebra_U1 {X : Matrix (Fin 1) (Fin 1) ℂ}
    (hX : X ∈ U1.lieAlgebra) : ∃ a : ℝ, X = Complex.I • scalar (Fin 1) (a : ℂ) := by
  obtain ⟨g, hg⟩ := hX 1
  have hn := mem_U1_iff.mp g.2
  have hdet : (NormedSpace.exp ((1 : ℝ) • X)).det = NormedSpace.exp X.trace := by
    rw [Matrix.det_exp, trace_smul]; simp
  have hdet' : (g.1 : Matrix (Fin 1) (Fin 1) ℂ).det = (g.1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 := by
    simp
  have hre : (X 0 0).re = 0 := by
    rw [← hdet', show (g.1 : Matrix (Fin 1) (Fin 1) ℂ) = _ from hg, hdet,
      ← Complex.exp_eq_exp_ℂ] at hn
    simpa [Complex.norm_exp, Matrix.trace] using hn
  refine ⟨(X 0 0).im, ?_⟩
  rw [eq_scalar_fin_one X]
  ext i j
  fin_cases i; fin_cases j
  simp [Complex.ext_iff, hre]

end GlobalGaugeGroup
