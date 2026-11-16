/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Basic
public import Physlib.SpaceAndTime.WaveVectorSpace.Derivatives.Basic
/-!

# Duality of `Space` and `WaveVectorSpace`

## i. Overview

Upon selecting an origin for the affine space `Space d`,
the spaces `Space d` and `WaveVectorSpace d` are dual as real vector spaces.
There is natural continuous bilinear map `WaveVectorSpace d × Space d → ℝ` which sends
the pair `(k, x)` to `∑ᵢ kⁱxᵢ`. For fixed `k` this gives rise to a functional `Space d →L[ℝ] ℝ`
mapping `x ↦ k ⬝ᵥ x`, and similarly for fixed `x`.

## ii. Key results

- `Space.dual x` : the functional on `WaveVectorSpace` corresponding to `x : Space d`,
  bundled as a continuous linear map.
- `WaveVectorSpace.dual k` : the functional on `Space` corresponding to `k : WaveVectorSpace d`,
  bundled as a continuous linear map.
- `WaveVectorSpace.pairingCLM` : the dual pairing between `WaveVectorSpace` and `Space`,
  bundled as a continuous bilinear map.

## iii. Table of contents

- A. Strong duals
- B. Bilinear pairing
- C. Derivatives

## iv. References

-/

@[expose] public section

TODO "Show how the dual functionals interact with `VAdd (EuclideanSpace ℝ (Fin d)) (Space d)`."

variable {d : ℕ}

/-!
## A. Strong duals
-/

namespace Space

/-- The functional on `WaveVectorSpace d` dual to `x`, defined by `k ↦ k ⬝ᵥ x`. -/
def dual (x : Space d) : StrongDual ℝ (WaveVectorSpace d) where
  toFun k := k ⬝ᵥ x
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

lemma dual_apply (x : Space d) (k : WaveVectorSpace d) : x.dual k = k ⬝ᵥ x := rfl

@[simp]
lemma opNorm_dual_eq_norm (x : Space d) : ‖x.dual‖ = ‖x‖ := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds (norm_nonneg x) (fun k ↦ ?_) fun N hN h ↦ ?_
  · calc
      _ = |inner ℝ (WithLp.toLp 2 x.val) (WithLp.toLp 2 k.val)| := by
        simp [dual_apply, inner, dotProduct]
      _ ≤ ‖WithLp.toLp 2 x.val‖ * ‖WithLp.toLp 2 k.val‖ := abs_real_inner_le_norm _ _
      _ = ‖x‖ * ‖k‖ := by simp [PiLp.norm_eq_of_L2, norm_eq, WaveVectorSpace.norm_eq]
  · suffices ‖x‖ ^ 2 ≤ N * ‖x‖ by nlinarith
    simpa [dual_apply, dotProduct, ← pow_two, ← norm_sq_eq, WaveVectorSpace.norm_eq] using h ⟨x⟩

end Space

namespace WaveVectorSpace

/-- The functional on `Space d` dual to `k`, defined by `x ↦ k ⬝ᵥ x`. -/
def dual (k : WaveVectorSpace d) : StrongDual ℝ (Space d) where
  toFun x := k ⬝ᵥ x
  map_add' _ _ := by simp
  map_smul' _ _ := by simp [dotProduct, mul_left_comm, Finset.mul_sum]

lemma dual_apply (k : WaveVectorSpace d) (x : Space d) : k.dual x = k ⬝ᵥ x := rfl

@[simp]
lemma opNorm_dual_eq_norm (k : WaveVectorSpace d) : ‖k.dual‖ = ‖k‖ := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds (norm_nonneg k) (fun x ↦ ?_) fun N hN h ↦ ?_
  · calc
      _ = |inner ℝ (WithLp.toLp 2 x.val) (WithLp.toLp 2 k.val)| := by
        simp [dual_apply, inner, dotProduct]
      _ ≤ ‖WithLp.toLp 2 x.val‖ * ‖WithLp.toLp 2 k.val‖ := abs_real_inner_le_norm _ _
      _ = ‖k‖ * ‖x‖ := by simp [PiLp.norm_eq_of_L2, norm_eq, Space.norm_eq, mul_comm]
  · suffices ‖k‖ ^ 2 ≤ N * ‖k‖ by nlinarith
    simpa [dual_apply, dotProduct, ← pow_two, ← norm_sq_eq, Space.norm_eq] using h ⟨k⟩

/-!
## B. Bilinear pairing
-/

/-- The bilinear form `WaveVectorSpace d × Space d → ℝ` given by `k ↦ x ↦ k ⬝ᵥ x`. -/
def pairingCLM : WaveVectorSpace d →L[ℝ] Space d →L[ℝ] ℝ where
  toFun k := k.dual
  map_add' _ _ := by ext; simp [dual_apply]
  map_smul' _ _ := by ext; simp [dual_apply, dotProduct, mul_assoc, Finset.mul_sum]
  cont := by
    refine continuous_clm_apply.mpr fun x ↦ ?_
    change Continuous x.dual
    fun_prop

lemma pairingCLM_apply_eq_dual (k : WaveVectorSpace d) : pairingCLM k = k.dual := rfl

lemma pairingCLM_flip_apply_eq_dual (x : Space d) : pairingCLM.flip x = x.dual := rfl

@[simp]
lemma pairingCLM_apply_apply (k : WaveVectorSpace d) (x : Space d) : pairingCLM k x = k ⬝ᵥ x := rfl

@[fun_prop]
lemma continuous_dual : Continuous (dual : WaveVectorSpace d → StrongDual ℝ (Space d)) :=
  pairingCLM.continuous

@[fun_prop]
lemma _root_.Space.continuous_dual :
    Continuous (Space.dual : Space d → StrongDual ℝ (WaveVectorSpace d)) :=
  pairingCLM.flip.continuous

/-!
## C. Derivatives
-/

@[simp]
lemma deriv_pairingCLM (i : Fin d) (k : WaveVectorSpace d) (x : Space d) :
    ∂[i] (pairingCLM k) x = k i := by
  simp [Space.deriv_eq, pairingCLM_apply_eq_dual, dual_apply, dotProduct, Space.basis_apply]

@[simp]
lemma deriv_pairingCLM_flip (i : Fin d) (x : Space d) (k : WaveVectorSpace d) :
    ∂[i] (pairingCLM.flip x) k = x i := by
  simp [deriv_eq, pairingCLM_flip_apply_eq_dual, Space.dual_apply, dotProduct, basis_apply,
    ← nsmul_eq_mul]

/-- The derivative of the functional `x ↦ k ⬝ᵥ x` with respect to `xⁱ` is `kᵢ`. -/
@[simp]
lemma deriv_dual (i : Fin d) (k : WaveVectorSpace d) (x : Space d) : ∂[i] k.dual x = k i :=
  deriv_pairingCLM i k x

/-- The derivative of the functional `k ↦ k ⬝ᵥ x` with respect to `kᵢ` is `xⁱ`. -/
@[simp]
lemma _root_.Space.deriv_dual (i : Fin d) (x : Space d) (k : WaveVectorSpace d) :
    ∂[i] x.dual k = x i :=
  deriv_pairingCLM_flip i x k

end WaveVectorSpace
