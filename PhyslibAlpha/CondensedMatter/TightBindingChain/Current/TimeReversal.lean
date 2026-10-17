/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Current.Basic
public import PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.Product
/-!

# Time reversal in the open tight binding chain

## i. Overview

Time reversal `Θ` conjugates the amplitudes of a state in the site basis. It is antiunitary. The
Hamiltonian and the position operator have real matrix elements, so they commute with `Θ`, while
the current `J = i (H X - X H)` changes sign.

## ii. Key results

- `timeReversal` : complex conjugation of amplitudes.
- `inner_timeReversal`, `norm_timeReversal` : `Θ` is antiunitary.
- `apply_timeReversal` : an operator with real matrix elements commutes with `Θ`.
- `openHamiltonian_timeReversal`, `position_timeReversal` : `H` and `X` commute with `Θ`.
- `current_timeReversal` : `Θ` reverses the current.

## iii. Table of contents

- A. Time reversal

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open InnerProductSpace QuantumMechanics.FiniteHilbertSpace
variable (T : TightBindingChain)

/-!

## A. Time reversal

-/

/-- Time reversal: complex conjugation of the amplitudes. -/
noncomputable def timeReversal (ψ : T.HilbertSpace) : T.HilbertSpace :=
  ⟨WithLp.toLp 2 fun n => (starRingEnd ℂ) (ψ.val n)⟩

lemma timeReversal_val (ψ : T.HilbertSpace) (n : Fin T.N) :
    (T.timeReversal ψ).val n = (starRingEnd ℂ) (ψ.val n) := rfl

lemma timeReversal_sub (ψ φ : T.HilbertSpace) :
    T.timeReversal (ψ - φ) = T.timeReversal ψ - T.timeReversal φ := by
  ext n
  exact map_sub _ _ _

lemma timeReversal_smul (c : ℂ) (ψ : T.HilbertSpace) :
    T.timeReversal (c • ψ) = (starRingEnd ℂ) c • T.timeReversal ψ := by
  ext n
  exact map_mul _ _ _

lemma timeReversal_real_smul (r : ℝ) (ψ : T.HilbertSpace) :
    T.timeReversal (r • ψ) = r • T.timeReversal ψ := by
  rw [← Complex.coe_smul, timeReversal_smul, Complex.conj_ofReal, Complex.coe_smul]

lemma inner_timeReversal (ψ φ : T.HilbertSpace) :
    ⟪T.timeReversal ψ, T.timeReversal φ⟫_ℂ = (starRingEnd ℂ) ⟪ψ, φ⟫_ℂ := by
  simp only [inner_eq_val, PiLp.inner_apply, map_sum, RCLike.inner_apply, timeReversal_val,
    map_mul, Complex.conj_conj]

lemma norm_timeReversal (ψ : T.HilbertSpace) : ‖T.timeReversal ψ‖ = ‖ψ‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ ψ, inner_timeReversal,
    RCLike.conj_re]

/-- An operator with real matrix elements commutes with time reversal. -/
lemma apply_timeReversal {A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace}
    (hA : ∀ n m, (starRingEnd ℂ) ⟪|n⟩, A |m⟩⟫_ℂ = ⟪|n⟩, A |m⟩⟫_ℂ) (ψ : T.HilbertSpace) :
    A (T.timeReversal ψ) = T.timeReversal (A ψ) := by
  ext n
  rw [val_apply, timeReversal_val, val_apply, map_sum]
  exact Finset.sum_congr rfl fun m _ => by
    rw [map_mul, timeReversal_val, val_apply_basisFun]
    exact congrArg (· * _) (hA n m).symm

lemma openHamiltonian_timeReversal (ψ : T.HilbertSpace) :
    T.openHamiltonian (T.timeReversal ψ) = T.timeReversal (T.openHamiltonian ψ) :=
  T.apply_timeReversal (fun n m => by rw [inner_openHamiltonian]; split_ifs <;> simp) ψ

lemma position_timeReversal (ψ : T.HilbertSpace) :
    T.position (T.timeReversal ψ) = T.timeReversal (T.position ψ) :=
  T.apply_timeReversal (fun n m => by
    rw [position_apply_localizedState, inner_smul_right, localizedState_orthonormal_eq_ite]
    split_ifs <;> simp) ψ

/-- Time reversal reverses the current. -/
lemma current_timeReversal (ψ : T.HilbertSpace) :
    T.current (T.timeReversal ψ) = -T.timeReversal (T.current ψ) := by
  simp only [current, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    position_timeReversal, openHamiltonian_timeReversal, ← timeReversal_sub, timeReversal_smul,
    Complex.conj_I, neg_smul, neg_neg]

end TightBindingChain
end CondensedMatter
