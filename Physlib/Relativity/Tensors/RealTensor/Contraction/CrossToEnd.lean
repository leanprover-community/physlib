/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Basic
/-!

# Components of real Lorentz cross contractions

## i. Overview

This file gives the standard-basis component formula for `crossToEnd` on real Lorentz tensors.
The contraction pairing of the standard covariant and contravariant bases reduces the generic
component expansion to one finite sum.

## ii. Key results

- `realLorentzTensor.crossToEnd_basis_repr_apply_eq_fin` expresses each component of a cross
  contraction as a sum over the contracted Lorentz index.

## iii. Table of contents

- A. Basis components

## iv. References

* None.
-/

@[expose] public section

noncomputable section

namespace realLorentzTensor

open TensorSpecies Tensor

/-!

## A. Basis components

-/

/-- For real Lorentz tensors, the component formula for `crossToEnd` collapses to one sum because
the standard contravariant and covariant bases are dual under contraction. -/
lemma crossToEnd_basis_repr_apply_eq_fin {d nA nB : ℕ} {cA : Fin (nA + 1) → Color}
    {cB : Fin (nB + 1) → Color} (i : Fin (nA + 1)) (j : Fin (nB + 1))
    (hc : (realLorentzTensor d).τ (cA i) = cB j) (t : ℝT(d, cA)) (M : ℝT(d, cB))
    (φ : ComponentIdx (S := realLorentzTensor d)
      (Fin.append (cA ∘ i.succAbove) (cB ∘ j.succAbove))) :
    (Tensor.basis _).repr (crossToEnd i j hc t M) φ =
      ∑ x : Fin 1 ⊕ Fin d,
        (Tensor.basis cA).repr t (i.insertNth x (fun m => φ (Fin.castAdd nB m))) *
          (Tensor.basis cB).repr M (j.insertNth x (fun m => φ (Fin.natAdd nA m))) := by
  rw [crossToEnd]
  simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
  rw [permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs => enter [2, x]; rw [permT_basis_repr_symm_apply, prodT_basis_repr_apply]
  simp only [basisIdxCongr_const, Equiv.refl_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [ComponentIdx.prod, Equiv.coe_fn_mk, basisIdxCongr_const, Equiv.refl_apply]
  congr 1
  · congr 1
    funext m
    rw [IsReindexing.inv_cast_eq]
    induction m using Fin.succAboveCases (i := i) with
    | x =>
      rw [Fin.insertNth_apply_same]
      exact ComponentIdx.DropPairSection.ofFinEquiv_apply_fst _ _ _
    | p q =>
      rw [Fin.insertNth_apply_succAbove]
      conv_lhs => rw [← Fin.succSuccAbove_castAdd_natAdd_apply_castAdd i j q]
      simp only [Fin.cast_cast, Fin.cast_eq_self]
      rw [(ComponentIdx.DropPairSection.mem_iff_apply_succSuccAbove_eq _ _).mp
        (ComponentIdx.DropPairSection.ofFinEquiv _ _ _).2]
      simp only [basisIdxCongr_const, Equiv.refl_apply]
      exact congrArg φ (IsReindexing.inv_id_eq _ _)
  · congr 1
    funext m
    rw [IsReindexing.inv_cast_eq]
    induction m using Fin.succAboveCases (i := j) with
    | x =>
      rw [Fin.insertNth_apply_same]
      exact ComponentIdx.DropPairSection.ofFinEquiv_apply_snd _ _ _
    | p q =>
      rw [Fin.insertNth_apply_succAbove]
      conv_lhs => rw [← Fin.succSuccAbove_castAdd_natAdd_apply_natAdd i j q]
      simp only [Fin.cast_cast, Fin.cast_eq_self]
      rw [(ComponentIdx.DropPairSection.mem_iff_apply_succSuccAbove_eq _ _).mp
        (ComponentIdx.DropPairSection.ofFinEquiv _ _ _).2]
      simp only [basisIdxCongr_const, Equiv.refl_apply]
      exact congrArg φ (IsReindexing.inv_id_eq _ _)

end realLorentzTensor
