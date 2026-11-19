/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.Fermions.Weyl.Metric
/-!
# The units are the unique invariants

Up to scale, the unit `δ` is the only invariant of a Weyl representation tensored with its dual.

## i. Overview

On `V ⊗ V*`, for `V` one of the four Weyl representations, `SL(2, ℂ)` acts on the matrix of
components by conjugation, `X ↦ N X N⁻¹`. The two boosts along `z` combine to give the
off-diagonal part of `X`, so an invariant has none, and conjugation by `ε` swaps the two diagonal
entries (A). An invariant of `V ⊗ V*` therefore has a multiple of the identity matrix as
components, which is the unit `δ` (B). For each of the four pairs this says that the invariants of
`V ⊗ V*` are the line through `δ` (C).

## ii. Key results

- `Fermion.DualLeftHandedWeyl.invariants_tprod_eq_span_unitVal` and its three siblings : the
  invariants of `V ⊗ V*` are the line through the unit.

## iii. Table of contents

- A. Matrices
- B. Tensor products
- C. The four pairs

## iv. References

The units are in `Physlib.Relativity.Fermions.Weyl.Unit`, where these results are written to move.
The matrix of components `tensorToMatrix`, the elements `boostTwo`, `boostHalf` and `epsilon`,
and the tactic `weyl_act` are in `PhyslibAlpha.Relativity.Fermions.Weyl.Metric`, alongside the
analogous results for the metrics.

-/

@[expose] public section

namespace Fermion

noncomputable section

open Matrix MatrixGroups TensorProduct

/-!

## A. Matrices

-/

section Units

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- A linear map on matrices which is unchanged by the boosts `X ↦ D X D⁻¹`, on every matrix
  with the same image as `X`, and by `X ↦ ε X ε⁻¹` at `X`, sends `X` to a multiple of the image
  of the identity. -/
lemma map_eq_smul_map_one_of_conj (F : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] B)
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hD : ∀ Z, F Z = F X → F !![Z 0 0, 4 * Z 0 1; Z 1 0 / 4, Z 1 1] = F Z)
    (hD' : ∀ Z, F Z = F X → F !![Z 0 0, Z 0 1 / 4; 4 * Z 1 0, Z 1 1] = F Z)
    (hε : F !![X 1 1, -X 1 0; -X 0 1, X 0 0] = F X) :
    F X = ((X 0 0 + X 1 1) / 2) • F 1 := by
  have hdiag (Z : Matrix (Fin 2) (Fin 2) ℂ) (hZ : F Z = F X) :
      F Z = F !![Z 0 0, 0; 0, Z 1 1] := by
    have hsplit : Z = !![Z 0 0, 0; 0, Z 1 1] + (4 / 9 : ℂ) • (!![Z 0 0, 4 * Z 0 1; Z 1 0 / 4, Z 1 1]
        + !![Z 0 0, Z 0 1 / 4; 4 * Z 1 0, Z 1 1] - (2 : ℂ) • Z) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> ring
    conv_lhs => rw [hsplit]
    rw [map_add, map_smul, map_sub, map_add, map_smul, hD Z hZ, hD' Z hZ]
    module
  have h1 := hdiag X rfl
  have h2 : F X = F !![X 1 1, 0; 0, X 0 0] := by
    rw [← hε, hdiag _ hε]
    simp
  have hsum : !![X 0 0, 0; 0, X 1 1] + !![X 1 1, 0; 0, X 0 0] =
      (X 0 0 + X 1 1) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  calc F X = (1 / 2 : ℂ) • (F X + F X) := by module
    _ = (1 / 2 : ℂ) • F (!![X 0 0, 0; 0, X 1 1] + !![X 1 1, 0; 0, X 0 0]) := by
      rw [map_add, ← h1, ← h2]
    _ = ((X 0 0 + X 1 1) / 2) • F 1 := by
      rw [hsum, map_smul, smul_smul]
      ring_nf

/-!

## B. Tensor products

-/

/-- When three elements of `SL(2,ℂ)` act on the components of `V ⊗ W` as two boosts and `ε`,
  every invariant of `V ⊗ W` is a multiple of the element with the identity as components. -/
lemma exists_eq_smul_one_of_conj {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (b : Module.Basis (Fin 2) ℂ V) (c : Module.Basis (Fin 2) ℂ W)
    {ρV : Representation ℂ SL(2,ℂ) V} {ρW : Representation ℂ SL(2,ℂ) W} {v : V ⊗[ℂ] W}
    (hv : v ∈ (ρV.tprod ρW).invariants)
    (hD : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![X 0 0, 4 * X 0 1; X 1 0 / 4, X 1 1])
    (hD' : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![X 0 0, X 0 1 / 4; 4 * X 1 0, X 1 1])
    (hε : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![X 1 1, -X 1 0; -X 0 1, X 0 0]) :
    ∃ z : ℂ, v = z • (tensorToMatrix b c).symm 1 := by
  have hinv' (Z : Matrix (Fin 2) (Fin 2) ℂ)
      (hZ : (tensorToMatrix b c).symm Z = (tensorToMatrix b c).symm (tensorToMatrix b c v)) :
      (tensorToMatrix b c).symm Z ∈ (ρV.tprod ρW).invariants := by
    rw [hZ, LinearEquiv.symm_apply_apply]
    exact hv
  have hF (Z : Matrix (Fin 2) (Fin 2) ℂ) :
      (tensorToMatrix b c).symm.toLinearMap Z = (tensorToMatrix b c).symm Z := rfl
  have h := map_eq_smul_map_one_of_conj (tensorToMatrix b c).symm.toLinearMap
    (X := tensorToMatrix b c v)
    (fun Z hZ => by
      rw [hF, hF] at hZ ⊢
      exact (symm_act_eq b c (hinv' Z hZ) (h := hD) :))
    (fun Z hZ => by
      rw [hF, hF] at hZ ⊢
      exact (symm_act_eq b c (hinv' Z hZ) (h := hD') :))
    (by
      rw [hF, hF]
      exact (symm_act_eq b c (hinv' _ rfl) (h := hε) :))
  rw [hF, hF, LinearEquiv.symm_apply_apply] at h
  exact ⟨_, h⟩

/-!

## C. The four pairs

For each pair `V ⊗ V*` the statement is in the namespace that holds its unit, as in
`DualLeftHandedWeyl.unitVal : LeftHandedWeyl ⊗ DualLeftHandedWeyl`.

-/

/-- The `SL(2,ℂ)`-invariants of `LeftHandedWeyl ⊗ DualLeftHandedWeyl` are the line through the unit
  `δᵃₐ`. -/
lemma DualLeftHandedWeyl.invariants_tprod_eq_span_unitVal :
    (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).invariants = ℂ ∙ unitVal :=
  Representation.invariants_eq_span_singleton
    (by simpa [unit_apply_one] using unit.apply_one_mem_invariants) fun _ hv =>
    exists_eq_smul_one_of_conj LeftHandedWeyl.basis DualLeftHandedWeyl.basis hv
      ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩ ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩
      ⟨Lorentz.SL2C.epsilon, by weyl_act⟩

/-- The `SL(2,ℂ)`-invariants of `DualLeftHandedWeyl ⊗ LeftHandedWeyl` are the line through the unit
  `δₐᵃ`. -/
lemma LeftHandedWeyl.invariants_tprod_eq_span_unitVal :
    (DualLeftHandedWeyl.rep.tprod LeftHandedWeyl.rep).invariants = ℂ ∙ unitVal :=
  Representation.invariants_eq_span_singleton
    (by simpa [unit_apply_one] using unit.apply_one_mem_invariants) fun _ hv =>
    exists_eq_smul_one_of_conj DualLeftHandedWeyl.basis LeftHandedWeyl.basis hv
      ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩ ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩
      ⟨Lorentz.SL2C.epsilon, by weyl_act⟩

/-- The `SL(2,ℂ)`-invariants of `RightHandedWeyl ⊗ DualRightHandedWeyl` are the line through the
  unit `δ^{ȧ}_{ȧ}`. -/
lemma DualRightHandedWeyl.invariants_tprod_eq_span_unitVal :
    (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep).invariants = ℂ ∙ unitVal :=
  Representation.invariants_eq_span_singleton
    (by simpa [unit_apply_one] using unit.apply_one_mem_invariants) fun _ hv =>
    exists_eq_smul_one_of_conj RightHandedWeyl.basis DualRightHandedWeyl.basis hv
      ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩ ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩
      ⟨Lorentz.SL2C.epsilon, by weyl_act⟩

/-- The `SL(2,ℂ)`-invariants of `DualRightHandedWeyl ⊗ RightHandedWeyl` are the line through the
  unit `δ_{ȧ}^{ȧ}`. -/
lemma RightHandedWeyl.invariants_tprod_eq_span_unitVal :
    (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep).invariants = ℂ ∙ unitVal :=
  Representation.invariants_eq_span_singleton
    (by simpa [unit_apply_one] using unit.apply_one_mem_invariants) fun _ hv =>
    exists_eq_smul_one_of_conj DualRightHandedWeyl.basis RightHandedWeyl.basis hv
      ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩ ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩
      ⟨Lorentz.SL2C.epsilon, by weyl_act⟩

end Units

end

end Fermion
