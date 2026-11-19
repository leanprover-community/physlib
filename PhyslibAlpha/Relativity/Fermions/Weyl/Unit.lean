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
off-diagonal part of `X`, so an equivariant map kills it, and conjugation by `ε` swaps the two
diagonal entries (A). An invariant in the image of an equivariant map out of `V ⊗ V*` is
therefore the image of a multiple of the identity matrix, which is the unit `δ` (B). For each of
the four pairs this gives three statements (C). The invariants in the image of an equivariant map
`f` out of `V ⊗ V*` are the line through `f δ`; for `f` the identity, the invariants of `V ⊗ V*`
are the line through `δ`; and every intertwining map from the trivial representation is a
multiple of the unit.

## ii. Key results

- `Fermion.DualLeftHandedWeyl.invariants_inf_range_eq_span_map_unitVal` and its three siblings :
  the invariants in the image of an equivariant map out of `V ⊗ V*` are the line through the image
  of the unit.
- `Fermion.DualLeftHandedWeyl.invariants_tprod_eq_span_unitVal` and its three siblings : the
  invariants of `V ⊗ V*` are the line through the unit.
- `Fermion.DualLeftHandedWeyl.intertwiningMap_eq_smul_unit` and its three siblings : every
  intertwining map from the trivial representation into `V ⊗ V*` is a multiple of the unit.

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

/-- For an equivariant map `f` out of `V ⊗ W`, on which three elements of `SL(2,ℂ)` act on
  components as two boosts and `ε`, every invariant in the image of `f` is a multiple of the image
  of the element with the identity as components. -/
lemma exists_eq_smul_map_one_of_conj {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (b : Module.Basis (Fin 2) ℂ V) (c : Module.Basis (Fin 2) ℂ W)
    {ρV : Representation ℂ SL(2,ℂ) V} {ρW : Representation ℂ SL(2,ℂ) W}
    {ρ : Representation ℂ SL(2,ℂ) B} (f : (ρV.tprod ρW).IntertwiningMap ρ) {x : B}
    (hinv : x ∈ ρ.invariants) (hx : x ∈ f.range.toSubmodule)
    (hD : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![X 0 0, 4 * X 0 1; X 1 0 / 4, X 1 1])
    (hD' : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![X 0 0, X 0 1 / 4; 4 * X 1 0, X 1 1])
    (hε : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![X 1 1, -X 1 0; -X 0 1, X 0 0]) :
    ∃ z : ℂ, x = z • f ((tensorToMatrix b c).symm 1) := by
  obtain ⟨v, rfl⟩ := hx
  have hinv : ∀ g, ρ g (f v) = f v := hinv
  have hinv' (Z : Matrix (Fin 2) (Fin 2) ℂ)
      (hZ : f ((tensorToMatrix b c).symm Z) = f ((tensorToMatrix b c).symm (tensorToMatrix b c v)))
      (g : SL(2,ℂ)) : ρ g (f ((tensorToMatrix b c).symm Z)) = f ((tensorToMatrix b c).symm Z) := by
    rw [hZ, LinearEquiv.symm_apply_apply]
    exact hinv g
  set F := f.toLinearMap ∘ₗ (tensorToMatrix b c).symm.toLinearMap with hF
  have hFa (Z : Matrix (Fin 2) (Fin 2) ℂ) : F Z = f ((tensorToMatrix b c).symm Z) := by
    rw [hF, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Representation.IntertwiningMap.toLinearMap_apply]
  have h := map_eq_smul_map_one_of_conj F (X := tensorToMatrix b c v)
    (fun Z hZ => by
      rw [hFa, hFa] at hZ ⊢
      exact (map_symm_act_eq b c f (hinv' Z hZ) (h := hD) :))
    (fun Z hZ => by
      rw [hFa, hFa] at hZ ⊢
      exact (map_symm_act_eq b c f (hinv' Z hZ) (h := hD') :))
    (by
      rw [hFa, hFa]
      exact (map_symm_act_eq b c f (hinv' _ rfl) (h := hε) :))
  rw [hFa, hFa, LinearEquiv.symm_apply_apply] at h
  exact ⟨_, h⟩

/-!

## C. The four pairs

For each pair `V ⊗ V*` the statements are in the namespace that holds its unit, as in
`DualLeftHandedWeyl.unitVal : LeftHandedWeyl ⊗ DualLeftHandedWeyl`.

-/

variable {ρ : Representation ℂ SL(2,ℂ) B}

/-- For an equivariant map `f` out of `LeftHandedWeyl ⊗ DualLeftHandedWeyl`, the
  `SL(2,ℂ)`-invariants in the image of `f` are the line through the image `f δᵃₐ` of the unit. -/
lemma DualLeftHandedWeyl.invariants_inf_range_eq_span_map_unitVal
    (f : (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f unitVal :=
  Representation.invariants_inf_range_eq_span
    (by simpa [unit_apply_one] using unit.apply_one_mem_invariants) fun _ hinv hx =>
    exists_eq_smul_map_one_of_conj LeftHandedWeyl.basis DualLeftHandedWeyl.basis f hinv hx
      ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩ ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩
      ⟨Lorentz.SL2C.epsilon, by weyl_act⟩

/-- The `SL(2,ℂ)`-invariants of `LeftHandedWeyl ⊗ DualLeftHandedWeyl` are the line through the unit
  `δᵃₐ`. -/
lemma DualLeftHandedWeyl.invariants_tprod_eq_span_unitVal :
    (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).invariants = ℂ ∙ unitVal := by
  simpa using invariants_inf_range_eq_span_map_unitVal (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `LeftHandedWeyl ⊗
  DualLeftHandedWeyl` is a multiple of the unit `δᵃₐ`. -/
lemma DualLeftHandedWeyl.intertwiningMap_eq_smul_unit
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep)) :
    ∃ z : ℂ, φ = z • unit :=
  Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span
    (by rw [unit_apply_one]; exact invariants_tprod_eq_span_unitVal) φ

/-- For an equivariant map `f` out of `DualLeftHandedWeyl ⊗ LeftHandedWeyl`, the
  `SL(2,ℂ)`-invariants in the image of `f` are the line through the image `f δₐᵃ` of the unit. -/
lemma LeftHandedWeyl.invariants_inf_range_eq_span_map_unitVal
    (f : (DualLeftHandedWeyl.rep.tprod LeftHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f unitVal :=
  Representation.invariants_inf_range_eq_span
    (by simpa [unit_apply_one] using unit.apply_one_mem_invariants) fun _ hinv hx =>
    exists_eq_smul_map_one_of_conj DualLeftHandedWeyl.basis LeftHandedWeyl.basis f hinv hx
      ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩ ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩
      ⟨Lorentz.SL2C.epsilon, by weyl_act⟩

/-- The `SL(2,ℂ)`-invariants of `DualLeftHandedWeyl ⊗ LeftHandedWeyl` are the line through the unit
  `δₐᵃ`. -/
lemma LeftHandedWeyl.invariants_tprod_eq_span_unitVal :
    (DualLeftHandedWeyl.rep.tprod LeftHandedWeyl.rep).invariants = ℂ ∙ unitVal := by
  simpa using invariants_inf_range_eq_span_map_unitVal (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `DualLeftHandedWeyl ⊗
  LeftHandedWeyl` is a multiple of the unit `δₐᵃ`. -/
lemma LeftHandedWeyl.intertwiningMap_eq_smul_unit
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (DualLeftHandedWeyl.rep.tprod LeftHandedWeyl.rep)) :
    ∃ z : ℂ, φ = z • unit :=
  Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span
    (by rw [unit_apply_one]; exact invariants_tprod_eq_span_unitVal) φ

/-- For an equivariant map `f` out of `RightHandedWeyl ⊗ DualRightHandedWeyl`, the
  `SL(2,ℂ)`-invariants in the image of `f` are the line through the image `f δ^{ȧ}_{ȧ}` of the unit.
  -/
lemma DualRightHandedWeyl.invariants_inf_range_eq_span_map_unitVal
    (f : (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f unitVal :=
  Representation.invariants_inf_range_eq_span
    (by simpa [unit_apply_one] using unit.apply_one_mem_invariants) fun _ hinv hx =>
    exists_eq_smul_map_one_of_conj RightHandedWeyl.basis DualRightHandedWeyl.basis f hinv hx
      ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩ ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩
      ⟨Lorentz.SL2C.epsilon, by weyl_act⟩

/-- The `SL(2,ℂ)`-invariants of `RightHandedWeyl ⊗ DualRightHandedWeyl` are the line through the
  unit `δ^{ȧ}_{ȧ}`. -/
lemma DualRightHandedWeyl.invariants_tprod_eq_span_unitVal :
    (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep).invariants = ℂ ∙ unitVal := by
  simpa using invariants_inf_range_eq_span_map_unitVal (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `RightHandedWeyl ⊗
  DualRightHandedWeyl` is a multiple of the unit `δ^{ȧ}_{ȧ}`. -/
lemma DualRightHandedWeyl.intertwiningMap_eq_smul_unit
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep)) :
    ∃ z : ℂ, φ = z • unit :=
  Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span
    (by rw [unit_apply_one]; exact invariants_tprod_eq_span_unitVal) φ

/-- For an equivariant map `f` out of `DualRightHandedWeyl ⊗ RightHandedWeyl`, the
  `SL(2,ℂ)`-invariants in the image of `f` are the line through the image `f δ_{ȧ}^{ȧ}` of the unit.
  -/
lemma RightHandedWeyl.invariants_inf_range_eq_span_map_unitVal
    (f : (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f unitVal :=
  Representation.invariants_inf_range_eq_span
    (by simpa [unit_apply_one] using unit.apply_one_mem_invariants) fun _ hinv hx =>
    exists_eq_smul_map_one_of_conj DualRightHandedWeyl.basis RightHandedWeyl.basis f hinv hx
      ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩ ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩
      ⟨Lorentz.SL2C.epsilon, by weyl_act⟩

/-- The `SL(2,ℂ)`-invariants of `DualRightHandedWeyl ⊗ RightHandedWeyl` are the line through the
  unit `δ_{ȧ}^{ȧ}`. -/
lemma RightHandedWeyl.invariants_tprod_eq_span_unitVal :
    (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep).invariants = ℂ ∙ unitVal := by
  simpa using invariants_inf_range_eq_span_map_unitVal (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `DualRightHandedWeyl ⊗
  RightHandedWeyl` is a multiple of the unit `δ_{ȧ}^{ȧ}`. -/
lemma RightHandedWeyl.intertwiningMap_eq_smul_unit
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep)) :
    ∃ z : ℂ, φ = z • unit :=
  Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span
    (by rw [unit_apply_one]; exact invariants_tprod_eq_span_unitVal) φ

end Units

end

end Fermion
