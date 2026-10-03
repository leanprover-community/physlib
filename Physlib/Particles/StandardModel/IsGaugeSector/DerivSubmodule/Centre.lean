/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsGaugeSector.Basic
public import Physlib.Relativity.LorentzGroup.Invariants.Centre
/-!
# The centre of `SL(2,ℂ)` on the gauge sector

The field strength is of integer spin, so the centre of `SL(2,ℂ)` acts on its derivative
submodules by `+1`. Every index a field-strength symbol carries — the two covector indices and
the covariant-derivative slots — mixes by the Lorentz matrix, and the adjoint value index does
not see the Lorentz group at all; since `-1` covers the identity Lorentz transformation
(`SL2C.toLorentzGroup_neg_one`), nothing moves.

This is the integer-spin half of the parity count the gauge-fermion classification runs.
Paired with `IsFermionSector.derivSubmodule_le_centreEigenspace`, which gives the fermions
`-1`, it makes the product `F ψ` carry `-1`, and a subspace of sign `-1` carries no Lorentz
invariant.

Unlike the Higgs and fermion towers, the field-strength symbols are not of the shape
`IsLorentzCovDerivTransforms` describes — they carry two covector indices beside their
derivative slots — so the collapse at the centre is run directly on `repLorentz_F`.

- A. The field-strength symbols
- B. The field-strength derivative submodules

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Lorentz.Invariants

namespace IsGaugeSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      F massWeightPoly)

/-!

## A. The field-strength symbols

At the centre each of the three sums of `repLorentz_F` is a sum against a row of the identity
matrix, so each collapses to its diagonal term and the symbol is returned unchanged.

-/

include h in
/-- A field-strength symbol is fixed by the centre of `SL(2,ℂ)`: all of its indices mix by the
  Lorentz matrix, which is the identity there. -/
lemma repLorentz_neg_one_F {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) : repLorentz (-1) (F l μ ν φ) = F l μ ν φ := by
  rw [h.repLorentz_F (-1) n l μ ν φ, SL2C.toLorentzGroup_neg_one, Finset.sum_eq_single l]
  · simp [Matrix.one_apply]
  · intro p _ hp
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hp
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · simp
    · simp [hi]
  · simp

include h in
/-- The span of a field-strength symbol family carries the sign `+1`. -/
lemma span_range_F_le_centreEigenspace {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) :
    Submodule.span ℂ (Set.range (F l μ ν)) ≤ centreEigenspace repLorentz 1 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨φ, rfl⟩
  rw [SetLike.mem_coe, mem_centreEigenspace, h.repLorentz_neg_one_F l μ ν φ, one_smul]

/-!

## B. The field-strength derivative submodules

The derivative submodule is the join of the symbol spans over the derivative slots and the two
covector indices, and an eigenspace is closed under joins.

-/

include h in
/-- **The centre of `SL(2,ℂ)` acts on the field-strength derivative submodules by `+1`**, for
  any number of covariant derivatives: the field strength is of integer spin and every one of
  its indices is inert at the centre. -/
theorem derivSubmodule_le_centreEigenspace (n : ℕ) :
    h.derivSubmodule n ≤ centreEigenspace repLorentz 1 := by
  rw [derivSubmodule]
  exact iSup_le fun l => iSup_le fun μ => iSup_le fun ν =>
    h.span_range_F_le_centreEigenspace l μ ν

end IsGaugeSector

end StandardModel
