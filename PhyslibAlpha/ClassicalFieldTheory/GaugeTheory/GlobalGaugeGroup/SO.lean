/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU
/-!
# The global gauge group SO(n)

The special orthogonal group, as a global gauge group.

## i. Overview

The special orthogonal group `SO(n)` is the group of real orthogonal `n × n` matrices of
determinant one, the rotations of `ℝⁿ`. It appears as a gauge group in grand unified
theories, such as `SO(10)`. A global gauge group sits inside `GL(n, ℂ)`, and there `SO(n)`
is the group of real matrices in `SU(n)`. A real matrix `B` is unitary exactly when
`Bᵀ B = 1`, and has determinant one as a complex matrix exactly when it does as a real one.

The real matrices are the image of the entrywise embedding `ℝ → ℂ`. This embedding has the
entrywise real part as a continuous left inverse, so its image is closed, and the real
matrices in `SU(n)` form a closed submonoid. The conjugate transpose of a real matrix is its
transpose, again real, so the submonoid is closed under the conjugate transpose.

## ii. Key results

- `GlobalGaugeGroup.realSpecialOrthogonalGroup` : the real special orthogonal matrices, as
  complex matrices.
- `GlobalGaugeGroup.ofReal_mem_realSpecialOrthogonalGroup_iff` : a real matrix lies in it
  exactly when it is orthogonal of determinant one.
- `GlobalGaugeGroup.SO` : the global gauge group `SO(n)`.
- `GlobalGaugeGroup.mem_SO_iff` : an invertible matrix lies in `SO(n)` exactly when it is a
  real orthogonal matrix of determinant one.

## iii. Table of contents

- A. The real special orthogonal matrices
- B. Real matrices
- C. Membership in the real special orthogonal matrices
- D. The group SO(n)

## iv. References

* None.

-/

@[expose] public section

open Matrix Topology

namespace GlobalGaugeGroup

/-!

## A. The real special orthogonal matrices

-/

/-- The real orthogonal `n × n` matrices of determinant one, as complex matrices, the real
  matrices in `SU(n)`. -/
def realSpecialOrthogonalGroup (n : ℕ) : Submonoid (Matrix (Fin n) (Fin n) ℂ) :=
  specialUnitaryGroup (Fin n) ℂ ⊓
    (Complex.ofRealHom.mapMatrix : Matrix (Fin n) (Fin n) ℝ →+* _).range.toSubmonoid

/-!

## B. Real matrices

-/

/-- The entrywise embedding of real matrices into complex matrices is a closed embedding.
  The entrywise real part is a continuous left inverse. -/
lemma isClosedEmbedding_ofReal_mapMatrix (n : ℕ) :
    IsClosedEmbedding (Complex.ofRealHom.mapMatrix : Matrix (Fin n) (Fin n) ℝ →+* _) :=
  Function.LeftInverse.isClosedEmbedding (f := fun A => A.map Complex.re)
    (fun B => by ext i j; simp [RingHom.mapMatrix_apply])
    (continuous_id.matrix_map Complex.continuous_re)
    (continuous_id.matrix_map Complex.continuous_ofReal)

/-- The conjugate transpose of a real matrix is its transpose. -/
lemma star_ofReal_mapMatrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    star (Complex.ofRealHom.mapMatrix B) = Complex.ofRealHom.mapMatrix Bᵀ := by
  ext i j
  simp [RingHom.mapMatrix_apply, star_apply]

/-!

## C. Membership in the real special orthogonal matrices

-/

/-- A complex matrix is a real special orthogonal matrix exactly when it is special unitary and
  the entrywise embedding of a real matrix. -/
lemma mem_realSpecialOrthogonalGroup_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} :
    A ∈ realSpecialOrthogonalGroup n ↔
      A ∈ specialUnitaryGroup (Fin n) ℂ ∧ ∃ B : Matrix (Fin n) (Fin n) ℝ,
        Complex.ofRealHom.mapMatrix B = A :=
  Iff.rfl

/-- A real matrix lies in the real special orthogonal matrices exactly when it is
  orthogonal, `Bᵀ B = 1`, of determinant one. -/
lemma ofReal_mem_realSpecialOrthogonalGroup_iff {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    Complex.ofRealHom.mapMatrix B ∈ realSpecialOrthogonalGroup n ↔
      Bᵀ * B = 1 ∧ B.det = 1 := by
  have hinj := (isClosedEmbedding_ofReal_mapMatrix n).injective
  rw [mem_realSpecialOrthogonalGroup_iff, mem_specialUnitaryGroup_iff,
    mem_unitaryGroup_iff', star_ofReal_mapMatrix, ← map_mul, ← RingHom.map_det,
    ← map_one Complex.ofRealHom.mapMatrix, hinj.eq_iff, ← map_one Complex.ofRealHom,
    (Complex.ofRealHom.injective).eq_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, B, rfl⟩⟩

/-- The real special orthogonal matrices form a closed set. -/
lemma isClosed_realSpecialOrthogonalGroup (n : ℕ) :
    IsClosed (realSpecialOrthogonalGroup n : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  rw [realSpecialOrthogonalGroup, Submonoid.coe_inf]
  exact (isClosed_specialUnitaryGroup n).inter
    (isClosedEmbedding_ofReal_mapMatrix n).isClosed_range

/-- The conjugate transpose of a real special orthogonal matrix is real special
  orthogonal. -/
lemma star_mem_realSpecialOrthogonalGroup {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ realSpecialOrthogonalGroup n) : star A ∈ realSpecialOrthogonalGroup n := by
  obtain ⟨hSU, B, rfl⟩ := mem_realSpecialOrthogonalGroup_iff.1 hA
  refine ⟨(star (⟨_, hSU⟩ : specialUnitaryGroup (Fin n) ℂ)).2, Bᵀ, ?_⟩
  exact (star_ofReal_mapMatrix B).symm

/-!

## D. The group SO(n)

-/

/-- The global gauge group `SO(n)`, the real orthogonal `n × n` matrices of determinant one,
  as complex matrices. -/
def SO (n : ℕ) : GlobalGaugeGroup (Fin n) :=
  ofSubmonoid (realSpecialOrthogonalGroup n) (isClosed_realSpecialOrthogonalGroup n)

/-- An invertible matrix lies in `SO(n)` exactly when it is a real orthogonal matrix of
  determinant one. -/
lemma mem_SO_iff {n : ℕ} {g : GeneralLinearGroup (Fin n) ℂ} :
    g ∈ (SO n).group ↔ ∃ B : Matrix (Fin n) (Fin n) ℝ,
      Bᵀ * B = 1 ∧ B.det = 1 ∧ Complex.ofRealHom.mapMatrix B = g := by
  rw [SO, mem_ofSubmonoid_iff_of_star_mem (S := realSpecialOrthogonalGroup n)
    (fun _ hA => hA.1.1) fun _ => star_mem_realSpecialOrthogonalGroup]
  refine ⟨fun h => ?_, fun ⟨B, hB, hdet, hBg⟩ => ?_⟩
  · obtain ⟨B, hBg⟩ := (mem_realSpecialOrthogonalGroup_iff.1 h).2
    rw [← hBg, ofReal_mem_realSpecialOrthogonalGroup_iff] at h
    exact ⟨B, h.1, h.2, hBg⟩
  · rw [← hBg, ofReal_mem_realSpecialOrthogonalGroup_iff]
    exact ⟨hB, hdet⟩

end GlobalGaugeGroup
