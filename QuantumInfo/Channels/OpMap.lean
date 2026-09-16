/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Channels.Unbundled

/-! # Linear maps of operators

A quantum channel is a linear map taking operators on one Hilbert space to operators on another.
This file introduces `OpMap E F`, the basis-free counterpart of `MatrixMap`, together with the
properties a channel can have: `IsTracePreserving`, `Unital`, `IsHermitianPreserving`,
`IsPositive`, and `IsCompletelyPositive`.

The first four are stated directly on operators. Complete positivity is the exception: it is
defined through the matrix representation, because the Choi matrix and the ampliation
`Φ ⊗ id` are matrix constructions. `OpMap.isCompletelyPositiveOf_congr` shows that the resulting
notion does not depend on the choice of orthonormal bases, which is what makes the definition
legitimate.

`OpMap.toMatOf` produces the matrix map in given orthonormal bases, and `OpMap.toMat` the one in
the preferred bases of a `StdBasis` instance. The `*_toMatOf_iff` and `*_toMat_iff` lemmas transfer
each property in both directions, so that a matrix-level fact about a channel and its
operator-level counterpart are interchangeable.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder

/-- An `OpMap` is a linear map from operators on `E` to operators on `F`. This is the basis-free
form of `MatrixMap`; `OpMap.toMat` recovers the matrix map in the preferred bases. -/
abbrev OpMap (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :=
  (E →L[ℂ] E) →ₗ[ℂ] (F →L[ℂ] F)

namespace OpMap

variable {E F G ι κ ν ι' κ' : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

section Defs

/-- An operator map is *trace preserving* if the trace of the output always equals the trace of
the input. -/
def IsTracePreserving (Φ : OpMap E F) : Prop :=
  ∀ A : E →L[ℂ] E, LinearMap.trace ℂ F ↑(Φ A) = LinearMap.trace ℂ E ↑A

/-- An operator map is *unital* if it preserves the identity. -/
def Unital (Φ : OpMap E F) : Prop :=
  Φ 1 = 1

/-- An operator map is *Hermitian preserving* if it maps self-adjoint operators to self-adjoint
operators. -/
def IsHermitianPreserving (Φ : OpMap E F) : Prop :=
  ∀ ⦃A : E →L[ℂ] E⦄, IsSelfAdjoint A → IsSelfAdjoint (Φ A)

/-- An operator map is *positive* if it maps positive operators to positive operators. -/
def IsPositive (Φ : OpMap E F) : Prop :=
  ∀ ⦃A : E →L[ℂ] E⦄, 0 ≤ A → 0 ≤ Φ A

end Defs

section Closure

variable {Φ : OpMap E F} {Ψ : OpMap F G}

theorem isTracePreserving_id : IsTracePreserving (LinearMap.id : OpMap E E) :=
  fun _ ↦ rfl

theorem IsTracePreserving.comp (hΦ : Φ.IsTracePreserving) (hΨ : Ψ.IsTracePreserving) :
    IsTracePreserving (Ψ ∘ₗ Φ) :=
  fun A ↦ (hΨ (Φ A)).trans (hΦ A)

theorem unital_id : Unital (LinearMap.id : OpMap E E) :=
  rfl

theorem Unital.comp (hΦ : Φ.Unital) (hΨ : Ψ.Unital) : Unital (Ψ ∘ₗ Φ) := by
  rw [Unital, LinearMap.comp_apply, hΦ, hΨ]

theorem isHermitianPreserving_id : IsHermitianPreserving (LinearMap.id : OpMap E E) :=
  fun _ h ↦ h

theorem IsHermitianPreserving.comp (hΦ : Φ.IsHermitianPreserving)
    (hΨ : Ψ.IsHermitianPreserving) : IsHermitianPreserving (Ψ ∘ₗ Φ) :=
  fun _ h ↦ hΨ (hΦ h)

theorem isPositive_id : IsPositive (LinearMap.id : OpMap E E) :=
  fun _ h ↦ h

theorem IsPositive.comp (hΦ : Φ.IsPositive) (hΨ : Ψ.IsPositive) : IsPositive (Ψ ∘ₗ Φ) :=
  fun _ h ↦ hΨ (hΦ h)

end Closure

section ToMatOf

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
variable [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']

/-- The linear equivalence between operator maps and matrix maps determined by given orthonormal
bases of the source and target. -/
def matEquivOf (bE : OrthonormalBasis ι ℂ E) (bF : OrthonormalBasis κ ℂ F) :
    OpMap E F ≃ₗ[ℂ] MatrixMap ι κ ℂ :=
  LinearEquiv.arrowCongr (StdBasis.toMatOf bE).toAlgEquiv.toLinearEquiv
    (StdBasis.toMatOf bF).toAlgEquiv.toLinearEquiv

/-- The matrix map representing an operator map in given orthonormal bases. -/
def toMatOf (bE : OrthonormalBasis ι ℂ E) (bF : OrthonormalBasis κ ℂ F) (Φ : OpMap E F) :
    MatrixMap ι κ ℂ :=
  matEquivOf bE bF Φ

theorem toMatOf_apply (bE : OrthonormalBasis ι ℂ E) (bF : OrthonormalBasis κ ℂ F) (Φ : OpMap E F)
    (M : Matrix ι ι ℂ) :
    toMatOf bE bF Φ M = StdBasis.toMatOf bF (Φ ((StdBasis.toMatOf bE).symm M)) :=
  rfl

@[simp]
theorem toMatOf_apply_toMatOf (bE : OrthonormalBasis ι ℂ E) (bF : OrthonormalBasis κ ℂ F)
    (Φ : OpMap E F) (A : E →L[ℂ] E) :
    toMatOf bE bF Φ (StdBasis.toMatOf bE A) = StdBasis.toMatOf bF (Φ A) := by
  rw [toMatOf_apply, StarAlgEquiv.symm_apply_apply]

theorem toMatOf_injective (bE : OrthonormalBasis ι ℂ E) (bF : OrthonormalBasis κ ℂ F) :
    Function.Injective (toMatOf bE bF) :=
  (matEquivOf bE bF).injective

@[simp]
theorem toMatOf_id (bE : OrthonormalBasis ι ℂ E) :
    toMatOf bE bE (LinearMap.id : OpMap E E) = MatrixMap.id ι ℂ := by
  refine LinearMap.ext fun M ↦ ?_
  rw [toMatOf_apply]
  simp [MatrixMap.id]

theorem toMatOf_comp (bE : OrthonormalBasis ι ℂ E) (bF : OrthonormalBasis κ ℂ F)
    (bG : OrthonormalBasis ν ℂ G) (Φ : OpMap E F) (Ψ : OpMap F G) :
    toMatOf bE bG (Ψ ∘ₗ Φ) = toMatOf bF bG Ψ ∘ₗ toMatOf bE bF Φ := by
  refine LinearMap.ext fun M ↦ ?_
  rw [LinearMap.comp_apply, toMatOf_apply, toMatOf_apply, toMatOf_apply,
    StarAlgEquiv.symm_apply_apply]
  rfl

/-- Changing the orthonormal bases conjugates the matrix representation of an operator map by a
unitary on either side. -/
theorem toMatOf_congr (bE bE' : OrthonormalBasis ι ℂ E) (bF bF' : OrthonormalBasis κ ℂ F)
    (Φ : OpMap E F) :
    toMatOf bE' bF' Φ =
      MatrixMap.conj (star (StdBasis.changeOfBasis bF bF') : Matrix κ κ ℂ) ∘ₗ
        toMatOf bE bF Φ ∘ₗ
        MatrixMap.conj (StdBasis.changeOfBasis bE bE' : Matrix ι ι ℂ) := by
  have : FiniteDimensional ℂ E := Module.Basis.finiteDimensional_of_finite bE.toBasis
  have : FiniteDimensional ℂ F := Module.Basis.finiteDimensional_of_finite bF.toBasis
  refine LinearMap.ext fun M ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, MatrixMap.conj_apply, MatrixMap.conj_apply,
    toMatOf_apply, toMatOf_apply, StdBasis.toMatOf_symm_conj bE bE',
    StdBasis.toMatOf_conj bF bF']
  simp [Matrix.star_eq_conjTranspose]

/-- Relabelling the index types of the bases relabels the matrix representation. -/
theorem toMatOf_reindex (bE : OrthonormalBasis ι ℂ E) (bF : OrthonormalBasis κ ℂ F)
    (e : ι ≃ ι') (f : κ ≃ κ') (Φ : OpMap E F) :
    toMatOf (bE.reindex e) (bF.reindex f) Φ =
      MatrixMap.submatrix ℂ f.symm ∘ₗ toMatOf bE bF Φ ∘ₗ MatrixMap.submatrix ℂ e := by
  have : FiniteDimensional ℂ E := Module.Basis.finiteDimensional_of_finite bE.toBasis
  have : FiniteDimensional ℂ F := Module.Basis.finiteDimensional_of_finite bF.toBasis
  refine LinearMap.ext fun M ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, toMatOf_apply, toMatOf_apply,
    StdBasis.toMatOf_symm_reindex, StdBasis.toMatOf_reindex]
  rfl

end ToMatOf

section TransferOf

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (bE : OrthonormalBasis ι ℂ E) (bF : OrthonormalBasis κ ℂ F)

@[simp]
theorem isTracePreserving_toMatOf_iff [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (Φ : OpMap E F) : (toMatOf bE bF Φ).IsTracePreserving ↔ Φ.IsTracePreserving := by
  constructor
  · intro h A
    have := h (StdBasis.toMatOf bE A)
    rwa [toMatOf_apply_toMatOf, StdBasis.trace_toMatOf, StdBasis.trace_toMatOf] at this
  · intro h M
    rw [toMatOf_apply, StdBasis.trace_toMatOf, h, ← StdBasis.trace_toMatOf bE,
      StarAlgEquiv.apply_symm_apply]

@[simp]
theorem unital_toMatOf_iff (Φ : OpMap E F) : (toMatOf bE bF Φ).Unital ↔ Φ.Unital := by
  rw [MatrixMap.Unital, Unital, toMatOf_apply]
  rw [show (1 : Matrix ι ι ℂ) = StdBasis.toMatOf bE 1 by simp, StarAlgEquiv.symm_apply_apply]
  simp

@[simp]
theorem isHermitianPreserving_toMatOf_iff (Φ : OpMap E F) :
    (toMatOf bE bF Φ).IsHermitianPreserving ↔ Φ.IsHermitianPreserving := by
  constructor
  · intro h A hA
    rw [← StdBasis.isHermitian_toMatOf_iff bF, ← toMatOf_apply_toMatOf bE]
    exact h ((StdBasis.isHermitian_toMatOf_iff bE A).mpr hA)
  · intro h M hM
    rw [toMatOf_apply, StdBasis.isHermitian_toMatOf_iff]
    exact h ((StdBasis.isHermitian_toMatOf_iff bE _).mp (by rwa [StarAlgEquiv.apply_symm_apply]))

@[simp]
theorem isPositive_toMatOf_iff (Φ : OpMap E F) :
    (toMatOf bE bF Φ).IsPositive ↔ Φ.IsPositive := by
  constructor
  · intro h A hA
    rw [← StdBasis.posSemidef_toMatOf_iff_nonneg bF, ← toMatOf_apply_toMatOf bE]
    exact h ((StdBasis.posSemidef_toMatOf_iff_nonneg bE A).mpr hA)
  · intro h M hM
    rw [toMatOf_apply, StdBasis.posSemidef_toMatOf_iff_nonneg]
    exact h ((StdBasis.posSemidef_toMatOf_iff_nonneg bE _).mp
      (by rwa [StarAlgEquiv.apply_symm_apply]))

end TransferOf

section CompletelyPositive

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
variable [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']

/-- An operator map is *completely positive relative to given orthonormal bases* if its matrix
representation in those bases is completely positive. By `OpMap.isCompletelyPositiveOf_congr` the
bases do not matter, so `OpMap.IsCompletelyPositive` is the notion to use. -/
def IsCompletelyPositiveOf (bE : OrthonormalBasis ι ℂ E) (bF : OrthonormalBasis κ ℂ F)
    (Φ : OpMap E F) : Prop :=
  (toMatOf bE bF Φ).IsCompletelyPositive

theorem IsCompletelyPositiveOf.reindex {bE : OrthonormalBasis ι ℂ E}
    {bF : OrthonormalBasis κ ℂ F} {Φ : OpMap E F} (h : IsCompletelyPositiveOf bE bF Φ)
    (e : ι ≃ ι') (f : κ ≃ κ') : IsCompletelyPositiveOf (bE.reindex e) (bF.reindex f) Φ := by
  rw [IsCompletelyPositiveOf, toMatOf_reindex]
  exact ((MatrixMap.IsCompletelyPositive.submatrix _).comp h).comp
    (MatrixMap.IsCompletelyPositive.submatrix _)

/-- Complete positivity is unchanged by relabelling the index types of the bases. -/
theorem isCompletelyPositiveOf_reindex (bE : OrthonormalBasis ι ℂ E)
    (bF : OrthonormalBasis κ ℂ F) (e : ι ≃ ι') (f : κ ≃ κ') (Φ : OpMap E F) :
    IsCompletelyPositiveOf (bE.reindex e) (bF.reindex f) Φ ↔ IsCompletelyPositiveOf bE bF Φ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.reindex e f⟩
  have h2 := h.reindex e.symm f.symm
  rwa [OrthonormalBasis.reindex_reindex_symm, OrthonormalBasis.reindex_reindex_symm] at h2

/-- **Complete positivity does not depend on the choice of orthonormal bases**, not even on the
types indexing them. -/
theorem isCompletelyPositiveOf_congr (bE : OrthonormalBasis ι ℂ E) (bE' : OrthonormalBasis ι' ℂ E)
    (bF : OrthonormalBasis κ ℂ F) (bF' : OrthonormalBasis κ' ℂ F) (Φ : OpMap E F) :
    IsCompletelyPositiveOf bE' bF' Φ ↔ IsCompletelyPositiveOf bE bF Φ := by
  have hE : Fintype.card ι = Fintype.card ι' := by
    rw [← Module.finrank_eq_card_basis bE.toBasis, ← Module.finrank_eq_card_basis bE'.toBasis]
  have hF : Fintype.card κ = Fintype.card κ' := by
    rw [← Module.finrank_eq_card_basis bF.toBasis, ← Module.finrank_eq_card_basis bF'.toBasis]
  obtain ⟨e⟩ : Nonempty (ι ≃ ι') := ⟨Fintype.equivOfCardEq hE⟩
  obtain ⟨f⟩ : Nonempty (κ ≃ κ') := ⟨Fintype.equivOfCardEq hF⟩
  rw [← isCompletelyPositiveOf_reindex bE bF e f]
  have key : ∀ (cE cE' : OrthonormalBasis ι' ℂ E) (cF cF' : OrthonormalBasis κ' ℂ F),
      IsCompletelyPositiveOf cE cF Φ → IsCompletelyPositiveOf cE' cF' Φ := by
    intro cE cE' cF cF' h
    rw [IsCompletelyPositiveOf, toMatOf_congr cE cE' cF cF']
    exact ((MatrixMap.congruence_CP _).comp h).comp (MatrixMap.congruence_CP _)
  exact ⟨key _ _ _ _, key _ _ _ _⟩

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]

/-- An operator map is *completely positive* if its matrix representation is.

Unlike the other properties of an `OpMap`, this one has to be stated through a matrix
representation, because the ampliation `Φ ⊗ id` used to define complete positivity is a matrix
construction. The basis used is immaterial: `OpMap.isCompletelyPositive_iff_of` says that any
orthonormal bases, indexed by any types, give the same answer. -/
def IsCompletelyPositive (Φ : OpMap E F) : Prop :=
  IsCompletelyPositiveOf (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ F) Φ

/-- Complete positivity may be checked in any pair of orthonormal bases. -/
theorem isCompletelyPositive_iff_of (bE : OrthonormalBasis ι ℂ E) (bF : OrthonormalBasis κ ℂ F)
    (Φ : OpMap E F) : Φ.IsCompletelyPositive ↔ IsCompletelyPositiveOf bE bF Φ :=
  isCompletelyPositiveOf_congr bE (stdOrthonormalBasis ℂ E) bF (stdOrthonormalBasis ℂ F) Φ

@[simp]
theorem isCompletelyPositive_toMatOf_iff (bE : OrthonormalBasis ι ℂ E)
    (bF : OrthonormalBasis κ ℂ F) (Φ : OpMap E F) :
    (toMatOf bE bF Φ).IsCompletelyPositive ↔ Φ.IsCompletelyPositive :=
  (isCompletelyPositive_iff_of bE bF Φ).symm

theorem IsCompletelyPositive.isPositive {Φ : OpMap E F} (h : Φ.IsCompletelyPositive) :
    Φ.IsPositive :=
  (isPositive_toMatOf_iff (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ F) Φ).mp
    (MatrixMap.IsCompletelyPositive.IsPositive h)

theorem IsPositive.isHermitianPreserving {Φ : OpMap E F} (h : Φ.IsPositive) :
    Φ.IsHermitianPreserving :=
  (isHermitianPreserving_toMatOf_iff (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ F) Φ).mp
    ((isPositive_toMatOf_iff _ _ Φ).mpr h).IsHermitianPreserving

theorem IsCompletelyPositive.isHermitianPreserving {Φ : OpMap E F} (h : Φ.IsCompletelyPositive) :
    Φ.IsHermitianPreserving :=
  h.isPositive.isHermitianPreserving

theorem IsCompletelyPositive.comp {Φ : OpMap E F} {Ψ : OpMap F G} (hΦ : Φ.IsCompletelyPositive)
    (hΨ : Ψ.IsCompletelyPositive) : IsCompletelyPositive (Ψ ∘ₗ Φ) := by
  rw [isCompletelyPositive_iff_of (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ G),
    IsCompletelyPositiveOf, toMatOf_comp _ (stdOrthonormalBasis ℂ F)]
  exact MatrixMap.IsCompletelyPositive.comp
    ((isCompletelyPositive_iff_of _ _ Φ).mp hΦ) ((isCompletelyPositive_iff_of _ _ Ψ).mp hΨ)

theorem isCompletelyPositive_id : IsCompletelyPositive (LinearMap.id : OpMap E E) := by
  show IsCompletelyPositiveOf (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ E) _
  rw [IsCompletelyPositiveOf, toMatOf_id]
  exact MatrixMap.IsCompletelyPositive.id (A := Fin (Module.finrank ℂ E)) (R := ℂ)

end CompletelyPositive

section Preferred

variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]
variable [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ]
variable [Fintype ν] [DecidableEq ν] [StdBasis ℂ G ν]

variable (E F ι κ) in
/-- The linear equivalence between operator maps and matrix maps determined by the preferred bases
of the source and target. -/
def matEquiv : OpMap E F ≃ₗ[ℂ] MatrixMap ι κ ℂ :=
  matEquivOf stdBasis stdBasis

/-- The matrix map representing an operator map in the preferred bases. -/
def toMat (Φ : OpMap E F) : MatrixMap ι κ ℂ :=
  matEquiv E F ι κ Φ

variable (E F) in
/-- The operator map with a given matrix in the preferred bases. -/
def ofMat (M : MatrixMap ι κ ℂ) : OpMap E F :=
  (matEquiv E F ι κ).symm M

@[simp]
theorem toMat_ofMat (M : MatrixMap ι κ ℂ) : toMat (ofMat E F M) = M :=
  (matEquiv E F ι κ).apply_symm_apply M

@[simp]
theorem ofMat_toMat (Φ : OpMap E F) : ofMat E F (toMat (ι := ι) (κ := κ) Φ) = Φ :=
  (matEquiv E F ι κ).symm_apply_apply Φ

theorem toMat_eq_toMatOf (Φ : OpMap E F) :
    toMat (ι := ι) (κ := κ) Φ = toMatOf stdBasis stdBasis Φ :=
  rfl

theorem toMat_apply (Φ : OpMap E F) (M : Matrix ι ι ℂ) :
    toMat (κ := κ) Φ M = StdBasis.toMat ℂ F κ (Φ ((StdBasis.toMat ℂ E ι).symm M)) :=
  rfl

@[simp]
theorem toMat_apply_toMat (Φ : OpMap E F) (A : E →L[ℂ] E) :
    toMat (ι := ι) (κ := κ) Φ (StdBasis.toMat ℂ E ι A) = StdBasis.toMat ℂ F κ (Φ A) :=
  toMatOf_apply_toMatOf _ _ Φ A

theorem toMat_injective : Function.Injective (toMat (E := E) (F := F) (ι := ι) (κ := κ)) :=
  (matEquiv E F ι κ).injective

@[simp]
theorem toMat_id : toMat (ι := ι) (κ := ι) (LinearMap.id : OpMap E E) = MatrixMap.id ι ℂ :=
  toMatOf_id _

theorem toMat_comp (Φ : OpMap E F) (Ψ : OpMap F G) :
    toMat (ι := ι) (κ := ν) (Ψ ∘ₗ Φ) = toMat (ι := κ) (κ := ν) Ψ ∘ₗ toMat (ι := ι) (κ := κ) Φ :=
  toMatOf_comp _ _ _ Φ Ψ

@[simp]
theorem isTracePreserving_toMat_iff (Φ : OpMap E F) :
    (toMat (ι := ι) (κ := κ) Φ).IsTracePreserving ↔ Φ.IsTracePreserving :=
  isTracePreserving_toMatOf_iff _ _ Φ

@[simp]
theorem unital_toMat_iff (Φ : OpMap E F) : (toMat (ι := ι) (κ := κ) Φ).Unital ↔ Φ.Unital :=
  unital_toMatOf_iff _ _ Φ

@[simp]
theorem isHermitianPreserving_toMat_iff (Φ : OpMap E F) :
    (toMat (ι := ι) (κ := κ) Φ).IsHermitianPreserving ↔ Φ.IsHermitianPreserving :=
  isHermitianPreserving_toMatOf_iff _ _ Φ

@[simp]
theorem isPositive_toMat_iff (Φ : OpMap E F) :
    (toMat (ι := ι) (κ := κ) Φ).IsPositive ↔ Φ.IsPositive :=
  isPositive_toMatOf_iff _ _ Φ

@[simp]
theorem isCompletelyPositive_toMat_iff (Φ : OpMap E F) :
    (toMat (ι := ι) (κ := κ) Φ).IsCompletelyPositive ↔ Φ.IsCompletelyPositive :=
  isCompletelyPositive_toMatOf_iff _ _ Φ

end Preferred

end OpMap
