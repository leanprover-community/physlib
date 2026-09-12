/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Preferred orthonormal bases

Quantum information theory is usually written down twice: once in a basis-free language of
operators on a Hilbert space, and once in the language of matrices. The two are equivalent, but
only after a choice of orthonormal basis, and a handful of notions -- computational-basis states,
Pauli and Clifford operators, controlled gates, stabilizer entropies -- are genuinely defined
*relative to* such a choice.

This file introduces `StdBasis 𝕜 E ι`, a class carrying a preferred `OrthonormalBasis ι 𝕜 E`, so
that the choice can be propagated by typeclass inference instead of being threaded through every
definition by hand. Since `OrthonormalBasis ι 𝕜 E` unfolds to a `LinearIsometryEquiv` onto
`EuclideanSpace 𝕜 ι`, an instance of `StdBasis 𝕜 E ι` is exactly the data identifying `E` with a
labelled copy of `EuclideanSpace 𝕜 ι`.

## Main definitions

* `StdBasis 𝕜 E ι`: the class of a preferred orthonormal basis of `E` indexed by `ι`.
* `StdBasis.toMatOf`: the ⋆-algebra equivalence `(E →L[𝕜] E) ≃⋆ₐ[𝕜] Matrix ι ι 𝕜` determined by an
  explicit orthonormal basis.
* `StdBasis.toMat`: the same, using the preferred basis.
* `StdBasis.toMatUnitary`, `StdBasis.unitaryOfMat`: the resulting bijection between unitary
  operators on `E` and unitary matrices indexed by `ι`.
* `StdBasis.changeOfBasis`: the unitary matrix relating the matrices of an operator in two
  different orthonormal bases.

## Main results

* `StdBasis.toMatOf_conj`: changing the orthonormal basis conjugates the matrix by a unitary.
* `StdBasis.congr_of_unitaryInvariant`: any quantity computed from the matrix of an operator that
  is invariant under unitary conjugation does not depend on the choice of orthonormal basis. This
  is the workhorse for showing that a matrix-level definition descends to operators.
* `StdBasis.posSemidef_toMatOf_iff`, `StdBasis.trace_toMatOf`: the matrix positivity and trace
  agree with their basis-free counterparts.

## Design notes

The basis is required to be *orthonormal* rather than a bare `Module.Basis`. This is not a
convenience: with a bare basis the change-of-basis matrix ranges over all of `GL`, and the
quantities of interest in quantum information (eigenvalues, entropies, Schatten norms, positivity)
are *not* invariant under general similarity. Orthonormality is exactly what makes the
change-of-basis matrix unitary, and it is also what makes `E →L[𝕜] E ≃ Matrix ι ι 𝕜` a
⋆-isomorphism rather than merely an algebra isomorphism, so that adjoints, self-adjointness,
unitarity, spectra and the continuous functional calculus all transport.

The index type `ι` is an `outParam`: a type carries at most one preferred basis, and the index type
is part of that choice. Consequently `StdBasis.reindex` and `StdBasis.transport` are *definitions*
rather than instances; making them instances would both loop and silently install non-canonical
bases.
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace Matrix TensorProduct

/-- A preferred orthonormal basis of `E`, indexed by `ι`.

This is the data used by notions that are genuinely basis-dependent (computational-basis states,
Pauli operators, controlled gates), and by the matrix representation of operators on `E`. -/
class StdBasis (𝕜 : Type*) (E : Type*) (ι : outParam Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] where
  /-- The preferred orthonormal basis. -/
  stdBasis : OrthonormalBasis ι 𝕜 E

export StdBasis (stdBasis)

namespace OrthonormalBasis

variable {𝕜 E ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [Fintype ι] [Fintype κ]

@[simp]
theorem reindex_reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ κ) {ν : Type*} [Fintype ν]
    (f : κ ≃ ν) : (b.reindex e).reindex f = b.reindex (e.trans f) :=
  DFunLike.ext _ _ fun _ ↦ by simp

@[simp]
theorem reindex_refl (b : OrthonormalBasis ι 𝕜 E) : b.reindex (Equiv.refl ι) = b :=
  DFunLike.ext _ _ fun _ ↦ by simp

theorem reindex_reindex_symm (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e).reindex e.symm = b := by
  simp

end OrthonormalBasis

/-- The standard basis of `EuclideanSpace 𝕜 d` is `EuclideanSpace.basisFun`. This is the instance
that makes existing matrix-indexed definitions a special case of the abstract ones. -/
noncomputable instance EuclideanSpace.instStdBasis (𝕜 : Type*) [RCLike 𝕜] (d : Type*)
    [Fintype d] : StdBasis 𝕜 (EuclideanSpace 𝕜 d) d where
  stdBasis := EuclideanSpace.basisFun d 𝕜

namespace StdBasis

variable {𝕜 E F ι κ : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

section Instances

variable [Fintype ι] [Fintype κ]

/-- A space with a preferred (necessarily finite) orthonormal basis is finite-dimensional. -/
instance (priority := 100) toFiniteDimensional [StdBasis 𝕜 E ι] : FiniteDimensional 𝕜 E :=
  Module.Basis.finiteDimensional_of_finite (stdBasis (𝕜 := 𝕜) (E := E) (ι := ι)).toBasis

/-- A space with a preferred orthonormal basis is complete.

Mathlib keeps `FiniteDimensional.complete` a theorem rather than an instance because the scalar
field cannot be recovered from the goal `CompleteSpace E`. Here it can: a `StdBasis 𝕜 E ι` instance
pins down `𝕜`, so the search terminates. Having this available means the operator ⋆-algebra
structure on `E →L[𝕜] E` -- adjoints, the continuous functional calculus, `StdBasis.toMat` -- is
usable from a `StdBasis` instance alone, without carrying `[CompleteSpace E]` in every signature. -/
instance (priority := 100) toCompleteSpace [StdBasis 𝕜 E ι] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E

/-- A finite-dimensional complex normed space is complete.

Mathlib registers `FiniteDimensional.proper` as an instance only for `𝕜 = ℝ`, so a space that is
finite-dimensional over `ℂ` -- but not known to be a `ℝ`-normed space -- does not pick up
completeness by inference. Registering it here means `[FiniteDimensional ℂ E]` alone is enough to
use the operator ⋆-algebra on `E →L[ℂ] E`, and `[CompleteSpace E]` never has to appear next to it.
`CompleteSpace` is a `Prop`, so the extra route to it creates no diamond. -/
instance (priority := 100) _root_.FiniteDimensional.toCompleteSpaceComplex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] : CompleteSpace E :=
  FiniteDimensional.complete ℂ E

/-- A tensor product of finite-dimensional inner product spaces is complete. This is needed for the
`StdBasis` instance on a tensor product to be usable, since the operator ⋆-algebra structure on
`E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F` requires completeness. -/
instance _root_.TensorProduct.instCompleteSpaceOfFiniteDimensional
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] : CompleteSpace (E ⊗[𝕜] F) :=
  FiniteDimensional.complete 𝕜 _

/-- The preferred basis of a tensor product is the tensor product of the preferred bases, indexed
by the product of the index types. -/
noncomputable instance instTensorProduct [StdBasis 𝕜 E ι] [StdBasis 𝕜 F κ] :
    StdBasis 𝕜 (E ⊗[𝕜] F) (ι × κ) where
  stdBasis := (stdBasis (𝕜 := 𝕜) (E := E)).tensorProduct (stdBasis (𝕜 := 𝕜) (E := F))

@[simp]
theorem stdBasis_euclideanSpace (d : Type*) [Fintype d] :
    stdBasis (𝕜 := 𝕜) (E := EuclideanSpace 𝕜 d) = EuclideanSpace.basisFun d 𝕜 :=
  rfl

@[simp]
theorem stdBasis_tensorProduct [StdBasis 𝕜 E ι] [StdBasis 𝕜 F κ] :
    stdBasis (𝕜 := 𝕜) (E := E ⊗[𝕜] F) =
      (stdBasis (𝕜 := 𝕜) (E := E)).tensorProduct (stdBasis (𝕜 := 𝕜) (E := F)) :=
  rfl

/-- Relabel the preferred basis of `E` along an equivalence of index types.

This is deliberately not an instance: a type has at most one preferred basis, and there is no
canonical `ι ≃ κ` to relabel along. -/
@[instance_reducible]
noncomputable def reindex [StdBasis 𝕜 E ι] (e : ι ≃ κ) : StdBasis 𝕜 E κ :=
  ⟨(stdBasis (𝕜 := 𝕜) (E := E)).reindex e⟩

/-- Transport the preferred basis of `E` to `F` along a linear isometry equivalence.

This is deliberately not an instance, for the same reason as `StdBasis.reindex`. -/
@[instance_reducible]
noncomputable def transport [StdBasis 𝕜 E ι] (f : E ≃ₗᵢ[𝕜] F) : StdBasis 𝕜 F ι :=
  ⟨(stdBasis (𝕜 := 𝕜) (E := E)).map f⟩

/-- An arbitrary preferred basis on a finite-dimensional space, indexed by `Fin (finrank 𝕜 E)`.

This is deliberately not an instance: a space that already has a preferred basis must not silently
acquire a second one. It is meant to be introduced locally (`let _ := StdBasis.some 𝕜 E`) inside
the proof of a basis-free statement, so that the statement can be discharged by its matrix
analogue. -/
@[instance_reducible]
noncomputable def some (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] : StdBasis 𝕜 E (Fin (Module.finrank 𝕜 E)) :=
  ⟨stdOrthonormalBasis 𝕜 E⟩

end Instances

section ToMat

variable [Fintype ι] [DecidableEq ι] [CompleteSpace E]

/-- The matrix of an operator in a given orthonormal basis, as a ⋆-algebra equivalence.

Because this is an equivalence of ⋆-algebras, it automatically transports products, adjoints,
self-adjointness, unitarity, spectra, and the continuous functional calculus. -/
noncomputable def toMatOf (b : OrthonormalBasis ι 𝕜 E) : (E →L[𝕜] E) ≃⋆ₐ[𝕜] Matrix ι ι 𝕜 :=
  b.repr.conjStarAlgEquiv.trans (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)).symm

/-- The matrix of an operator in the preferred basis of `E`. -/
noncomputable def toMat (𝕜 E ι : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι] [StdBasis 𝕜 E ι] :
    (E →L[𝕜] E) ≃⋆ₐ[𝕜] Matrix ι ι 𝕜 :=
  toMatOf (stdBasis (𝕜 := 𝕜) (E := E))

theorem toMat_def [StdBasis 𝕜 E ι] : toMat 𝕜 E ι = toMatOf (stdBasis (𝕜 := 𝕜) (E := E)) :=
  rfl

/-- `StdBasis.toMat` for the basis provided by an explicitly given instance is `toMatOf` of that
basis. This lets statements about a *change of instance* be reduced to statements about a change of
orthonormal basis. -/
theorem toMat_mk (b : OrthonormalBasis ι 𝕜 E) :
    @toMat 𝕜 E ι _ _ _ _ _ ⟨b⟩ = toMatOf b :=
  rfl

@[simp]
theorem toMatOf_apply (b : OrthonormalBasis ι 𝕜 E) (A : E →L[𝕜] E) (i j : ι) :
    toMatOf b A i j = ⟪b i, A (b j)⟫_𝕜 := by
  show LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun ι 𝕜)
    ((b.repr.conjStarAlgEquiv A : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) :
      EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) i j = _
  rw [LinearMap.toMatrixOrthonormal_apply_apply]
  simp only [ContinuousLinearMap.coe_coe, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    EuclideanSpace.basisFun_apply, OrthonormalBasis.repr_symm_single]
  rw [← b.repr_self i, LinearIsometryEquiv.inner_map_map]

variable [FiniteDimensional 𝕜 E]

/-- `StdBasis.toMatOf` agrees with Mathlib's `LinearMap.toMatrixOrthonormal`. -/
theorem toMatOf_eq_toMatrixOrthonormal (b : OrthonormalBasis ι 𝕜 E) (A : E →L[𝕜] E) :
    toMatOf b A = LinearMap.toMatrixOrthonormal b (A : E →ₗ[𝕜] E) := by
  ext i j
  rw [toMatOf_apply, LinearMap.toMatrixOrthonormal_apply_apply, ContinuousLinearMap.coe_coe]

/-- On `EuclideanSpace 𝕜 d` the preferred matrix representation is the identity, in the sense that
it is Mathlib's `Matrix.toEuclideanCLM`. Existing matrix-level definitions are therefore literally
the special case `E := EuclideanSpace 𝕜 d` of the abstract ones. -/
@[simp]
theorem toMat_euclideanSpace (d : Type*) [Fintype d] [DecidableEq d] :
    toMat 𝕜 (EuclideanSpace 𝕜 d) d = (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := d)).symm :=
  rfl

@[simp]
theorem toMatOf_reindex (b : OrthonormalBasis ι 𝕜 E) [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (A : E →L[𝕜] E) : toMatOf (b.reindex e) A = (toMatOf b A).reindex e e := by
  rw [toMatOf_eq_toMatrixOrthonormal, toMatOf_eq_toMatrixOrthonormal,
    LinearMap.toMatrixOrthonormal_reindex]

@[simp]
theorem toMatOf_symm_reindex (b : OrthonormalBasis ι 𝕜 E) [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (M : Matrix κ κ 𝕜) : (toMatOf (b.reindex e)).symm M = (toMatOf b).symm (M.submatrix e e) := by
  apply EquivLike.injective (toMatOf (b.reindex e))
  rw [StarAlgEquiv.apply_symm_apply, toMatOf_reindex, StarAlgEquiv.apply_symm_apply]
  ext i j
  simp

section Unitary

omit [FiniteDimensional 𝕜 E]

variable [StdBasis 𝕜 E ι]

/-- The matrix of a unitary operator in the preferred basis, as a unitary matrix. -/
noncomputable def toMatUnitary (U : unitary (E →L[𝕜] E)) : Matrix.unitaryGroup ι 𝕜 :=
  ⟨toMat 𝕜 E ι U.val,
    ⟨by rw [← map_star, ← map_mul, U.2.1, map_one], by rw [← map_star, ← map_mul, U.2.2, map_one]⟩⟩

@[simp]
theorem toMatUnitary_coe (U : unitary (E →L[𝕜] E)) :
    (toMatUnitary (ι := ι) U : Matrix ι ι 𝕜) = toMat 𝕜 E ι U.val :=
  rfl

/-- The unitary operator whose matrix in the preferred basis is a given unitary matrix. -/
noncomputable def unitaryOfMat (U : Matrix.unitaryGroup ι 𝕜) : unitary (E →L[𝕜] E) :=
  ⟨(toMat 𝕜 E ι).symm U.val,
    ⟨by rw [← map_star, ← map_mul, U.2.1, map_one], by rw [← map_star, ← map_mul, U.2.2, map_one]⟩⟩

@[simp]
theorem unitaryOfMat_coe (U : Matrix.unitaryGroup ι 𝕜) :
    (unitaryOfMat (E := E) U : E →L[𝕜] E) = (toMat 𝕜 E ι).symm U.val :=
  rfl

@[simp]
theorem toMatUnitary_unitaryOfMat (U : Matrix.unitaryGroup ι 𝕜) :
    toMatUnitary (E := E) (ι := ι) (unitaryOfMat U) = U :=
  Subtype.ext <| by simp

@[simp]
theorem unitaryOfMat_toMatUnitary (U : unitary (E →L[𝕜] E)) :
    unitaryOfMat (toMatUnitary (ι := ι) U) = U :=
  Subtype.ext <| by simp

end Unitary

end ToMat

section ChangeOfBasis

variable [Fintype ι] [DecidableEq ι]

/-- The unitary change-of-basis matrix taking the matrix of an operator in the basis `b` to its
matrix in the basis `b'`. -/
noncomputable def changeOfBasis (b b' : OrthonormalBasis ι 𝕜 E) : Matrix.unitaryGroup ι 𝕜 :=
  ⟨b.toBasis.toMatrix b'.toBasis, b.toMatrix_orthonormalBasis_mem_unitary b'⟩

@[simp]
theorem changeOfBasis_coe (b b' : OrthonormalBasis ι 𝕜 E) :
    (changeOfBasis b b' : Matrix ι ι 𝕜) = b.toBasis.toMatrix b'.toBasis :=
  rfl

theorem changeOfBasis_star (b b' : OrthonormalBasis ι 𝕜 E) :
    (star (changeOfBasis b b') : Matrix ι ι 𝕜) = b'.toBasis.toMatrix b.toBasis := by
  have h₁ : b'.toBasis.toMatrix b.toBasis * b.toBasis.toMatrix b'.toBasis = 1 :=
    Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have h₂ : b.toBasis.toMatrix b'.toBasis * (b.toBasis.toMatrix b'.toBasis)ᴴ = 1 :=
    b.toMatrix_orthonormalBasis_self_mul_conjTranspose b'
  calc (star (changeOfBasis b b') : Matrix ι ι 𝕜)
      = 1 * (b.toBasis.toMatrix b'.toBasis)ᴴ := (one_mul _).symm
    _ = b'.toBasis.toMatrix b.toBasis *
          (b.toBasis.toMatrix b'.toBasis * (b.toBasis.toMatrix b'.toBasis)ᴴ) := by
        rw [← h₁, mul_assoc]
    _ = b'.toBasis.toMatrix b.toBasis := by rw [h₂, mul_one]

variable [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- Changing the orthonormal basis conjugates the matrix of an operator by a unitary. -/
theorem toMatOf_conj (b b' : OrthonormalBasis ι 𝕜 E) (A : E →L[𝕜] E) :
    toMatOf b' A =
      (star (changeOfBasis b b') : Matrix ι ι 𝕜) * toMatOf b A *
        (changeOfBasis b b' : Matrix ι ι 𝕜) := by
  rw [changeOfBasis_star, changeOfBasis_coe, toMatOf_eq_toMatrixOrthonormal,
    toMatOf_eq_toMatrixOrthonormal]
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix _ _ _ _ _).symm

/-- The inverse form of `StdBasis.toMatOf_conj`: reading a matrix as an operator in a different
orthonormal basis conjugates it by a unitary. -/
theorem toMatOf_symm_conj (b b' : OrthonormalBasis ι 𝕜 E) (M : Matrix ι ι 𝕜) :
    (toMatOf b').symm M = (toMatOf b).symm ((changeOfBasis b b' : Matrix ι ι 𝕜) * M *
      (star (changeOfBasis b b') : Matrix ι ι 𝕜)) := by
  set C := changeOfBasis b b' with hC
  have h₁ : (star C : Matrix ι ι 𝕜) * (C : Matrix ι ι 𝕜) = 1 :=
    Matrix.UnitaryGroup.star_mul_self C
  apply EquivLike.injective (toMatOf b')
  rw [StarAlgEquiv.apply_symm_apply, toMatOf_conj b b', StarAlgEquiv.apply_symm_apply, ← hC]
  calc M = ((star C : Matrix ι ι 𝕜) * (C : Matrix ι ι 𝕜)) * M *
        ((star C : Matrix ι ι 𝕜) * (C : Matrix ι ι 𝕜)) := by rw [h₁, one_mul, mul_one]
    _ = (star C : Matrix ι ι 𝕜) * ((C : Matrix ι ι 𝕜) * M * (star C : Matrix ι ι 𝕜)) *
        (C : Matrix ι ι 𝕜) := by noncomm_ring

/-- **Basis insensitivity.** A quantity extracted from the matrix of an operator is independent of
the choice of orthonormal basis as soon as it is invariant under unitary conjugation.

This reduces "prove the matrix definition is basis-independent" to the single unitary-invariance
fact that is usually already available (for instance `HermitianMat.eigenvalues_conj` or
`HermitianMat.trace_conj_unitary`). -/
theorem congr_of_unitaryInvariant {X : Type*} (f : Matrix ι ι 𝕜 → X)
    (hf : ∀ (U : Matrix.unitaryGroup ι 𝕜) (M : Matrix ι ι 𝕜),
      f ((star U : Matrix ι ι 𝕜) * M * (U : Matrix ι ι 𝕜)) = f M)
    (b b' : OrthonormalBasis ι 𝕜 E) (A : E →L[𝕜] E) :
    f (toMatOf b' A) = f (toMatOf b A) := by
  rw [toMatOf_conj b b', hf]

/-- The version of `StdBasis.congr_of_unitaryInvariant` for two `StdBasis` instances on the same
type. -/
theorem toMat_congr_of_unitaryInvariant {X : Type*} (f : Matrix ι ι 𝕜 → X)
    (hf : ∀ (U : Matrix.unitaryGroup ι 𝕜) (M : Matrix ι ι 𝕜),
      f ((star U : Matrix ι ι 𝕜) * M * (U : Matrix ι ι 𝕜)) = f M)
    (inst inst' : StdBasis 𝕜 E ι) (A : E →L[𝕜] E) :
    f (@toMat 𝕜 E ι _ _ _ _ _ inst' A) = f (@toMat 𝕜 E ι _ _ _ _ _ inst A) :=
  congr_of_unitaryInvariant f hf inst.stdBasis inst'.stdBasis A

end ChangeOfBasis

section Conjugation

variable [CompleteSpace E] [CompleteSpace F]

/-- Conjugating by a linear isometry equivalence preserves positivity of operators. -/
theorem _root_.ContinuousLinearMap.IsPositive.conjStarAlgEquiv
    (e : E ≃ₗᵢ[𝕜] F) {A : E →L[𝕜] E} (hA : A.IsPositive) :
    (e.conjStarAlgEquiv A).IsPositive := by
  refine ⟨fun x y ↦ ?_, fun x ↦ ?_⟩
  · calc ⟪(e.conjStarAlgEquiv A) x, y⟫_𝕜 = ⟪e (A (e.symm x)), e (e.symm y)⟫_𝕜 := by simp
      _ = ⟪A (e.symm x), e.symm y⟫_𝕜 := e.inner_map_map _ _
      _ = ⟪e.symm x, A (e.symm y)⟫_𝕜 := hA.1 _ _
      _ = ⟪e (e.symm x), e (A (e.symm y))⟫_𝕜 := (e.inner_map_map _ _).symm
      _ = ⟪x, (e.conjStarAlgEquiv A) y⟫_𝕜 := by simp
  · have h := hA.2 (e.symm x)
    rw [ContinuousLinearMap.reApplyInnerSelf] at h ⊢
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    have hx : ⟪e (A (e.symm x)), x⟫_𝕜 = ⟪A (e.symm x), e.symm x⟫_𝕜 := by
      rw [← e.inner_map_map (A (e.symm x)) (e.symm x), e.apply_symm_apply]
    rwa [hx]

/-- An operator is positive exactly when its conjugate by a linear isometry equivalence is. -/
theorem _root_.ContinuousLinearMap.isPositive_conjStarAlgEquiv_iff
    (e : E ≃ₗᵢ[𝕜] F) (A : E →L[𝕜] E) :
    (e.conjStarAlgEquiv A).IsPositive ↔ A.IsPositive := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conjStarAlgEquiv e⟩
  have := h.conjStarAlgEquiv e.symm
  rwa [← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.symm_apply_apply] at this

end Conjugation

section Transfer

variable [Fintype ι] [DecidableEq ι] [CompleteSpace E]

/-- The matrix of an operator is positive semidefinite exactly when the operator is positive. -/
theorem posSemidef_toMatOf_iff (b : OrthonormalBasis ι 𝕜 E) (A : E →L[𝕜] E) :
    (toMatOf b A).PosSemidef ↔ A.IsPositive := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  have hcoe : (toMatOf b A).toEuclideanLin =
      ((b.repr.conjStarAlgEquiv A : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) :
        EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) := by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    congr 1
    exact (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)).apply_symm_apply _
  rw [hcoe, ContinuousLinearMap.isPositive_toLinearMap_iff,
    ContinuousLinearMap.isPositive_conjStarAlgEquiv_iff]

/-- The matrix of an operator is positive semidefinite exactly when the operator is nonnegative in
the Loewner order. -/
theorem posSemidef_toMatOf_iff_nonneg (b : OrthonormalBasis ι 𝕜 E) (A : E →L[𝕜] E) :
    (toMatOf b A).PosSemidef ↔ 0 ≤ A :=
  (posSemidef_toMatOf_iff b A).trans (ContinuousLinearMap.nonneg_iff_isPositive A).symm

/-- The matrix of an operator is Hermitian exactly when the operator is self-adjoint. -/
theorem isHermitian_toMatOf_iff (b : OrthonormalBasis ι 𝕜 E) (A : E →L[𝕜] E) :
    (toMatOf b A).IsHermitian ↔ IsSelfAdjoint A := by
  have hst : toMatOf b (star A) = star (toMatOf b A) := (toMatOf b).map_star' A
  refine ⟨fun h ↦ EquivLike.injective (toMatOf b) ?_, fun h ↦ ?_⟩
  · rw [hst]
    exact h
  · show (toMatOf b A)ᴴ = toMatOf b A
    rw [← Matrix.star_eq_conjTranspose, ← hst, h.star_eq]

variable [FiniteDimensional 𝕜 E]

/-- The matrix of an operator has the same trace as the operator. -/
theorem trace_toMatOf (b : OrthonormalBasis ι 𝕜 E) (A : E →L[𝕜] E) :
    (toMatOf b A).trace = LinearMap.trace 𝕜 E (A : E →ₗ[𝕜] E) := by
  rw [toMatOf_eq_toMatrixOrthonormal, LinearMap.trace_eq_matrix_trace 𝕜 b.toBasis]
  rfl

end Transfer

section Preferred

variable [Fintype ι] [DecidableEq ι] [StdBasis 𝕜 E ι]

@[simp]
theorem toMat_apply (A : E →L[𝕜] E) (i j : ι) :
    toMat 𝕜 E ι A i j = ⟪stdBasis (𝕜 := 𝕜) (E := E) i, A (stdBasis (𝕜 := 𝕜) (E := E) j)⟫_𝕜 :=
  toMatOf_apply _ A i j

variable (𝕜 E ι) in
/-- `StdBasis.toMat` as a `𝕜`-linear equivalence, for use where only the linear structure is
needed -- for instance in transporting a linear map of operators to a linear map of matrices. -/
noncomputable def toMatₗ : (E →L[𝕜] E) ≃ₗ[𝕜] Matrix ι ι 𝕜 :=
  (toMat 𝕜 E ι).toAlgEquiv.toLinearEquiv

@[simp]
theorem toMatₗ_apply (A : E →L[𝕜] E) : toMatₗ 𝕜 E ι A = toMat 𝕜 E ι A :=
  rfl

@[simp]
theorem toMatₗ_symm_apply (M : Matrix ι ι 𝕜) : (toMatₗ 𝕜 E ι).symm M = (toMat 𝕜 E ι).symm M :=
  rfl

theorem toMat_eq_toMatrixOrthonormal (A : E →L[𝕜] E) :
    toMat 𝕜 E ι A = LinearMap.toMatrixOrthonormal (stdBasis (𝕜 := 𝕜) (E := E)) (A : E →ₗ[𝕜] E) :=
  toMatOf_eq_toMatrixOrthonormal _ A

/-- The matrix of an operator in the preferred basis is positive semidefinite exactly when the
operator is positive. -/
theorem posSemidef_toMat_iff (A : E →L[𝕜] E) : (toMat 𝕜 E ι A).PosSemidef ↔ A.IsPositive :=
  posSemidef_toMatOf_iff _ A

/-- The matrix of an operator in the preferred basis is positive semidefinite exactly when the
operator is nonnegative in the Loewner order. -/
theorem posSemidef_toMat_iff_nonneg (A : E →L[𝕜] E) : (toMat 𝕜 E ι A).PosSemidef ↔ 0 ≤ A :=
  posSemidef_toMatOf_iff_nonneg _ A

/-- The matrix of an operator in the preferred basis is Hermitian exactly when the operator is
self-adjoint. -/
theorem isHermitian_toMat_iff (A : E →L[𝕜] E) : (toMat 𝕜 E ι A).IsHermitian ↔ IsSelfAdjoint A :=
  isHermitian_toMatOf_iff _ A

/-- The matrix of an operator in the preferred basis has the same trace as the operator. -/
@[simp]
theorem trace_toMat (A : E →L[𝕜] E) :
    (toMat 𝕜 E ι A).trace = LinearMap.trace 𝕜 E (A : E →ₗ[𝕜] E) :=
  trace_toMatOf _ A

end Preferred

section Equiv

variable [Fintype ι] [DecidableEq ι] [StdBasis 𝕜 E ι] [StdBasis 𝕜 F ι]

variable (𝕜 E F ι) in
/-- The linear isometry equivalence between two spaces carrying preferred orthonormal bases with
the same index type: the one matching up the two preferred bases.

This is how a space whose preferred basis happens to be indexed by a product `ι × κ` -- for
instance `EuclideanSpace 𝕜 (ι × κ)` -- gets identified with an actual tensor product. -/
noncomputable def equiv : E ≃ₗᵢ[𝕜] F :=
  (stdBasis (𝕜 := 𝕜) (E := E)).repr.trans (stdBasis (𝕜 := 𝕜) (E := F)).repr.symm

@[simp]
theorem equiv_stdBasis (i : ι) :
    equiv 𝕜 E F ι (stdBasis (𝕜 := 𝕜) (E := E) i) = stdBasis (𝕜 := 𝕜) (E := F) i := by
  rw [equiv, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self,
    OrthonormalBasis.repr_symm_single]

@[simp]
theorem equiv_symm_stdBasis (i : ι) :
    (equiv 𝕜 E F ι).symm (stdBasis (𝕜 := 𝕜) (E := F) i) = stdBasis (𝕜 := 𝕜) (E := E) i := by
  rw [← equiv_stdBasis (𝕜 := 𝕜) (E := E) (F := F) i, LinearIsometryEquiv.symm_apply_apply]

variable [CompleteSpace E] [CompleteSpace F]

/-- Transporting an operator along `StdBasis.equiv` leaves its matrix unchanged: that is exactly
what it means for `StdBasis.equiv` to identify the two preferred bases. -/
@[simp]
theorem toMat_conjStarAlgEquiv_equiv (A : E →L[𝕜] E) :
    toMat 𝕜 F ι ((equiv 𝕜 E F ι).conjStarAlgEquiv A) = toMat 𝕜 E ι A := by
  ext i j
  rw [toMat_apply, toMat_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    equiv_symm_stdBasis, ← equiv_stdBasis (𝕜 := 𝕜) (E := E) (F := F) i,
    LinearIsometryEquiv.inner_map_map]

end Equiv

section Relabel

variable [Fintype ι] [DecidableEq ι] [StdBasis 𝕜 E ι] [Fintype κ] [DecidableEq κ] [StdBasis 𝕜 F κ]

/-- A linear isometry equivalence that carries the preferred basis of `E` to the preferred basis of
`F`, relabelling indices along `σ`, relabels matrices along `σ` as well.

`toMat_conjStarAlgEquiv_equiv` is the case `σ = Equiv.refl`; the case of interest with `σ ≠ refl`
is an isometry that rearranges tensor factors, such as `TensorProduct.assocIsometry`. -/
theorem toMat_conjStarAlgEquiv_of_stdBasis (e : E ≃ₗᵢ[𝕜] F) (σ : ι ≃ κ)
    (he : ∀ i, e (stdBasis (𝕜 := 𝕜) (E := E) i) = stdBasis (𝕜 := 𝕜) (E := F) (σ i))
    (A : E →L[𝕜] E) :
    toMat 𝕜 F κ (e.conjStarAlgEquiv A) = (toMat 𝕜 E ι A).submatrix σ.symm σ.symm := by
  have he' (k : κ) : stdBasis (𝕜 := 𝕜) (E := F) k = e (stdBasis (𝕜 := 𝕜) (E := E) (σ.symm k)) := by
    rw [he, Equiv.apply_symm_apply]
  have hsymm (k : κ) :
      e.symm (stdBasis (𝕜 := 𝕜) (E := F) k) = stdBasis (𝕜 := 𝕜) (E := E) (σ.symm k) := by
    rw [he', LinearIsometryEquiv.symm_apply_apply]
  ext k l
  rw [Matrix.submatrix_apply, toMat_apply, toMat_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hsymm, he' k,
    LinearIsometryEquiv.inner_map_map]

end Relabel

section TensorRearrange

variable {G μ : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
variable [Fintype ι] [Fintype κ] [Fintype μ]
variable [StdBasis 𝕜 E ι] [StdBasis 𝕜 F κ] [StdBasis 𝕜 G μ]

/-- Reassociating a triple tensor product carries preferred basis vectors to preferred basis
vectors, relabelling the index along `Equiv.prodAssoc`. -/
@[simp]
theorem assocIsometry_stdBasis (p : (ι × κ) × μ) :
    TensorProduct.assocIsometry 𝕜 E F G (stdBasis (𝕜 := 𝕜) (E := (E ⊗[𝕜] F) ⊗[𝕜] G) p) =
      stdBasis (𝕜 := 𝕜) (E := E ⊗[𝕜] (F ⊗[𝕜] G)) (Equiv.prodAssoc ι κ μ p) := by
  simp [OrthonormalBasis.tensorProduct_apply']

/-- Swapping the two factors of a tensor product carries preferred basis vectors to preferred
basis vectors, relabelling the index along `Equiv.prodComm`. -/
@[simp]
theorem commIsometry_stdBasis (p : ι × κ) :
    TensorProduct.commIsometry 𝕜 E F (stdBasis (𝕜 := 𝕜) (E := E ⊗[𝕜] F) p) =
      stdBasis (𝕜 := 𝕜) (E := F ⊗[𝕜] E) (Equiv.prodComm ι κ p) := by
  simp [OrthonormalBasis.tensorProduct_apply']

end TensorRearrange

end StdBasis
