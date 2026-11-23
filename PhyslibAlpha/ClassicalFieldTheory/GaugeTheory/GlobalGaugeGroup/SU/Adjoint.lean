/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.GellMann
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import PhyslibAlpha.Mathematics.ForMathlib.DataStructures.Matrix.PlaneMatrix
public import PhyslibAlpha.Mathematics.RepresentationTheory.Invariants
/-!
# The adjoint representation of `SU(N)`

The action of `SU(N)` on its complexified Lie algebra, and its matrix in the Gell-Mann basis.

## i. Overview

The adjoint representation of `SU(N)` acts on the complexified Lie algebra
`SUAlgebraComplexified N = ℂ ⊗[ℝ] su(N)` as the complexification of the conjugation action
`X ↦ g X g⁻¹` on `su(N)` (A). The generalized Gell-Mann matrices, a real basis of `su(N)`, give the
basis `adjBasis N` of the complexified Lie algebra. Sending `z ⊗ X` to the matrix `z X` identifies
the complexified Lie algebra with the traceless complex matrices (`adjMat`), injectively
(`adjMat_injective`) and onto (`adjMat_ofTraceless`), and on matrices the adjoint action is
conjugation (`adjMat_adjRep`). The coordinates in the Gell-Mann basis are the trace pairings
`tr (λ_a A) / 2`.

In the Gell-Mann basis the adjoint action of `g` has the matrix `adjMatrix g`, with entries
`tr (λ_a g λ_b g⁻¹) / 2`: real, the Gell-Mann matrices being hermitian, and orthogonal, the matrix
of `g⁻¹` being the transpose (B).

The trace form `A ⊗ B ↦ tr (A B)` is symmetric and nondegenerate, the trace pairing with a Gell-Mann
matrix being twice the coordinate, and it is invariant under the adjoint action, so it is the
contraction `adjContr` of two adjoint indices (C).

For two distinct coordinates `p` and `q`, an element `U` of `SU(2)` acts on the plane they span
and fixes the other coordinates. This is `SU.planeEmbed p q`, a group homomorphism from `SU(2)`
to `SU(N)` (D), built from the plane matrices of
`PhyslibAlpha.Mathematics.ForMathlib.DataStructures.Matrix.PlaneMatrix`. A diagonal phase
`diag (u, ū)` and the rotation by a quarter turn, embedded in every plane, force a matrix commuting
with all of `SU(N)` to be scalar (E). The matrix `adjMat A` of an invariant of the adjoint
representation commutes with every element of `SU(N)`, so it is a scalar, and it is traceless, so
the adjoint representation has no invariants but zero (F).

## ii. Key results

- `suTensor.adjRep` : the adjoint representation on the complexified Lie algebra.
- `suTensor.adjMat` : the complexified Lie algebra as traceless complex matrices.
- `suTensor.adjMatrix` : the matrix of the adjoint action in the Gell-Mann basis.
- `suTensor.adjMatrix_inv` : the matrix of `g⁻¹` is the transpose of that of `g`.
- `suTensor.traceForm_nondegenerate` : the trace form is nondegenerate.
- `suTensor.adjContr` : the contraction of two adjoint indices.
- `SU.planeEmbed` : `SU(2)` acting on the plane of two coordinates, as a subgroup of `SU(N)`.
- `SU.eq_smul_one_of_commute` : a matrix commuting with `SU(N)` is scalar.
- `suTensor.invariants_adjRep_eq_bot` : the adjoint representation has no invariants but zero.

## iii. Table of contents

- A. The adjoint representation on the complexified Lie algebra
- B. The matrix of the adjoint action
- C. The trace form and the contraction
- D. The plane embedding of `SU(2)`
- E. Matrices commuting with `SU(N)`
- F. One adjoint index has no invariants

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups Module TensorProduct

/-- The gauge group `SU(n)`, the special unitary matrices. -/
abbrev SU (n : ℕ) : Type := specialUnitaryGroup (Fin n) ℂ

/-- The Lie algebra `su(n)`, the traceless hermitian matrices. -/
abbrev SUAlgebra (n : ℕ) : Type := SUAlgebraOver ℂ n

/-- The adjoint action `a ↦ U a U†` of `SU(n)` on `su(n)`. -/
noncomputable def SUAlgebra.adjointValue {n : ℕ} : Representation ℝ (SU n) (SUAlgebra n) :=
  (SUAlgebraOver.conj (R := ℂ)).comp
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

@[simp]
lemma SUAlgebra.adjointValue_val {n : ℕ} (U : SU n) (a : SUAlgebra n) :
    (SUAlgebra.adjointValue U a).1 = U.1 * a.1 * star U.1 := rfl

namespace suTensor

/-!

## A. The adjoint representation on the complexified Lie algebra

-/

variable (N : ℕ)

/-- The generalized Gell-Mann basis `1 ⊗ λ_a` of the complexified Lie algebra `ℂ ⊗[ℝ] su(N)`. -/
noncomputable def adjBasis : Basis (GellMann.Index N) ℂ (SUAlgebraComplexified N) :=
  GellMann.realBasis.baseChange ℂ

lemma adjBasis_apply (a : GellMann.Index N) :
    adjBasis N a = (1 : ℂ) ⊗ₜ[ℝ] GellMann.realBasis a :=
  Module.Basis.baseChange_apply _ _ a

variable {N}

lemma val_inv_mul_val (g : SU N) : (g⁻¹).1 * g.1 = 1 := by
  rw [← Submonoid.coe_mul, inv_mul_cancel]
  rfl

lemma val_inv (g : SU N) : (g⁻¹).1 = star g.1 := by
  have h : g.1 * star g.1 = 1 :=
    mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp g.2).1
  calc (g⁻¹).1 = (g⁻¹).1 * (g.1 * star g.1) := by rw [h, Matrix.mul_one]
    _ = star g.1 := by rw [← Matrix.mul_assoc, val_inv_mul_val, Matrix.one_mul]

variable (N)

/-- The adjoint representation on the complexified Lie algebra, the complexification of the
  adjoint action `X ↦ g X g⁻¹` on `su(N)`. -/
noncomputable def adjRep : Representation ℂ (SU N) (SUAlgebraComplexified N) where
  toFun g := (SUAlgebra.adjointValue g).baseChange ℂ
  map_one' := by
    rw [map_one]
    exact LinearMap.baseChange_id
  map_mul' g h := by
    rw [map_mul]
    exact LinearMap.baseChange_comp _ _

/-- The matrix of an element of the complexified Lie algebra, `z ⊗ X ↦ z X`, a traceless complex
  matrix. -/
noncomputable def adjMat : SUAlgebraComplexified N →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  (SUAlgebraOver.submodule ℂ N).subtype.liftBaseChange ℂ

variable {N}

@[simp]
lemma adjMat_tmul (z : ℂ) (X : SUAlgebra N) : adjMat N (z ⊗ₜ X) = z • X.1 := rfl

@[simp]
lemma adjMat_adjBasis (a : GellMann.Index N) : adjMat N (adjBasis N a) = GellMann.matrix a := by
  rw [adjBasis_apply, adjMat_tmul, one_smul, GellMann.realBasis_apply_val]

/-- The matrix of an element of the complexified Lie algebra is traceless. -/
lemma trace_adjMat (A : SUAlgebraComplexified N) : (adjMat N A).trace = 0 := by
  induction A using TensorProduct.inductionOn with
  | tmul z X => rw [adjMat_tmul, trace_smul, X.trace_val, smul_zero]
  | add A B hA hB => rw [map_add, trace_add, hA, hB, add_zero]

/-- The adjoint representation moves the matrix by conjugation. -/
@[simp]
lemma adjMat_adjRep (g : SU N) (A : SUAlgebraComplexified N) :
    adjMat N (adjRep N g A) = g.1 * adjMat N A * (g⁻¹).1 := by
  induction A using TensorProduct.inductionOn with
  | tmul z X =>
    change adjMat N (z ⊗ₜ SUAlgebra.adjointValue g X) = _
    rw [adjMat_tmul, adjMat_tmul, SUAlgebra.adjointValue_val, val_inv, Matrix.mul_smul,
      Matrix.smul_mul]
  | add A B hA hB => rw [map_add, map_add, hA, hB, map_add, Matrix.mul_add, Matrix.add_mul]

/-- The coordinates in the Gell-Mann basis are read off by the trace form,
  `A = ∑ (tr (λ_a A) / 2) λ_a`. -/
lemma adjBasis_repr_apply (A : SUAlgebraComplexified N) (a : GellMann.Index N) :
    (adjBasis N).repr A a = (GellMann.matrix a * adjMat N A).trace / 2 := by
  conv_rhs => rw [← (adjBasis N).sum_repr A]
  simp only [map_sum, map_smul, adjMat_adjBasis, Matrix.mul_sum, Matrix.mul_smul, trace_sum,
    trace_smul, GellMann.trace_matrix_mul_matrix, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  ring

/-- An element of the complexified Lie algebra is determined by its matrix. -/
lemma adjMat_injective : Function.Injective (adjMat N) := fun A B h =>
  (adjBasis N).ext_elem fun a => by rw [adjBasis_repr_apply, adjBasis_repr_apply, h]

/-- The element of the complexified Lie algebra with a given traceless matrix. -/
noncomputable def ofTraceless (M : Matrix (Fin N) (Fin N) ℂ) : SUAlgebraComplexified N :=
  ∑ a, ((GellMann.matrix a * M).trace / 2) • adjBasis N a

/-- Every traceless matrix is the matrix of an element of the complexified Lie algebra. -/
@[simp]
lemma adjMat_ofTraceless {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.trace = 0) :
    adjMat N (ofTraceless M) = M := by
  have h := congrArg Subtype.val
    (GellMann.basis.sum_repr (⟨M, hM⟩ : ↥(LinearMap.ker (Matrix.traceLinearMap (Fin N) ℂ ℂ))))
  simp only [Submodule.coe_sum, Submodule.coe_smul, GellMann.basis_apply_val,
    GellMann.basis_repr_apply] at h
  simp only [ofTraceless, map_sum, map_smul, adjMat_adjBasis]
  exact h

/-!

## B. The matrix of the adjoint action

-/

/-- The matrix, in the Gell-Mann basis, of the adjoint action of an element of `SU(N)`. -/
noncomputable abbrev adjMatrix (g : SU N) : Matrix (GellMann.Index N) (GellMann.Index N) ℂ :=
  LinearMap.toMatrix (adjBasis N) (adjBasis N) (adjRep N g)

/-- The entries of the matrix of the adjoint action, `tr (λ_a g λ_b g⁻¹) / 2`. -/
lemma adjMatrix_apply (g : SU N) (a b : GellMann.Index N) :
    adjMatrix g a b = (GellMann.matrix a * (g.1 * GellMann.matrix b * (g⁻¹).1)).trace / 2 := by
  rw [adjMatrix, LinearMap.toMatrix_apply, adjBasis_repr_apply, adjMat_adjRep, adjMat_adjBasis]

/-- The matrix of the adjoint action is real, the Gell-Mann matrices being hermitian. -/
lemma star_adjMatrix_apply (g : SU N) (a b : GellMann.Index N) :
    star (adjMatrix g a b) = adjMatrix g a b := by
  rw [adjMatrix_apply, star_div₀, ← trace_conjTranspose]
  simp only [conjTranspose_mul, GellMann.conjTranspose_matrix, val_inv, star_eq_conjTranspose,
    conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [show star (2 : ℂ) = 2 by simp, trace_mul_comm g.1]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (GellMann.matrix b), trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The matrix of the adjoint action of the inverse of an element of `SU(N)` is the transpose of
  that of the element, by the cyclicity of the trace. -/
lemma adjMatrix_inv (g : SU N) : adjMatrix g⁻¹ = (adjMatrix g)ᵀ := by
  ext a b
  rw [transpose_apply, adjMatrix_apply, adjMatrix_apply, inv_inv]
  congr 1
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The matrix of the adjoint action of the inverse of an element of `SU(N)` times that of the
  element is the identity. -/
lemma adjMatrix_inv_mul (g : SU N) : adjMatrix g⁻¹ * adjMatrix g = 1 := by
  rw [adjMatrix, adjMatrix, ← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one,
    LinearMap.toMatrix_one]

/-!

## C. The trace form and the contraction

-/

variable (N)

/-- The trace form `A ⊗ B ↦ tr (A B)` on the complexified Lie algebra. -/
noncomputable def traceForm : LinearMap.BilinForm ℂ (SUAlgebraComplexified N) :=
  LinearMap.mk₂ ℂ (fun A B => (adjMat N A * adjMat N B).trace)
    (fun A A' B => by simp [add_mul, trace_add])
    (fun a A B => by simp)
    (fun A B B' => by simp [mul_add, trace_add])
    (fun a A B => by simp)

@[simp]
lemma traceForm_apply (A B : SUAlgebraComplexified N) :
    traceForm N A B = (adjMat N A * adjMat N B).trace := rfl

/-- The trace form is symmetric. -/
lemma traceForm_isSymm : (traceForm N).IsSymm :=
  ⟨fun A B => by rw [traceForm_apply, traceForm_apply, trace_mul_comm]⟩

/-- The trace form against a Gell-Mann basis vector is twice the coordinate. -/
lemma traceForm_adjBasis (A : SUAlgebraComplexified N) (a : GellMann.Index N) :
    traceForm N A (adjBasis N a) = 2 * (adjBasis N).repr A a := by
  rw [traceForm_apply, adjMat_adjBasis, adjBasis_repr_apply, trace_mul_comm]
  ring

/-- An element orthogonal to every element under the trace form vanishes. Its coordinates are its
  trace pairings with the Gell-Mann basis. -/
lemma traceForm_separatingLeft (A : SUAlgebraComplexified N) (hA : ∀ B, traceForm N A B = 0) :
    A = 0 :=
  (adjBasis N).ext_elem fun a => by
    have h := hA (adjBasis N a)
    rw [traceForm_adjBasis] at h
    simpa using h

/-- The trace form is nondegenerate on the complexified Lie algebra. -/
lemma traceForm_nondegenerate : (traceForm N).Nondegenerate :=
  ⟨traceForm_separatingLeft N, fun B hB => traceForm_separatingLeft N B fun A => by
    rw [(traceForm_isSymm N).eq]
    exact hB A⟩

/-- The contraction of two adjoint indices, the trace form `A ⊗ B ↦ tr (A B)`. -/
noncomputable def adjContr : ((adjRep N).tprod (adjRep N)).IntertwiningMap
    (Representation.trivial ℂ (SU N) ℂ) where
  toLinearMap := TensorProduct.lift (traceForm N)
  isIntertwining' g := TensorProduct.ext' fun A B => by
    change (adjMat N (adjRep N g A) * adjMat N (adjRep N g B)).trace
      = (adjMat N A * adjMat N B).trace
    rw [adjMat_adjRep, adjMat_adjRep, show g.1 * adjMat N A * (g⁻¹).1 * (g.1 * adjMat N B * (g⁻¹).1)
        = g.1 * (adjMat N A * adjMat N B) * (g⁻¹).1 by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (g⁻¹).1, val_inv_mul_val, Matrix.one_mul]]
    rw [Matrix.trace_mul_cycle, val_inv_mul_val, one_mul]

/-- The trace form separates the complexified Lie algebra. -/
lemma adjContr_flip_injective :
    Function.Injective (TensorProduct.curry (adjContr N).toLinearMap).flip := fun w w' h => by
  refine sub_eq_zero.1 ((traceForm_nondegenerate N).2 _ fun x => ?_)
  have hx := LinearMap.congr_fun h x
  simp only [LinearMap.flip_apply, TensorProduct.curry_apply] at hx
  rw [map_sub, sub_eq_zero]
  exact hx

end suTensor

open Matrix MatrixGroups

namespace SU

variable {N : ℕ} {p q : Fin N}

/-!

## D. The plane embedding of `SU(2)`

-/

/-- `SU(2)` acting on the plane of two distinct coordinates `p` and `q` and trivially on the
  others, a homomorphism from `SU(2)` to `SU(N)`. -/
noncomputable def planeEmbed (p q : Fin N) (hpq : p ≠ q) : SU 2 →* SU N where
  toFun U := ⟨planeMatrix p q U.1, by
    have hU := mem_specialUnitaryGroup_iff.mp U.2
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose] at hU
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose,
      conjTranspose_planeMatrix, planeMatrix_mul hpq, det_planeMatrix hpq, hU.1, planeMatrix_one]
    exact ⟨rfl, hU.2⟩⟩
  map_one' := Subtype.ext planeMatrix_one
  map_mul' U V := Subtype.ext (planeMatrix_mul hpq U.1 V.1).symm

@[simp]
lemma planeEmbed_val (hpq : p ≠ q) (U : SU 2) : (planeEmbed p q hpq U).1 = planeMatrix p q U.1 :=
  rfl

/-- The diagonal element `diag (u, ū)` of `SU(2)`, for any complex number `u` of modulus one. -/
noncomputable def diagPhase (u : ℂ) (hu : u * star u = 1) : SU 2 :=
  ⟨diagonal ![u, star u], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose,
      diagonal_conjTranspose, diagonal_mul_diagonal, det_diagonal, Fin.prod_univ_two]
    have hu' : (starRingEnd ℂ) u * u = 1 := by rw [mul_comm]; exact hu
    have hu'' : u * (starRingEnd ℂ) u = 1 := hu
    refine ⟨?_, by simpa using hu⟩
    rw [← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hu', hu'']⟩

@[simp]
lemma diagPhase_val (u : ℂ) (hu : u * star u = 1) :
    (diagPhase u hu).1 = diagonal ![u, star u] := rfl

/-- The real rotation of `SU(2)` with matrix `!![c, -s; s, c]`, for any real cosine `c` and sine
  `s` with `c² + s² = 1`. -/
noncomputable def rotation (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : SU 2 :=
  ⟨!![(c : ℂ), -s; s, c], by
    have h' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose, det_fin_two_of]
    refine ⟨?_, by linear_combination h'⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← pow_two] <;>
      first | linear_combination h' | ring⟩

@[simp]
lemma rotation_val (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (rotation c s h).1 = !![(c : ℂ), -s; s, c] := rfl

/-!

## E. Matrices commuting with `SU(N)`

The diagonal phase `diag (i, -i)` in the plane of `p` and `q` negates the entries at `(p, q)`
and `(q, p)` of a matrix it commutes with, and the quarter turn exchanges the diagonal entries
at `p` and `q`.

-/

/-- A matrix commuting with every element of `SU(N)` is fixed by conjugation. -/
lemma conj_eq_of_commute {C : Matrix (Fin N) (Fin N) ℂ} (hC : ∀ g : SU N, g.1 * C = C * g.1)
    (g : SU N) : g.1 * C * g.1ᴴ = C := by
  have hg : g.1 * g.1ᴴ = 1 := by
    rw [← star_eq_conjTranspose, ← mem_unitaryGroup_iff]
    exact (mem_specialUnitaryGroup_iff.mp g.2).1
  rw [hC, Matrix.mul_assoc, hg, Matrix.mul_one]

/-- A matrix commuting with every element of `SU(N)` is diagonal, with equal diagonal
  entries. -/
lemma apply_eq_of_commute {C : Matrix (Fin N) (Fin N) ℂ} (hC : ∀ g : SU N, g.1 * C = C * g.1)
    (hpq : p ≠ q) : C p q = 0 ∧ C p p = C q q := by
  have hI : Complex.I * star Complex.I = 1 := by simp
  have h1 := congrFun (congrFun (planeBlock_eq_of_conj_eq hpq
    (conj_eq_of_commute hC (planeEmbed p q hpq (diagPhase Complex.I hI)))) 0) 1
  have h2 := congrFun (congrFun (planeBlock_eq_of_conj_eq hpq
    (conj_eq_of_commute hC (planeEmbed p q hpq (rotation 0 1 (by norm_num))))) 1) 1
  have hB : ∀ i j, ((planeInclusion p q)ᵀ * C * planeInclusion p q) i j
      = C (![p, q] i) (![p, q] j) := planeBlock_apply C
  generalize (planeInclusion p q)ᵀ * C * planeInclusion p q = B at h1 h2 hB
  simp only [Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, diagPhase_val,
    rotation_val, diagonal_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    cons_val_fin_one, empty_val', Fin.isValue] at h1 h2
  simp only [hB] at h1 h2
  simp at h1 h2
  exact ⟨by linear_combination (-1 / 2 : ℂ) * h1 + (C p q / 2) * Complex.I_mul_I, h2⟩

/-- A matrix commuting with every element of `SU(N)` is scalar. -/
lemma eq_smul_one_of_commute {C : Matrix (Fin N) (Fin N) ℂ}
    (hC : ∀ g : SU N, g.1 * C = C * g.1) : ∃ z : ℂ, C = z • 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, Subsingleton.elim _ _⟩
  refine ⟨C ⟨0, hN⟩ ⟨0, hN⟩, ext fun x y => ?_⟩
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x = ⟨0, hN⟩
    · simp [hx]
    · simp [(apply_eq_of_commute hC hx).2]
  · simp [hxy, (apply_eq_of_commute hC hxy).1]

end SU

/-!

## F. One adjoint index has no invariants

An invariant of the adjoint representation is a traceless matrix commuting with every element of
`SU(N)`, so it is a scalar by E, and its trace vanishes.

-/

namespace suTensor

variable {N : ℕ}

open SU in
/-- The adjoint representation has no invariants but zero. The matrix of an invariant commutes
  with every element of `SU(N)`, so it is a scalar, and its trace vanishes. -/
lemma invariants_adjRep_eq_bot : (adjRep N).invariants = ⊥ := by
  refine Representation.invariants_eq_bot_of_forall fun A hA => ?_
  obtain ⟨z, hz⟩ := eq_smul_one_of_commute (C := adjMat N A) fun g => by
    have h := congrArg (adjMat N) (hA g)
    rw [adjMat_adjRep] at h
    conv_rhs => rw [← h]
    simp only [Matrix.mul_assoc, val_inv_mul_val, Matrix.mul_one]
  have htr := trace_adjMat A
  rw [hz, trace_smul, trace_one, smul_eq_mul, mul_eq_zero, Fintype.card_fin] at htr
  refine adjMat_injective ?_
  rw [map_zero]
  rcases htr with rfl | hN
  · rw [hz, zero_smul]
  · have : IsEmpty (Fin N) := by
      rw [Fin.isEmpty_iff]
      exact_mod_cast hN
    exact Subsingleton.elim _ _

end suTensor
