/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

/-!

# The Stinespring witness and its finite-dimensional positivity kernel

Ported from `unbounded-alpha-public`'s `QuantumMechanics/Unbounded/OperatorAlgebra/Dynamics/
ChristensenEvans/P1.lean`, restated against this repo's own bare Mathlib hypotheses instead of the
upstream-superseded `OperatorAlgebra` class (`[OperatorAlgebra A]` there is exactly
`[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]` here — `OperatorAlgebra` adds no field or
axiom beyond those three, so the translation is a pure restatement, not new mathematics).

A completely positive map `J : A →CP (H →L[ℂ] H)` (Mathlib's own `CompletelyPositiveMap`, matrix-
amplified positivity) is exactly a positive-definite `B(H)`-valued kernel on `A`: applying `J` to
the Gram matrix of any finite family `a : Fin n → A` gives a positive block operator on the
finite Hilbert sum `⊕ᵢ H`. This file builds that translation (`blockMatrixMap`, `gramMatrix`,
`cpKernel_inner_nonneg_natural'`) and the `StinespringWitness` structure recording a concrete
dilation `J a = V⋆ π(a) V`. `Dilation.lean` builds the canonical witness that always exists.

## Main definitions

- `blockMatrixMap` : a `CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)` acting block-by-block on the
  finite Hilbert sum `PiLp 2 (Fin n → H)`, and its algebraic API (`_mul`, `_star`, `_one`, ...).
- `gramMatrix`, `cpKernel_inner_nonneg_natural'` : the CP-map positivity kernel on finite families.
- `StinespringWitness A H K J` : a concrete dilation of `J` — an auxiliary Hilbert space `K`, a
  representation `π : A →⋆ₐ[ℂ] (K →L[ℂ] K)`, and an implementing operator `V : H →L[ℂ] K` with
  `J a = V⋆ π(a) V`.
- `completelyPositiveMap_map_star_general` : a CP map between C⋆-algebras is automatically
  star-preserving.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra
open ContinuousLinearMap

noncomputable section

/-! ## `blockMatrixMap`: the finite block-operator representation

This part uses only the codomain Hilbert space `H`, no algebra `A` at all. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded operator on `PiLp 2 (Fin n → H)` acting block-by-block by `M`. -/
def blockMatrixMap {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) := by
  let e : PiLp 2 (fun _ : Fin n => H) ≃L[ℂ] (∀ _ : Fin n, H) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)
  let p : (∀ _ : Fin n, H) →L[ℂ] (∀ _ : Fin n, H) :=
    ContinuousLinearMap.pi (fun i =>
      ∑ j, (M i j).comp (ContinuousLinearMap.proj j))
  exact e.symm.toContinuousLinearMap.comp (p.comp e.toContinuousLinearMap)

omit [CompleteSpace H] in
@[nolint unusedArguments, simp]
lemma blockMatrixMap_apply {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) :
    (blockMatrixMap M x).ofLp i = ∑ j, M i j (x.ofLp j) := by
  simp [blockMatrixMap, PiLp.coe_continuousLinearEquiv]

lemma blockMatrixMap_star {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    blockMatrixMap (star M) = (blockMatrixMap M).adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, blockMatrixMap_apply,
    CStarMatrix.star_eq_conjTranspose, CStarMatrix.conjTranspose_apply,
    ContinuousLinearMap.star_eq_adjoint, sum_inner, inner_sum]
  simp_rw [ContinuousLinearMap.adjoint_inner_left]
  rw [Finset.sum_comm]

omit [CompleteSpace H] in
lemma blockMatrixMap_mul {n : ℕ} (M N : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    blockMatrixMap (M * N) = blockMatrixMap M ∘L blockMatrixMap N := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  simp only [blockMatrixMap_apply, ContinuousLinearMap.comp_apply, CStarMatrix.mul_apply]
  simp_rw [sum_apply]
  rw [Finset.sum_comm]
  simp_rw [mul_apply_eq_comp]
  simp_rw [map_sum]

omit [CompleteSpace H] in
lemma blockMatrixMap_one {n : ℕ} :
    blockMatrixMap (1 : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  rw [blockMatrixMap_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

omit [CompleteSpace H] in
lemma blockMatrixMap_add {n : ℕ} (M N : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    blockMatrixMap (M + N) = blockMatrixMap M + blockMatrixMap N := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  rw [blockMatrixMap_apply]
  rw [add_apply, PiLp.add_apply]
  simp only [CStarMatrix.add_apply]
  simp_rw [add_apply]
  rw [Finset.sum_add_distrib]
  rw [blockMatrixMap_apply, blockMatrixMap_apply]

omit [CompleteSpace H] in
lemma blockMatrixMap_zero {n : ℕ} :
    blockMatrixMap (0 : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  simp [blockMatrixMap_apply]

/-- `blockMatrixMap`, packaged as a star algebra homomorphism from
`CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)`. -/
def blockMatrixRepresentation {n : ℕ} :
    CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) →⋆ₐ[ℂ]
      (PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) where
  toFun := blockMatrixMap
  map_one' := blockMatrixMap_one
  map_mul' := blockMatrixMap_mul
  map_zero' := blockMatrixMap_zero
  map_add' := blockMatrixMap_add
  commutes' := by
    intro c
    apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    rw [blockMatrixMap_apply]
    simp only [Algebra.algebraMap_eq_smul_one, smul_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  map_star' := blockMatrixMap_star

lemma blockMatrixMap_isPositive {n : ℕ} {M : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)}
    (hM : 0 ≤ M) : (blockMatrixMap M).IsPositive := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  change 0 ≤ (blockMatrixRepresentation (H := H) (n := n)) M
  exact map_nonneg (blockMatrixRepresentation (H := H) (n := n)) hM

lemma blockMatrixMap_inner_nonneg {n : ℕ} {M : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)}
    (hM : 0 ≤ M) (x : PiLp 2 (fun _ : Fin n => H)) :
    0 ≤ ∑ i, ∑ j, inner ℂ (M i j (x.ofLp j)) (x.ofLp i) := by
  have h := (blockMatrixMap_isPositive hM).inner_nonneg_left x
  simpa [PiLp.inner_apply, blockMatrixMap_apply, sum_inner, inner_sum] using h

/-! ## The CP-map positivity kernel

From here on, `A` is a unital C⋆-algebra with the compatible Mathlib order (`[CStarAlgebra A]
[PartialOrder A] [StarOrderedRing A]`) — the field content of `OperatorAlgebra A`. -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A CP map between C⋆-algebras is automatically star-preserving. -/
lemma completelyPositiveMap_map_star_general
    {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (J : A →CP B) (a : A) : star (J a) = J (star a) := by
  obtain ⟨x, hx, _, ha⟩ := CStarAlgebra.exists_sum_four_nonneg a
  rw [ha]
  simp only [map_sum, map_smul, star_sum, star_smul]
  apply Finset.sum_congr rfl
  intro i _
  have hxi : IsSelfAdjoint (x i) := IsSelfAdjoint.of_nonneg (hx i)
  have hJxi : IsSelfAdjoint (J (x i)) :=
    IsSelfAdjoint.of_nonneg (map_nonneg J (hx i))
  rw [hJxi.star_eq, hxi.star_eq]

/-- A square matrix whose only nonzero row is the zeroth row. -/
def rowMatrix {n : ℕ} [NeZero n] (a : Fin n → A) :
    CStarMatrix (Fin n) (Fin n) A := fun i j => if i = 0 then a j else 0

/-- The Gram matrix of a finite family of elements of a C⋆-algebra. -/
def gramMatrix {n : ℕ} [NeZero n] (a : Fin n → A) :
    CStarMatrix (Fin n) (Fin n) A := star (rowMatrix a) * rowMatrix a

omit [PartialOrder A] [StarOrderedRing A] in
@[simp]
lemma gramMatrix_apply {n : ℕ} [NeZero n] (a : Fin n → A) (i j : Fin n) :
    gramMatrix a i j = star (a i) * a j := by
  simp [gramMatrix, rowMatrix, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose]

lemma gramMatrix_nonneg {n : ℕ} [NeZero n] (a : Fin n → A) : 0 ≤ gramMatrix a :=
  star_mul_self_nonneg (rowMatrix a)

lemma cpGramMatrix_nonneg {n : ℕ} [NeZero n] (J : A →CP (H →L[ℂ] H)) (a : Fin n → A) :
    0 ≤ (gramMatrix a).map J :=
  J.map_cstarMatrix_nonneg _ (gramMatrix_nonneg a)

lemma cpKernel_inner_nonneg {n : ℕ} [NeZero n] (J : A →CP (H →L[ℂ] H)) (a : Fin n → A)
    (x : PiLp 2 (fun _ : Fin n => H)) :
    0 ≤ ∑ i, ∑ j, inner ℂ (J (star (a i) * a j) (x.ofLp j)) (x.ofLp i) := by
  have h := blockMatrixMap_inner_nonneg (cpGramMatrix_nonneg J a) x
  simpa [gramMatrix_apply] using h

lemma cpKernel_inner_nonneg' {n : ℕ} (J : A →CP (H →L[ℂ] H)) (a : Fin n → A)
    (x : PiLp 2 (fun _ : Fin n => H)) :
    0 ≤ ∑ i, ∑ j, inner ℂ (J (star (a i) * a j) (x.ofLp j)) (x.ofLp i) := by
  rcases n with _ | n
  · simp
  · let _ : NeZero (Nat.succ n) := ⟨Nat.succ_ne_zero n⟩
    exact cpKernel_inner_nonneg J a x

lemma cpKernel_inner_nonneg_natural {n : ℕ} [NeZero n] (J : A →CP (H →L[ℂ] H)) (a : Fin n → A)
    (x : PiLp 2 (fun _ : Fin n => H)) :
    0 ≤ ∑ i, ∑ j, inner ℂ (x.ofLp i) (J (star (a i) * a j) (x.ofLp j)) := by
  have hM : 0 ≤ (star (gramMatrix a)).map J :=
    J.map_cstarMatrix_nonneg _ (star_nonneg_iff.mpr (gramMatrix_nonneg a))
  have h := blockMatrixMap_inner_nonneg hM x
  rw [Finset.sum_comm] at h
  have hterm (i j : Fin n) :
      inner ℂ ((J (star (a j) * a i)) (x.ofLp i)) (x.ofLp j) =
        inner ℂ (x.ofLp i) ((J (star (a i) * a j)) (x.ofLp j)) := by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    have hop : J (star (a j) * a i) =
        ContinuousLinearMap.adjoint (J (star (a i) * a j)) := by
      calc
        J (star (a j) * a i) = J (star (star (a i) * a j)) := by
          congr 1
          simp [star_mul]
        _ = star (J (star (a i) * a j)) :=
          (completelyPositiveMap_map_star_general J _).symm
        _ = ContinuousLinearMap.adjoint (J (star (a i) * a j)) := by
          rfl
    rw [hop]
  have h' : 0 ≤ ∑ i, ∑ j,
      inner ℂ ((J (star (a j) * a i)) (x.ofLp i)) (x.ofLp j) := by
    simpa [gramMatrix_apply, CStarMatrix.star_apply] using h
  have hEq : (∑ i, ∑ j,
      inner ℂ ((J (star (a j) * a i)) (x.ofLp i)) (x.ofLp j)) =
      ∑ i, ∑ j, inner ℂ (x.ofLp i) ((J (star (a i) * a j)) (x.ofLp j)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hterm i j
  rw [← hEq]
  exact h'

lemma cpKernel_inner_nonneg_natural' {n : ℕ} (J : A →CP (H →L[ℂ] H)) (a : Fin n → A)
    (x : PiLp 2 (fun _ : Fin n => H)) :
    0 ≤ ∑ i, ∑ j, inner ℂ (x.ofLp i) (J (star (a i) * a j) (x.ofLp j)) := by
  rcases n with _ | n
  · simp
  · let _ : NeZero (Nat.succ n) := ⟨Nat.succ_ne_zero n⟩
    exact cpKernel_inner_nonneg_natural J a x

/-! ## Stinespring witnesses -/

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A Stinespring witness for a completely positive map into bounded operators.

This is the operator-level form of a dilation: the auxiliary space `K`, the representation `π`,
and the implementing operator `V` are data of the witness. Existence of such a witness (for every
CP map) is `Dilation.lean`'s canonical construction, kept as a separate theorem rather than an
instance or an axiom. -/
structure StinespringWitness (A H K : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (J : A →CP (H →L[ℂ] H)) where
  /-- The representation of the input operator algebra on the auxiliary space. -/
  representation : A →⋆ₐ[ℂ] (K →L[ℂ] K)
  /-- The implementing bounded operator from the physical space to the auxiliary space. -/
  implementing : H →L[ℂ] K
  /-- The Stinespring identity: `J a = V⋆ π(a) V`. -/
  map_eq : ∀ a : A,
    J a = ContinuousLinearMap.adjoint implementing ∘L
      (representation a) ∘L implementing

namespace StinespringWitness

variable {J : A →CP (H →L[ℂ] H)} (W : StinespringWitness A H K J)

lemma map_eq_apply (a : A) :
    J a = ContinuousLinearMap.adjoint W.implementing ∘L
      (W.representation a) ∘L W.implementing :=
  W.map_eq a

end StinespringWitness
