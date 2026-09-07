/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.RootDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.SU3PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
/-!
# Gauge tensors carrying two `su(3)` adjoint indices

A gluon field strength `F^a` carries one colour index `a`, running over the eight Gell-Mann
directions of `su(3)`. A product of two field strengths carries two, and the combination
that enters the Yang–Mills Lagrangian is the colour trace `∑ a, F^a F^a`. This file proves
the group theory behind that choice, in the form the Standard Model files consume: among
all combinations of the components of such a product, the multiples of the trace are the
only ones every colour rotation leaves alone. In the language of representation theory,
`8 ⊗ 8 = 1 ⊕ 8 ⊕ 8 ⊕ 10 ⊕ 10̄ ⊕ 27` contains exactly one singlet, the Kronecker delta.

`IsSU3BiAdjoint B repGauge T` records the hypothesis. `T` is a family indexed by two colour
indices and valued in a module `B` carrying a representation `repGauge` of the gauge group,
and a colour rotation `U ∈ SU(3)` moves its components by two copies of the adjoint matrix
of `U`, as a rank two tensor `T^{a b}` should. Nothing is asked of the isospin and
hypercharge factors: a product of coloured fields may well carry hypercharge, and the
conclusions are accordingly about invariance under colour.

The theorem, `mem_span_sup_su3_invariant_iff`, is stated modulo a colour-stable submodule
`S`, because the Standard Model files handle many families at once and peel them off one
at a time: a colour invariant in the span of the components joined with `S` is a multiple
of the trace contraction up to a colour-invariant error in `S`.

The proof has two halves, and neither needs more than the module structure of `B`.

The first half is the linear algebra of `Invariants.Basic`. A vector of the span is
`∑ l, c l • T l` for a coefficient function `c` on pairs of colour indices, and a colour
rotation acts on `c` by the Kronecker square of its adjoint matrix, a unitary action. So an
invariant vector of the span is the contraction of an invariant coefficient
(`Family.exists_invariant_coeff`), and the question becomes a finite one.

The second half is a finite computation. An invariant coefficient is a bilinear form on
colour coordinates fixed by every colour rotation, and a handful of explicit rotations pin
it down. The colour parities, the diagonal sign matrices of `SU(3)`, scale each Gell-Mann
direction by a sign and kill every entry joining two directions of different sign pattern.
The cyclic permutation and the transposition of colours, the Weyl group, equate the diagonal
entries along the root directions, equate them in the Cartan plane and kill the
antisymmetric entries. Two rotations inside the `SU(2)` of the first two colours carry a
Cartan direction onto the two members of a root pair and tie the Cartan entries to the root
entries. So the form is a multiple of the Kronecker delta and the vector a multiple of the
trace.

Section A sets up the adjoint matrix and the transformation law. Section B has the span,
the action on coefficients and the trace contraction. Section C has the coordinate vectors
of one index, section D computes the rotations on them, section E is the finite
computation, section F classifies the invariants of the span, and section G divides out a
stable submodule and proves the theorem. An aside at the end holds what other files import
from here and the theorem does not use: the weight basis of the adjoint, the quotient and
square-zero representations, and the gauge form of the theorem.
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The adjoint action of `SU(3)` on a colour index

## A.1. The adjoint matrix

Conjugating a Gell-Mann matrix by `U ∈ SU(3)` gives another traceless hermitian matrix,
and `su3AdjointMatrix U` holds its coordinates in the Gell-Mann basis, read off with the
trace pairing. By definition it is the `su(3)` block of `GaugeAlgebra.adjointMatrix` at the
colour rotation `(U, 1, 1)`, so it is orthogonal, the identity at `U = 1` and transposed at
`U⁻¹`, all of which is inherited from there.

-/

/-- The adjoint matrix of `U ∈ SU(3)`: the trace pairing of the Gell-Mann basis with the
  Gell-Mann basis conjugated by `U`. -/
noncomputable def su3AdjointMatrix (U : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of fun i j =>
    2⁻¹ * (Matrix.trace (gellMannMatrix i * (U.1 * gellMannMatrix j * star U.1))).re

/-- The entries of the adjoint matrix. -/
@[simp]
lemma su3AdjointMatrix_apply (U : specialUnitaryGroup (Fin 3) ℂ) (i j : Fin 8) :
    su3AdjointMatrix U i j
      = 2⁻¹ * (Matrix.trace (gellMannMatrix i * (U.1 * gellMannMatrix j * star U.1))).re :=
  rfl

/-- The rows of the adjoint matrix are orthonormal. -/
lemma sum_su3AdjointMatrix_row_mul (U : specialUnitaryGroup (Fin 3) ℂ) (c d : Fin 8) :
    ∑ a : Fin 8, su3AdjointMatrix U c a * su3AdjointMatrix U d a
      = if c = d then 1 else 0 :=
  GaugeAlgebra.sum_adjointMatrix_inl_row_mul (U, 1, 1) c d

/-- The adjoint matrix of the identity is the identity. -/
lemma su3AdjointMatrix_one (a b : Fin 8) :
    su3AdjointMatrix 1 a b = if a = b then 1 else 0 := by
  have h := congrFun (congrFun GaugeAlgebra.adjointMatrix_one (Sum.inl a)) (Sum.inl b)
  rw [Matrix.one_apply] at h
  simpa [su3AdjointMatrix_apply] using h

/-- The adjoint matrix of the inverse is the transpose. -/
lemma su3AdjointMatrix_inv (U : specialUnitaryGroup (Fin 3) ℂ) (a b : Fin 8) :
    su3AdjointMatrix U⁻¹ a b = su3AdjointMatrix U b a := by
  have h := GaugeAlgebra.adjointMatrix_inv_apply (U, 1, 1) (Sum.inl a) (Sum.inl b)
  rwa [show ((U, 1, 1) : GaugeGroupI)⁻¹ = (U⁻¹, 1, 1) from by simp] at h

/-- The Gell-Mann matrices are orthonormal for the trace pairing: this is the adjoint
  matrix of the identity, read entry by entry. -/
lemma re_trace_gellMannMatrix_mul (a b : Fin 8) :
    2⁻¹ * (Matrix.trace (gellMannMatrix a * gellMannMatrix b)).re
      = if a = b then 1 else 0 := by
  rw [← su3AdjointMatrix_one a b, su3AdjointMatrix_apply]
  simp

/-- An entry of the adjoint matrix is a Gell-Mann coordinate of a conjugated Gell-Mann
  matrix. -/
lemma su3AdjointMatrix_eq_gellMannCoeff (U : specialUnitaryGroup (Fin 3) ℂ) (a b : Fin 8) :
    su3AdjointMatrix U a b = gellMannCoeff (U.1 * gellMannMatrix b * star U.1) a := by
  have hmem := GaugeAlgebra.conj_mem U.2.1
    (gellMannMatrix_selfAdjoint b) (gellMannMatrix_trace b)
  rw [su3AdjointMatrix_apply, gellMannCoeff_eq_trace hmem.1 hmem.2]

/-!

## A.2. Bi-adjoint families

The transformation law carries one factor of the adjoint matrix per index, with the summed
index in the row slot. `IsSU3BiAdjointMat` records it for one linear map and one element
of `SU(3)`, and `IsSU3BiAdjoint` asks it of the colour rotation `(U, 1, 1)` for every `U`.
Since `U ↦ (U, 1, 1)` is a homomorphism this is an action of `SU(3)`, and it is all that
is assumed.

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with two
  adjoint indices: one factor of the adjoint matrix per index. -/
def IsSU3BiAdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 3) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 8) → B) : Prop :=
  ∀ l : Fin 2 → Fin 8,
    f (T l) = ∑ a : Fin 2 → Fin 8,
      (∏ i : Fin 2, ((su3AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a

/-- A family `T` of elements of `B`, indexed by two `su(3)` adjoint indices, transforms
  as a tensor `T^{a b}` under the colour factor of the gauge group. Nothing is asked of the
  isospin and hypercharge factors. -/
structure IsSU3BiAdjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 8) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 3) ℂ,
    IsSU3BiAdjointMat g (repGauge (g, 1, 1)) T

namespace IsSU3BiAdjoint

/- `span`, `traceContraction` and `biVec` take the hypothesis `hT` only to hang off it by
dot notation, and `mem_span_sup_invariant_iff` keeps a hypothesis for its caller; each is
marked `nolint unusedArguments` where it is declared. -/
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 8) → B}

/-!

## B. Coefficients, their action and the trace

A vector of the span of the components is a contraction `∑ l, c l • T l` against a
coefficient function `c` on pairs of colour indices, and the transformation law says exactly
that a colour rotation moves such a contraction by moving `c` with the Kronecker square of
its adjoint matrix, `act U`. Orthogonality of the adjoint matrix makes `act U⁻¹` the
transpose of `act U`, and the matrix being real, `act U` commutes with conjugation: these are
the two hypotheses of `Family.exists_invariant_coeff`. The trace contraction
`∑ a, T ![a, a]` is the contraction against the Kronecker delta `traceCoeff`, and it is
colour invariant because the delta is an invariant coefficient.

-/

/-- The span of the components. -/
@[nolint unusedArguments]
def span (hT : IsSU3BiAdjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span precisely when it is a linear combination of the
  components. -/
lemma mem_span_iff (hT : IsSU3BiAdjoint B repGauge T) (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 2 → Fin 8) → ℂ), x = ∑ d, c d • T d :=
  Family.mem_iSup_span_singleton_iff T x

/-- A sum over pairs of colour indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 8) → M) :
    ∑ d : Fin 2 → Fin 8, F d = ∑ x : Fin 8, ∑ y : Fin 8, F ![x, y] :=
  Family.sum_pi_two F

/-- The action of `U ∈ SU(3)` on coefficient functions: the Kronecker square of its
  adjoint matrix. -/
noncomputable def act (U : specialUnitaryGroup (Fin 3) ℂ) :
    ((Fin 2 → Fin 8) → ℂ) →ₗ[ℂ] (Fin 2 → Fin 8) → ℂ :=
  Matrix.toLin' (Matrix.of fun a l =>
    ∏ i : Fin 2, ((su3AdjointMatrix U (a i) (l i) : ℝ) : ℂ))

/-- The action on coefficients, written out. -/
lemma act_apply (U : specialUnitaryGroup (Fin 3) ℂ) (c : (Fin 2 → Fin 8) → ℂ)
    (a : Fin 2 → Fin 8) :
    act U c a = ∑ l, (∏ i : Fin 2, ((su3AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) * c l := by
  simp [act, Matrix.mulVec, dotProduct]

/-- The transformation law in coefficient form: a map moving the components by `U` moves a
  contraction by `act U` on its coefficients. -/
lemma map_sum_smul {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU3BiAdjointMat U f T) (c : (Fin 2 → Fin 8) → ℂ) :
    f (∑ l, c l • T l) = ∑ a, act U c a • T a := by
  simp only [map_sum, map_smul, act_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hf l, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [smul_smul, mul_comm]

/-- The action of `U⁻¹` is the transpose of the action of `U`, the adjoint matrix being
  orthogonal. -/
lemma sum_act_mul (U : specialUnitaryGroup (Fin 3) ℂ) (c d : (Fin 2 → Fin 8) → ℂ) :
    ∑ a, act U c a * d a = ∑ l, c l * act U⁻¹ d l := by
  simp only [act_apply, su3AdjointMatrix_inv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring

/-- The action on coefficients commutes with complex conjugation, the adjoint matrix being
  real. -/
lemma act_star (U : specialUnitaryGroup (Fin 3) ℂ) (c : (Fin 2 → Fin 8) → ℂ) :
    act U (star c) = star (act U c) := by
  funext a
  simp [act_apply, star_sum, star_mul', Complex.conj_ofReal]

/-- The Kronecker delta on pairs of colour indices: the coefficients of the trace. -/
def traceCoeff : (Fin 2 → Fin 8) → ℂ := fun l => if l 0 = l 1 then 1 else 0

/-- The Kronecker delta is an invariant coefficient: the rows of the adjoint matrix are
  orthonormal. -/
lemma act_traceCoeff (U : specialUnitaryGroup (Fin 3) ℂ) : act U traceCoeff = traceCoeff := by
  funext a
  rw [act_apply, sum_pi_two]
  have key : ∀ x y : Fin 8,
      (∏ i : Fin 2, ((su3AdjointMatrix U (a i) (![x, y] i) : ℝ) : ℂ)) * traceCoeff ![x, y]
        = if y = x then
            ((su3AdjointMatrix U (a 0) x * su3AdjointMatrix U (a 1) x : ℝ) : ℂ) else 0 := by
    intro x y
    by_cases h : y = x
    · subst h
      simp [traceCoeff, Fin.prod_univ_two]
    · simp [traceCoeff, Fin.prod_univ_two, h, Ne.symm h]
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Complex.ofReal_sum,
    sum_su3AdjointMatrix_row_mul]
  by_cases h : a 0 = a 1 <;> simp [traceCoeff, h]

/-- The trace contraction: the Kronecker contraction of the two colour indices. -/
@[nolint unusedArguments]
def traceContraction (hT : IsSU3BiAdjoint B repGauge T) : B := ∑ a : Fin 8, T ![a, a]

/-- The trace is the contraction against the Kronecker delta. -/
lemma sum_traceCoeff_smul (T : (Fin 2 → Fin 8) → B) :
    ∑ l, traceCoeff l • T l = ∑ a : Fin 8, T ![a, a] := by
  rw [sum_pi_two]
  simp [traceCoeff, ite_smul]

/-- Any map moving the components by an `SU(3)` matrix fixes the trace contraction. -/
lemma map_traceContraction (hT : IsSU3BiAdjoint B repGauge T)
    {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B} (hf : IsSU3BiAdjointMat U f T) :
    f hT.traceContraction = hT.traceContraction := by
  rw [traceContraction, ← sum_traceCoeff_smul, map_sum_smul hf, act_traceCoeff]

/-- The trace contraction is colour invariant. Nothing constrains the isospin and
  hypercharge factors, which may well move it. -/
lemma repGauge_traceContraction (hT : IsSU3BiAdjoint B repGauge T)
    (U : specialUnitaryGroup (Fin 3) ℂ) :
    repGauge (U, 1, 1) hT.traceContraction = hT.traceContraction :=
  hT.map_traceContraction (hT.repGauge_T U)

/-!

## C. Coordinate vectors of one index

The action of `U` on a single adjoint index is the row action `rowAct U` of its adjoint
matrix on coordinate vectors `Fin 8 → ℂ`, and `unitVec a` is the coordinate vector of the
Gell-Mann direction `a`. Sections D and E work entirely with these.

-/

/-- The coordinate vector of a single Gell-Mann direction. -/
def unitVec (a : Fin 8) : Fin 8 → ℂ := fun x => if x = a then 1 else 0

/-- The action of `U ∈ SU(3)` on the coordinates of one adjoint index. -/
noncomputable def rowAct (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 8 → ℂ) :
    Fin 8 → ℂ := fun a =>
  ∑ x : Fin 8, ((su3AdjointMatrix U a x : ℝ) : ℂ) * c x

/-- The row action is additive. -/
lemma rowAct_add (U : specialUnitaryGroup (Fin 3) ℂ) (c c' : Fin 8 → ℂ) :
    rowAct U (c + c') = rowAct U c + rowAct U c' := by
  funext a
  simp only [rowAct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The row action respects differences. -/
lemma rowAct_sub (U : specialUnitaryGroup (Fin 3) ℂ) (c c' : Fin 8 → ℂ) :
    rowAct U (c - c') = rowAct U c - rowAct U c' := by
  funext a
  simp only [rowAct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The row action is homogeneous. -/
lemma rowAct_smul (U : specialUnitaryGroup (Fin 3) ℂ) (z : ℂ) (c : Fin 8 → ℂ) :
    rowAct U (z • c) = z • rowAct U c := by
  funext a
  simp only [rowAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The row action on a Gell-Mann direction is a column of the adjoint matrix. -/
lemma rowAct_unitVec (U : specialUnitaryGroup (Fin 3) ℂ) (b a : Fin 8) :
    rowAct U (unitVec b) a = ((su3AdjointMatrix U a b : ℝ) : ℂ) := by
  simp only [rowAct, unitVec, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-!

## D. A handful of colour rotations on coordinate vectors

The classification of section E tests an invariant form against a few elements of `SU(3)`,
and this section computes what each does to the coordinate vectors of one index. Each
computation is the same: conjugate the Gell-Mann matrices by the element, read off the
adjoint matrix, and hence the row action on `unitVec`.

## D.1. The colour parities

The diagonal matrices of `SU(3)` with entries `±1` are the identity and the three parities
`su3Parity k`, which fix the colour `k` and reverse the other two. Conjugation by a parity
scales a Gell-Mann matrix by the product of the two diagonal entries it pairs, which is a
sign `paritySign`, so each Gell-Mann direction is an eigenvector of every parity.

-/

/-- The colour parity fixing the colour `k` and reversing the other two. -/
noncomputable def su3Parity (k : Fin 3) : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨Matrix.diagonal fun i => if i = k then 1 else -1,
    Matrix.mem_specialUnitaryGroup_diagonal _ (fun i => by split_ifs <;> simp)
      (by fin_cases k <;> simp [Fin.prod_univ_three])⟩

/-- The sign by which the parity `k` scales each Gell-Mann direction: `-1` on the four root
  directions pairing the colour `k` with another, `1` on the rest. -/
def paritySign : Fin 3 → Fin 8 → ℤ
  | 0 => ![-1, -1, 1, -1, -1, 1, 1, 1]
  | 1 => ![-1, -1, 1, 1, 1, -1, -1, 1]
  | 2 => ![1, 1, 1, -1, -1, -1, -1, 1]

/-- Conjugation by a parity scales each Gell-Mann matrix by its sign. -/
lemma conj_gellMannMatrix_su3Parity (k : Fin 3) (b : Fin 8) :
    (su3Parity k).1 * gellMannMatrix b * star (su3Parity k).1
      = ((paritySign k b : ℤ) : ℂ) • gellMannMatrix b := by
  rw [show (su3Parity k).1 = Matrix.diagonal fun i => if i = k then (1 : ℂ) else -1 from rfl,
    Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases k <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [paritySign, gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two,
      gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six,
      gellMannMatrix_seven]

/-- The adjoint matrix of a parity is diagonal, with the signs on the diagonal. -/
lemma su3AdjointMatrix_su3Parity (k : Fin 3) (a b : Fin 8) :
    su3AdjointMatrix (su3Parity k) a b = if a = b then (paritySign k b : ℝ) else 0 := by
  rw [su3AdjointMatrix_apply, conj_gellMannMatrix_su3Parity, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_intCast, Complex.re_ofReal_mul,
    mul_left_comm, re_trace_gellMannMatrix_mul]
  by_cases h : a = b <;> simp [h]

/-- A parity scales each Gell-Mann direction by its sign. -/
lemma rowAct_su3Parity_unitVec (k : Fin 3) (b : Fin 8) :
    rowAct (su3Parity k) (unitVec b) = ((paritySign k b : ℤ) : ℂ) • unitVec b := by
  funext a
  rw [rowAct_unitVec, su3AdjointMatrix_su3Parity]
  by_cases h : a = b <;> simp [unitVec, h]

/-!

## D.2. The cyclic colour rotation

Conjugation by the cyclic permutation matrix `su3Perm` permutes the matrix units, hence the
Gell-Mann matrices up to signs; only the two Cartan directions are mixed, by a rotation
through `2 π / 3`. On the Cartan plane the rotation is diagonalised by the combinations
`x₂ ∓ i x₇`, recorded in `cartanVec`, with eigenvalues `ω` and `ω ^ 2`.

-/

/-- The star of the cyclic colour matrix is the matrix of the inverse cycle. -/
lemma star_su3PermMatrix :
    star !![(0 : ℂ), 0, 1; 1, 0, 0; 0, 1, 0] = !![(0 : ℂ), 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The conjugate of each Gell-Mann matrix by the cyclic colour rotation. -/
noncomputable def permGellMann : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => !![0, 0, 0; 0, 0, 1; 0, 1, 0]
  | 1 => !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0]
  | 2 => !![0, 0, 0; 0, 1, 0; 0, 0, -1]
  | 3 => !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  | 4 => !![0, Complex.I, 0; -Complex.I, 0, 0; 0, 0, 0]
  | 5 => !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  | 6 => !![0, 0, Complex.I; 0, 0, 0; -Complex.I, 0, 0]
  | 7 => !![((-2 * (Real.sqrt 3)⁻¹ : ℝ) : ℂ), 0, 0;
            0, (((Real.sqrt 3)⁻¹ : ℝ) : ℂ), 0;
            0, 0, (((Real.sqrt 3)⁻¹ : ℝ) : ℂ)]

/-- Conjugating a Gell-Mann matrix by the cyclic colour rotation. -/
lemma conj_gellMannMatrix_su3Perm (b : Fin 8) :
    su3Perm.1 * gellMannMatrix b * star su3Perm.1 = permGellMann b := by
  rw [su3Perm_coe, star_su3PermMatrix]
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [permGellMann, gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two,
      gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six,
      gellMannMatrix_seven, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

/-- The image of each Gell-Mann direction under the cyclic colour rotation: the six root
  directions are permuted up to sign, the two Cartan directions rotated into each other. -/
noncomputable def permCol : Fin 8 → Fin 8 → ℂ
  | 0 => unitVec 5
  | 1 => unitVec 6
  | 2 => -(2 : ℂ)⁻¹ • unitVec 2 + (((Real.sqrt 3 : ℝ) : ℂ) / 2) • unitVec 7
  | 3 => unitVec 0
  | 4 => -unitVec 1
  | 5 => unitVec 3
  | 6 => -unitVec 4
  | 7 => -((((Real.sqrt 3 : ℝ) : ℂ) / 2) • unitVec 2) - (2 : ℂ)⁻¹ • unitVec 7

/-- The cyclic colour rotation on the Gell-Mann directions. -/
lemma rowAct_su3Perm_unitVec (b : Fin 8) :
    rowAct su3Perm (unitVec b) = permCol b := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  funext a
  rw [rowAct_unitVec, su3AdjointMatrix_eq_gellMannCoeff, conj_gellMannMatrix_su3Perm]
  fin_cases b <;> fin_cases a <;> simp [permGellMann, gellMannCoeff, permCol, unitVec]
  all_goals first
    | ring1
    | linear_combination (-(1 : ℂ) / 6) * h3

/-- The two eigenvectors of the cyclic colour rotation in the Cartan plane, the
  combinations `x₂ ∓ i x₇` of the two Cartan coordinates. -/
noncomputable def cartanVec : Fin 2 → Fin 8 → ℂ
  | 0 => unitVec 2 - Complex.I • unitVec 7
  | 1 => unitVec 2 + Complex.I • unitVec 7

/-- The grade of each Cartan eigenvector: its eigenvalue is `ω ^ cartanGrade`. -/
def cartanGrade : Fin 2 → ZMod 3
  | 0 => 1
  | 1 => 2

/-- The cube root of unity `ω = exp (2 π i / 3)`, written out. -/
lemma su3Omega_eq : su3Omega = -2⁻¹ + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  have h : (2 * (Real.pi : ℂ) * Complex.I / 3)
      = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [su3Omega, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- The square of `ω`, written out. -/
lemma su3Omega_sq : su3Omega ^ 2 = -2⁻¹ - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [su3Omega_eq]
  push_cast
  linear_combination (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq + (-(1 : ℂ) / 4) * h3

/-- The grade one sign `ω`, written out. -/
lemma su3PermSign_one_eq :
    su3PermSign 1 = -2⁻¹ + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [su3PermSign_one, su3Omega_eq]

/-- The grade two sign `ω ^ 2`, written out. -/
lemma su3PermSign_two_eq :
    su3PermSign 2 = -2⁻¹ - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [su3PermSign_two, su3Omega_sq]

/-- The cyclic colour rotation scales each Cartan eigenvector by the cube root of unity of
  its grade. -/
lemma rowAct_su3Perm_cartanVec (c : Fin 2) :
    rowAct su3Perm (cartanVec c) = su3PermSign (cartanGrade c) • cartanVec c := by
  fin_cases c <;>
    simp only [cartanVec, cartanGrade, rowAct_sub, rowAct_add, rowAct_smul,
      rowAct_su3Perm_unitVec, permCol, su3PermSign_one_eq, su3PermSign_two_eq] <;>
    match_scalars
  all_goals ring_nf
  all_goals try simp only [Complex.I_sq]
  all_goals ring1

/-- The first Cartan direction in the eigenbasis of the cyclic colour rotation. -/
lemma unitVec_two_eq_cartanVec_add :
    unitVec 2 = (2 : ℂ)⁻¹ • (cartanVec 0 + cartanVec 1) := by
  simp only [cartanVec]
  module

/-- The second Cartan direction in the eigenbasis of the cyclic colour rotation. -/
lemma unitVec_seven_eq_cartanVec_sub :
    unitVec 7 = (Complex.I / 2) • (cartanVec 0 - cartanVec 1) := by
  simp only [cartanVec]
  match_scalars
  all_goals first
    | ring1
    | linear_combination Complex.I_sq

/-!

## D.3. The colour transposition

Conjugation by the transposition `su3Transp` of the first two colours permutes the
Gell-Mann matrices up to signs, without mixing any two of them: it fixes the first root pair
up to the sign of its second member, exchanges the other two root pairs, and negates the
first Cartan direction while fixing the second.

-/

/-- The transposition matrix is real and symmetric, so it is its own star. -/
lemma star_su3TranspMatrix :
    star !![(0 : ℂ), -1, 0; -1, 0, 0; 0, 0, -1] = !![(0 : ℂ), -1, 0; -1, 0, 0; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The conjugate of each Gell-Mann matrix by the transposition. -/
noncomputable def transpGellMann : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => gellMannMatrix 0
  | 1 => -gellMannMatrix 1
  | 2 => -gellMannMatrix 2
  | 3 => gellMannMatrix 5
  | 4 => gellMannMatrix 6
  | 5 => gellMannMatrix 3
  | 6 => gellMannMatrix 4
  | 7 => gellMannMatrix 7

/-- Conjugating a Gell-Mann matrix by the transposition. -/
lemma conj_gellMannMatrix_su3Transp (b : Fin 8) :
    su3Transp.1 * gellMannMatrix b * star su3Transp.1 = transpGellMann b := by
  rw [su3Transp_coe, star_su3TranspMatrix]
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [transpGellMann, gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two,
      gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six,
      gellMannMatrix_seven, Matrix.mul_apply, Fin.sum_univ_three]

/-- The image of each Gell-Mann direction under the transposition. -/
noncomputable def transpCol : Fin 8 → Fin 8 → ℂ
  | 0 => unitVec 0
  | 1 => -unitVec 1
  | 2 => -unitVec 2
  | 3 => unitVec 5
  | 4 => unitVec 6
  | 5 => unitVec 3
  | 6 => unitVec 4
  | 7 => unitVec 7

/-- The transposition on the Gell-Mann directions. -/
lemma rowAct_su3Transp_unitVec (b : Fin 8) :
    rowAct su3Transp (unitVec b) = transpCol b := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  funext a
  rw [rowAct_unitVec, su3AdjointMatrix_eq_gellMannCoeff, conj_gellMannMatrix_su3Transp]
  fin_cases b <;> fin_cases a <;>
    simp [transpGellMann, gellMannCoeff, transpCol, unitVec, gellMannMatrix_zero,
      gellMannMatrix_one, gellMannMatrix_two, gellMannMatrix_three, gellMannMatrix_four,
      gellMannMatrix_five, gellMannMatrix_six, gellMannMatrix_seven]
  all_goals first
    | linear_combination ((1 : ℂ) / 3) * h3
    | norm_num

/-!

## D.4. Two turns in the `SU(2)` of the first two colours

Everything so far normalises the colour torus, and nothing in the normaliser can tell the
Cartan plane from the root directions. The directions `λ₁`, `λ₂`, `λ₃` span an `su(2)`
acting on the first two colours, on which the corresponding `SU(2)` acts by rotations, and
the turn `su3Turn v` with `u = (1 + i) / 2` and `|v| = |u|` carries `λ₃` onto the root
direction `-2 u v`. Two turns are used: `su3TurnFst` lands on `-λ₁` and `su3TurnSnd` on
`λ₂`, since the Weyl group never mixes the two members of a root pair.

-/

/-- The block `!![u, v; -conj v, conj u]` at `u = (1 + i) / 2`, with the third colour
  fixed. -/
noncomputable def su3TurnMatrix (v : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(1 + Complex.I) / 2, v, 0; -(starRingEnd ℂ) v, (1 - Complex.I) / 2, 0; 0, 0, 1]

/-- The star of a turn matrix. -/
lemma star_su3TurnMatrix (v : ℂ) :
    star (su3TurnMatrix v)
      = !![(1 - Complex.I) / 2, -v, 0; (starRingEnd ℂ) v, (1 + Complex.I) / 2, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su3TurnMatrix, Complex.ext_iff]

/-- A turn matrix lies in `SU(3)` when its off-diagonal entry has the modulus of the
  diagonal one. -/
lemma su3TurnMatrix_mem {v : ℂ} (hv : v * (starRingEnd ℂ) v = 2⁻¹) :
    su3TurnMatrix v ∈ specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_su3TurnMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [su3TurnMatrix, Matrix.mul_apply, Fin.sum_univ_three]
    all_goals first
      | ring1
      | linear_combination hv - (1 / 4 : ℂ) * Complex.I_sq
  · rw [Matrix.det_fin_three]
    simp [su3TurnMatrix]
    all_goals first
      | ring1
      | linear_combination hv - (1 / 4 : ℂ) * Complex.I_sq

/-- A turn as an element of `SU(3)`. -/
noncomputable def su3Turn (v : ℂ) (hv : v * (starRingEnd ℂ) v = 2⁻¹) :
    specialUnitaryGroup (Fin 3) ℂ := ⟨su3TurnMatrix v, su3TurnMatrix_mem hv⟩

/-- Conjugating the first Cartan direction by a turn: the diagonal cancels, and what is left
  is a combination of the two members of the first root pair. -/
lemma conj_gellMannMatrix_two_su3Turn {v : ℂ} (hv : v * (starRingEnd ℂ) v = 2⁻¹) :
    (su3Turn v hv).1 * gellMannMatrix 2 * star (su3Turn v hv).1
      = !![0, -((1 + Complex.I) * v), 0;
          -((1 - Complex.I) * (starRingEnd ℂ) v), 0, 0;
          0, 0, 0] := by
  rw [show (su3Turn v hv).1 = su3TurnMatrix v from rfl, star_su3TurnMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su3TurnMatrix, gellMannMatrix_two, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first
    | ring1
    | linear_combination hv - (1 / 4 : ℂ) * Complex.I_sq
    | linear_combination -hv + (1 / 4 : ℂ) * Complex.I_sq
    | linear_combination hv + (1 / 4 : ℂ) * Complex.I_sq
    | linear_combination -hv - (1 / 4 : ℂ) * Complex.I_sq

/-- The first turn, at `v = (1 - i) / 2`. -/
noncomputable def su3TurnFst : specialUnitaryGroup (Fin 3) ℂ :=
  su3Turn ((1 - Complex.I) / 2)
    (by rw [map_div₀, map_sub, map_one, Complex.conj_I, map_ofNat]
        linear_combination (-1 / 4 : ℂ) * Complex.I_sq)

/-- The second turn, at `v = (1 + i) / 2`. -/
noncomputable def su3TurnSnd : specialUnitaryGroup (Fin 3) ℂ :=
  su3Turn ((1 + Complex.I) / 2)
    (by rw [map_div₀, map_add, map_one, Complex.conj_I, map_ofNat]
        linear_combination (-1 / 4 : ℂ) * Complex.I_sq)

/-- The first turn carries the first Cartan direction to minus the first member of the
  first root pair. -/
lemma rowAct_su3TurnFst_unitVec_two :
    rowAct su3TurnFst (unitVec 2) = -unitVec 0 := by
  funext a
  rw [su3TurnFst, rowAct_unitVec, su3AdjointMatrix_eq_gellMannCoeff,
    conj_gellMannMatrix_two_su3Turn]
  fin_cases a <;> simp [gellMannCoeff, unitVec]
  all_goals norm_num

/-- The second turn carries the first Cartan direction to the second member of the first
  root pair. -/
lemma rowAct_su3TurnSnd_unitVec_two :
    rowAct su3TurnSnd (unitVec 2) = unitVec 1 := by
  funext a
  rw [su3TurnSnd, rowAct_unitVec, su3AdjointMatrix_eq_gellMannCoeff,
    conj_gellMannMatrix_two_su3Turn]
  fin_cases a <;> simp [gellMannCoeff, unitVec]
  all_goals norm_num

/-!

## E. An invariant coefficient is a multiple of the Kronecker delta

A coefficient `c` is a bilinear form `form c` on coordinate vectors, with `c ![a, b]` the
value on two Gell-Mann directions. If `c` is fixed by every `act U`, the form is fixed by
every row action, and the rotations of section D read off its entries: the parities
kill the entries joining directions of different sign pattern, the transposition and the
cyclic rotation kill the remaining off-diagonal entries and equate the diagonal ones within
the root directions and within the Cartan plane, and the two turns equate a Cartan diagonal
entry with a root one. What is left is a multiple of the delta.

-/

/-- The bilinear form on coordinate vectors with coefficients `c`. -/
def form (c : (Fin 2 → Fin 8) → ℂ) (v w : Fin 8 → ℂ) : ℂ :=
  ∑ l, v (l 0) * w (l 1) * c l

/-- The form on two Gell-Mann directions is an entry of `c`. -/
lemma form_unitVec (c : (Fin 2 → Fin 8) → ℂ) (a b : Fin 8) :
    form c (unitVec a) (unitVec b) = c ![a, b] := by
  rw [form, sum_pi_two, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [unitVec]
  · intro y _ hy
    simp [unitVec, hy]
  · simp
  · intro x _ hx
    simp [unitVec, hx]
  · simp

/-- The form is additive on the left. -/
lemma form_add_left (c : (Fin 2 → Fin 8) → ℂ) (v v' w : Fin 8 → ℂ) :
    form c (v + v') w = form c v w + form c v' w := by
  simp only [form, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The form is additive on the right. -/
lemma form_add_right (c : (Fin 2 → Fin 8) → ℂ) (v w w' : Fin 8 → ℂ) :
    form c v (w + w') = form c v w + form c v w' := by
  simp only [form, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- The form respects differences on the left. -/
lemma form_sub_left (c : (Fin 2 → Fin 8) → ℂ) (v v' w : Fin 8 → ℂ) :
    form c (v - v') w = form c v w - form c v' w := by
  simp only [form, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The form respects differences on the right. -/
lemma form_sub_right (c : (Fin 2 → Fin 8) → ℂ) (v w w' : Fin 8 → ℂ) :
    form c v (w - w') = form c v w - form c v w' := by
  simp only [form, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- The form is homogeneous on the left. -/
lemma form_smul_left (c : (Fin 2 → Fin 8) → ℂ) (z : ℂ) (v w : Fin 8 → ℂ) :
    form c (z • v) w = z * form c v w := by
  simp only [form, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The form is homogeneous on the right. -/
lemma form_smul_right (c : (Fin 2 → Fin 8) → ℂ) (z : ℂ) (v w : Fin 8 → ℂ) :
    form c v (z • w) = z * form c v w := by
  simp only [form, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- The form on a negated left argument. -/
lemma form_neg_left (c : (Fin 2 → Fin 8) → ℂ) (v w : Fin 8 → ℂ) :
    form c (-v) w = -form c v w := by
  simp only [form, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- The form on a negated right argument. -/
lemma form_neg_right (c : (Fin 2 → Fin 8) → ℂ) (v w : Fin 8 → ℂ) :
    form c v (-w) = -form c v w := by
  simp only [form, Pi.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]

/-- The form of an invariant coefficient is fixed by every row action: the row action on a
  product of coordinate vectors is `act U` on the product coefficient, and `act U⁻¹` is the
  transpose of `act U`. -/
lemma form_rowAct {c : (Fin 2 → Fin 8) → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 3) ℂ, act U c = c)
    (U : specialUnitaryGroup (Fin 3) ℂ) (v w : Fin 8 → ℂ) :
    form c (rowAct U v) (rowAct U w) = form c v w := by
  have key : ∀ l : Fin 2 → Fin 8,
      rowAct U v (l 0) * rowAct U w (l 1) = act U (fun m => v (m 0) * w (m 1)) l := by
    intro l
    simp only [rowAct, act_apply, Fin.prod_univ_two]
    rw [sum_pi_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  simp only [form, key]
  rw [sum_act_mul, hc]

/-- An invariant coefficient is a multiple of the Kronecker delta. -/
theorem exists_smul_traceCoeff_of_act_eq {c : (Fin 2 → Fin 8) → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 3) ℂ, act U c = c) :
    ∃ z : ℂ, c = z • traceCoeff := by
  have hβ := form_rowAct hc
  -- the parities kill every entry joining two directions of different sign pattern
  have hpar : ∀ (k : Fin 3) (a b : Fin 8),
      paritySign k a ≠ paritySign k b → c ![a, b] = 0 := by
    intro k a b hab
    have h := hβ (su3Parity k) (unitVec a) (unitVec b)
    rw [rowAct_su3Parity_unitVec, rowAct_su3Parity_unitVec, form_smul_left, form_smul_right,
      form_unitVec, ← mul_assoc] at h
    have hpm : ∀ (k : Fin 3) (a : Fin 8), paritySign k a = 1 ∨ paritySign k a = -1 := by
      decide
    rcases hpm k a with ha | ha <;> rcases hpm k b with hb | hb <;> rw [ha, hb] at h hab <;>
      push_cast at h
    · exact absurd rfl hab
    · linear_combination (-1 / 2 : ℂ) * h
    · linear_combination (-1 / 2 : ℂ) * h
    · exact absurd rfl hab
  -- the transposition and the cyclic rotation, on Gell-Mann directions
  have hτ : ∀ a b, form c (transpCol a) (transpCol b) = c ![a, b] := fun a b => by
    have h := hβ su3Transp (unitVec a) (unitVec b)
    rwa [rowAct_su3Transp_unitVec, rowAct_su3Transp_unitVec, form_unitVec] at h
  have hπ : ∀ a b, form c (permCol a) (permCol b) = c ![a, b] := fun a b => by
    have h := hβ su3Perm (unitVec a) (unitVec b)
    rwa [rowAct_su3Perm_unitVec, rowAct_su3Perm_unitVec, form_unitVec] at h
  -- the remaining off-diagonal entries: within a root pair or within the Cartan plane
  have h01 : c ![0, 1] = 0 := by
    have h := hτ 0 1
    simp only [transpCol, form_neg_right, form_unitVec] at h
    linear_combination (-1 / 2 : ℂ) * h
  have h10 : c ![1, 0] = 0 := by
    have h := hτ 1 0
    simp only [transpCol, form_neg_left, form_unitVec] at h
    linear_combination (-1 / 2 : ℂ) * h
  have h27 : c ![2, 7] = 0 := by
    have h := hτ 2 7
    simp only [transpCol, form_neg_left, form_unitVec] at h
    linear_combination (-1 / 2 : ℂ) * h
  have h72 : c ![7, 2] = 0 := by
    have h := hτ 7 2
    simp only [transpCol, form_neg_right, form_unitVec] at h
    linear_combination (-1 / 2 : ℂ) * h
  have h34 : c ![3, 4] = 0 := by
    have h := hπ 3 4
    simp only [permCol, form_neg_right, form_unitVec] at h
    rw [← h, h01, neg_zero]
  have h43 : c ![4, 3] = 0 := by
    have h := hπ 4 3
    simp only [permCol, form_neg_left, form_unitVec] at h
    rw [← h, h10, neg_zero]
  have h56 : c ![5, 6] = 0 := by
    have h := hπ 5 6
    simp only [permCol, form_neg_right, form_unitVec] at h
    rw [← h, h34, neg_zero]
  have h65 : c ![6, 5] = 0 := by
    have h := hπ 6 5
    simp only [permCol, form_neg_left, form_unitVec] at h
    rw [← h, h43, neg_zero]
  have hoff : ∀ a b : Fin 8, a ≠ b → c ![a, b] = 0 := by
    intro a b hab
    have key : (∃ k, paritySign k a ≠ paritySign k b)
        ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 7) ∨ (a = 7 ∧ b = 2)
        ∨ (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) ∨ (a = 5 ∧ b = 6)
        ∨ (a = 6 ∧ b = 5) := by
      revert a b
      decide
    rcases key with ⟨k, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hpar k a b hk
    all_goals assumption
  -- the diagonal entries along the root directions, moved around by the cyclic rotation
  have h55 : c ![5, 5] = c ![0, 0] := by
    simpa only [permCol, form_unitVec] using hπ 0 0
  have h66 : c ![6, 6] = c ![1, 1] := by
    simpa only [permCol, form_unitVec] using hπ 1 1
  have h33 : c ![3, 3] = c ![5, 5] := by
    simpa only [permCol, form_unitVec] using hπ 5 5
  have h44 : c ![4, 4] = c ![6, 6] := by
    simpa only [permCol, form_neg_left, form_neg_right, neg_neg, form_unitVec] using hπ 6 6
  -- the two turns tie the Cartan entry `c ![2, 2]` to `c ![0, 0]` and `c ![1, 1]`
  have hQ : c ![0, 0] = c ![2, 2] := by
    have h := hβ su3TurnFst (unitVec 2) (unitVec 2)
    rwa [rowAct_su3TurnFst_unitVec_two, form_neg_left, form_neg_right, neg_neg, form_unitVec,
      form_unitVec] at h
  have hQ' : c ![1, 1] = c ![2, 2] := by
    have h := hβ su3TurnSnd (unitVec 2) (unitVec 2)
    rwa [rowAct_su3TurnSnd_unitVec_two, form_unitVec, form_unitVec] at h
  -- the Cartan plane: the eigenvectors of the cyclic rotation are isotropic
  have hω : ∀ a : Fin 2, form c (cartanVec a) (cartanVec a) = 0 := by
    intro a
    have h := hβ su3Perm (cartanVec a) (cartanVec a)
    rw [rowAct_su3Perm_cartanVec, form_smul_left, form_smul_right, ← mul_assoc,
      ← su3PermSign_add] at h
    have hs : su3PermSign (cartanGrade a + cartanGrade a) ≠ 1 := by
      fin_cases a
      · exact su3Omega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by decide) (by decide)
      · exact su3Omega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by decide) (by decide)
    exact (mul_left_eq_self₀.1 h).resolve_left hs
  have h77 : c ![7, 7] = c ![2, 2] := by
    rw [← form_unitVec c 7 7, ← form_unitVec c 2 2, unitVec_two_eq_cartanVec_add,
      unitVec_seven_eq_cartanVec_sub]
    simp only [form_smul_left, form_smul_right, form_add_left, form_add_right, form_sub_left,
      form_sub_right, hω]
    linear_combination
      (-(form c (cartanVec 0) (cartanVec 1) + form c (cartanVec 1) (cartanVec 0)) / 4)
        * Complex.I_sq
  have hdiag : ∀ a : Fin 8, c ![a, a] = c ![2, 2] := by
    intro a
    have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by
      revert a
      decide
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hQ
    · exact hQ'
    · rfl
    · rw [h33, h55, hQ]
    · rw [h44, h66, hQ']
    · rw [h55, hQ]
    · rw [h66, hQ']
    · exact h77
  refine ⟨c ![2, 2], funext fun l => ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = ![a, b] := ⟨l 0, l 1, by ext i; fin_cases i <;> rfl⟩
  by_cases h : a = b
  · subst h
    simp [traceCoeff, hdiag]
  · simp [traceCoeff, h, hoff a b h]

/-!

## F. The colour invariants of the span

The action on coefficients is unitary, by `sum_act_mul` and `act_star`, so
`Family.exists_invariant_coeff` writes a colour invariant of the span as the contraction of
an invariant coefficient, and section E makes that coefficient a multiple of the delta. The
statement is made for any family of linear maps `φ U` obeying the law, not only for the
colour rotations `repGauge (U, 1, 1)`, so that section G can apply it in a quotient.

-/

/-- Every invariant in the span of a family obeying the law for a family of linear maps
  `φ U` is a multiple of the trace: the one singlet of `8 ⊗ 8`. -/
theorem exists_smul_sum_diag_of_invariant {φ : specialUnitaryGroup (Fin 3) ℂ → B →ₗ[ℂ] B}
    (hT : ∀ U, IsSU3BiAdjointMat U (φ U) T) {x : B} (hx : x ∈ ⨆ d, ℂ ∙ T d)
    (hinv : ∀ U, φ U x = x) :
    ∃ z : ℂ, x = z • ∑ a : Fin 8, T ![a, a] := by
  obtain ⟨c, rfl, hc⟩ := Family.exists_invariant_coeff T φ act
    (fun U c => map_sum_smul (hT U) c)
    (Family.sum_star_mul_of_transpose act sum_act_mul act_star) hx hinv
  obtain ⟨z, hz⟩ := exists_smul_traceCoeff_of_act_eq hc
  refine ⟨z, ?_⟩
  rw [hz, ← sum_traceCoeff_smul, Finset.smul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- Every colour invariant in the span of the components is a multiple of the trace
  contraction. -/
theorem exists_smul_traceContraction_of_su3_invariant (hT : IsSU3BiAdjoint B repGauge T)
    {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    ∃ z : ℂ, x = z • hT.traceContraction :=
  exists_smul_sum_diag_of_invariant hT.repGauge_T hx hinv

/-!

## G. The invariants modulo a stable submodule

The Standard Model files handle many families at once and peel them off one at a time, so
the classification is wanted modulo a submodule `S` in which the other families are parked.
The law descends to the quotient by a colour-stable `S`, so section F applies there, and
`Family.exists_smul_add_of_mem_sup` lifts the result back.

-/

/-- The law descends to the quotient by a submodule stable under the map. -/
lemma isSU3BiAdjointMat_mapQ {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU3BiAdjointMat U f T) (S : Submodule ℂ B) (hS : ∀ y ∈ S, f y ∈ S) :
    IsSU3BiAdjointMat U (S.mapQ S f hS) fun l => S.mkQ (T l) := by
  intro l
  dsimp only
  rw [← LinearMap.comp_apply, Submodule.mapQ_mkQ, LinearMap.comp_apply, hf l, map_sum]
  exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- A colour invariant of the span of the components joined with a colour-stable submodule
  `S` is a multiple of the trace contraction up to a colour-invariant remainder in `S`. -/
theorem mem_span_sup_su3_invariant_iff (hT : IsSU3BiAdjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 3) ℂ, ∀ y ∈ S, repGauge (U, 1, 1) y ∈ S)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • hT.traceContraction + y
      ∧ ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) y = y := by
  refine Family.exists_smul_add_of_mem_sup T (fun U => repGauge (U, 1, 1)) S hS
    hT.traceContraction hT.repGauge_traceContraction (fun x hx hinv => ?_) hx hinv
  obtain ⟨z, hz⟩ := exists_smul_sum_diag_of_invariant
    (fun U => isSU3BiAdjointMat_mapQ (hT.repGauge_T U) S (hS U)) hx hinv
  exact ⟨z, by rw [hz, traceContraction, map_sum]⟩

/-!

## Aside: what other files import from here

Nothing from here on is used by the theorem above. Each item exists because another file
imports it under this name, and each says which.

## Aside: the weight basis of the adjoint, for `MassDimEight` and `IsSU3Adjoint`

The Gell-Mann directions carry no definite colour charge; the eigenvectors of the colour
torus do. They are, for each of the three root directions, the two complex combinations
`x₁ ± i x₂` of the paired Gell-Mann coordinates, and the two Cartan directions as they
stand: eight coordinate vectors `wtCoeff`, indexed by `WeightIdx`. `MassDimEight` matches
the gluon field strengths with the components of a bi-adjoint family through this basis,
using that its root pairs and Cartan indices are those of the whole gauge algebra,
`rootIdx_castSucc` and `cartanIdx_castSucc`, and that the sixty four contractions `biVec`
of `T` against two weight vectors span the components, `span_eq_wtSpan`. `IsSU3Adjoint`
reads the two Cartan directions in the eigenbasis `cartanVec`, `wtCoeff_cartan_zero` and
`wtCoeff_cartan_one`.

-/

/-- The index type of the adjoint weight basis: three positive roots, three negative roots
  and two Cartan directions. -/
abbrev WeightIdx : Type := Fin 3 ⊕ Fin 3 ⊕ Fin 2

/-- The pairs of Gell-Mann indices making up the three root directions. -/
def rootPair : Fin 3 → Fin 8 × Fin 8
  | 0 => (0, 1)
  | 1 => (3, 4)
  | 2 => (5, 6)

/-- The root pairs are the `su(3)` root pairs of the whole gauge algebra. -/
lemma rootIdx_castSucc (r : Fin 3) :
    GaugeAlgebra.rootIdx r.castSucc
      = (Sum.inl (rootPair r).1, Sum.inl (rootPair r).2) := by
  fin_cases r <;> rfl

/-- The Cartan indices are the `su(3)` Cartan indices of the whole gauge algebra. -/
lemma cartanIdx_castSucc (c : Fin 2) :
    GaugeAlgebra.cartanIdx c.castSucc.castSucc = Sum.inl (GaugeAlgebra.su3CartanId c) := by
  fin_cases c <;> rfl

/-- Every Gell-Mann index is a member of a root pair or a Cartan index. -/
lemma exists_rootPair_or_cartanId (a : Fin 8) :
    (∃ r : Fin 3, a = (rootPair r).1) ∨ (∃ r : Fin 3, a = (rootPair r).2)
      ∨ ∃ c : Fin 2, a = GaugeAlgebra.su3CartanId c := by
  revert a
  decide

/-- The weight basis of the adjoint in Gell-Mann coordinates: `x₁ ± i x₂` on each root
  pair, and the Cartan directions themselves. -/
noncomputable def wtCoeff : WeightIdx → Fin 8 → ℂ
  | Sum.inl r, a => (if a = (rootPair r).1 then 1 else 0)
      + Complex.I * (if a = (rootPair r).2 then 1 else 0)
  | Sum.inr (Sum.inl r), a => (if a = (rootPair r).1 then 1 else 0)
      - Complex.I * (if a = (rootPair r).2 then 1 else 0)
  | Sum.inr (Sum.inr c), a => if a = GaugeAlgebra.su3CartanId c then 1 else 0

/-- The first member of a root pair, in the weight basis. -/
lemma unitVec_rootPair_fst (r : Fin 3) :
    unitVec (rootPair r).1
      = (2 : ℂ)⁻¹ • (wtCoeff (Sum.inl r) + wtCoeff (Sum.inr (Sum.inl r))) := by
  funext x
  simp only [unitVec, wtCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The second member of a root pair, in the weight basis. -/
lemma unitVec_rootPair_snd (r : Fin 3) :
    unitVec (rootPair r).2
      = (-(Complex.I / 2)) • (wtCoeff (Sum.inl r) - wtCoeff (Sum.inr (Sum.inl r))) := by
  funext x
  simp only [unitVec, wtCoeff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A Cartan direction is already a weight vector. -/
lemma unitVec_cartanId (c : Fin 2) :
    unitVec (GaugeAlgebra.su3CartanId c) = wtCoeff (Sum.inr (Sum.inr c)) := rfl

/-- The first Cartan direction in the eigenbasis of the cyclic colour rotation. -/
lemma wtCoeff_cartan_zero :
    wtCoeff (Sum.inr (Sum.inr 0)) = (2 : ℂ)⁻¹ • (cartanVec 0 + cartanVec 1) :=
  unitVec_two_eq_cartanVec_add

/-- The second Cartan direction in the eigenbasis of the cyclic colour rotation. -/
lemma wtCoeff_cartan_one :
    wtCoeff (Sum.inr (Sum.inr 1)) = (Complex.I / 2) • (cartanVec 0 - cartanVec 1) :=
  unitVec_seven_eq_cartanVec_sub

/-- The contraction of the two indices of `T` against a pair of coordinate vectors. -/
@[nolint unusedArguments]
noncomputable def biVec (hT : IsSU3BiAdjoint B repGauge T) (c₀ c₁ : Fin 8 → ℂ) : B :=
  ∑ d : Fin 2 → Fin 8, (c₀ (d 0) * c₁ (d 1)) • T d

variable (hT : IsSU3BiAdjoint B repGauge T)

/-- Scaling the left coordinate vector. -/
lemma biVec_smul_left (z : ℂ) (c₀ c₁ : Fin 8 → ℂ) :
    hT.biVec (z • c₀) c₁ = z • hT.biVec c₀ c₁ := by
  simp only [biVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul, mul_assoc]

/-- Scaling the right coordinate vector. -/
lemma biVec_smul_right (z : ℂ) (c₀ c₁ : Fin 8 → ℂ) :
    hT.biVec c₀ (z • c₁) = z • hT.biVec c₀ c₁ := by
  simp only [biVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul]
  exact Finset.sum_congr rfl fun d _ => by ring_nf

/-- Adding on the left. -/
lemma biVec_add_left (c₀ c₀' c₁ : Fin 8 → ℂ) :
    hT.biVec (c₀ + c₀') c₁ = hT.biVec c₀ c₁ + hT.biVec c₀' c₁ := by
  simp only [biVec, Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

/-- Subtracting on the left. -/
lemma biVec_sub_left (c₀ c₀' c₁ : Fin 8 → ℂ) :
    hT.biVec (c₀ - c₀') c₁ = hT.biVec c₀ c₁ - hT.biVec c₀' c₁ := by
  simp only [biVec, Pi.sub_apply, sub_mul, sub_smul, Finset.sum_sub_distrib]

/-- Adding on the right. -/
lemma biVec_add_right (c₀ c₁ c₁' : Fin 8 → ℂ) :
    hT.biVec c₀ (c₁ + c₁') = hT.biVec c₀ c₁ + hT.biVec c₀ c₁' := by
  simp only [biVec, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]

/-- Subtracting on the right. -/
lemma biVec_sub_right (c₀ c₁ c₁' : Fin 8 → ℂ) :
    hT.biVec c₀ (c₁ - c₁') = hT.biVec c₀ c₁ - hT.biVec c₀ c₁' := by
  simp only [biVec, Pi.sub_apply, mul_sub, sub_smul, Finset.sum_sub_distrib]

/-- Contracting against two Gell-Mann directions returns a component. -/
lemma biVec_unitVec (a b : Fin 8) : hT.biVec (unitVec a) (unitVec b) = T ![a, b] := by
  rw [biVec, sum_pi_two]
  simp [unitVec, ite_smul]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a) fun x _ hx => by simp [hx]]
  simp

/-- The join of the lines through the bi-adjoint weight vectors. -/
noncomputable def wtSpan (hT : IsSU3BiAdjoint B repGauge T) : Submodule ℂ B :=
  ⨆ k : WeightIdx × WeightIdx, ℂ ∙ hT.biVec (wtCoeff k.1) (wtCoeff k.2)

/-- A weight vector contracted against a Gell-Mann direction lies in `wtSpan`. -/
lemma biVec_wtCoeff_unitVec_mem (k : WeightIdx) (b : Fin 8) :
    hT.biVec (wtCoeff k) (unitVec b) ∈ hT.wtSpan := by
  have hgen : ∀ k' : WeightIdx, hT.biVec (wtCoeff k) (wtCoeff k') ∈ hT.wtSpan :=
    fun k' => Submodule.mem_iSup_of_mem (k, k') (Submodule.mem_span_singleton_self _)
  rcases exists_rootPair_or_cartanId b with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨c, rfl⟩
  · rw [unitVec_rootPair_fst, hT.biVec_smul_right, hT.biVec_add_right]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hgen _) (hgen _))
  · rw [unitVec_rootPair_snd, hT.biVec_smul_right, hT.biVec_sub_right]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hgen _) (hgen _))
  · rw [unitVec_cartanId]
    exact hgen _

/-- Every component lies in `wtSpan`. -/
lemma biVec_unitVec_mem (a b : Fin 8) :
    hT.biVec (unitVec a) (unitVec b) ∈ hT.wtSpan := by
  rcases exists_rootPair_or_cartanId a with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨c, rfl⟩
  · rw [unitVec_rootPair_fst, hT.biVec_smul_left, hT.biVec_add_left]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (hT.biVec_wtCoeff_unitVec_mem _ _) (hT.biVec_wtCoeff_unitVec_mem _ _))
  · rw [unitVec_rootPair_snd, hT.biVec_smul_left, hT.biVec_sub_left]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (hT.biVec_wtCoeff_unitVec_mem _ _) (hT.biVec_wtCoeff_unitVec_mem _ _))
  · rw [unitVec_cartanId]
    exact hT.biVec_wtCoeff_unitVec_mem _ _

/-- The bi-adjoint weight vectors span the components: the change of basis from the
  Gell-Mann basis to the weight basis is invertible. -/
lemma span_eq_wtSpan : hT.span = hT.wtSpan := by
  refine le_antisymm (iSup_le fun d => (Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    (iSup_le fun k => (Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
  · have hd : T d = T ![d 0, d 1] := by
      congr 1
      funext j
      fin_cases j <;> simp
    rw [hd, ← hT.biVec_unitVec]
    exact hT.biVec_unitVec_mem _ _
  · rw [span, biVec]
    exact sum_mem fun d _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-!

## Aside: the quotient representation, for `MassDimEight`

A submodule stable under a representation of the whole gauge group carries the induced
representation on the quotient. The theorem above needs only the induced maps
`Submodule.mapQ`; `MassDimEight` uses the representation.

-/

/-- The representation induced on the quotient by a stable submodule. -/
noncomputable def quotRep (ρ : Representation ℂ GaugeGroupI B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, ρ g y ∈ S) :
    Representation ℂ GaugeGroupI (B ⧸ S) where
  toFun g := S.mapQ S (ρ g) fun y hy => hS g y hy
  map_one' := by
    ext y
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, map_one, Module.End.one_apply]
  map_mul' g₁ g₂ := by
    ext y
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, map_mul, Module.End.mul_apply]

/-- The quotient representation on a class is the class of the representation. -/
lemma quotRep_mkQ {ρ : Representation ℂ GaugeGroupI B} (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, ρ g y ∈ S) (g : GaugeGroupI) (y : B) :
    quotRep ρ S hS g (S.mkQ y) = S.mkQ (ρ g y) := rfl

/-!

## Aside: the trivial square-zero extension, for `MassDimEight`

`MassDimEight` needs a transport in the opposite direction to `quotRep`, from a module to an
algebra: the trivial square-zero extension `TrivSqZeroExt ℂ M` is a commutative algebra on
which any representation of `M` acts multiplicatively, `sqZeroRep`. It belongs with
`GaugeWeightDecomposition`.

-/

section SquareZero

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The opposite scalar action on a complex vector space, which the square-zero extension
  needs to be a ring. Since `ℂ` is commutative it is the given action read through `unop`,
  and it is given a low priority so that the action of `ℂ` on itself is unaffected. -/
noncomputable local instance (priority := 100) opModule : Module ℂᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id ℂ).fromOpposite fun x y => mul_comm x y)

/-- The two scalar actions of `ℂ` on a complex vector space commute. -/
local instance (priority := 100) smulCommClassOpModule : SMulCommClass ℂ ℂᵐᵒᵖ M :=
  ⟨fun a b m => smul_comm a b.unop m⟩

/-- The opposite scalar action agrees with the given one, `ℂ` being commutative. -/
local instance (priority := 100) isCentralScalarOpModule : IsCentralScalar ℂ M :=
  ⟨fun _ _ => rfl⟩

/-- The linear map of the square-zero extension induced by a linear map of the module: the
  identity on the scalar part and the given map on the module part. -/
def sqZeroMap (f : M →ₗ[ℂ] M) : TrivSqZeroExt ℂ M →ₗ[ℂ] TrivSqZeroExt ℂ M where
  toFun u := TrivSqZeroExt.inl u.fst + TrivSqZeroExt.inr (f u.snd)
  map_add' u v := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_smul' c u := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

/-- The induced map leaves the scalar part alone. -/
@[simp]
lemma fst_sqZeroMap (f : M →ₗ[ℂ] M) (u : TrivSqZeroExt ℂ M) :
    (sqZeroMap f u).fst = u.fst := by
  simp [sqZeroMap]

/-- The induced map acts by the given map on the module part. -/
@[simp]
lemma snd_sqZeroMap (f : M →ₗ[ℂ] M) (u : TrivSqZeroExt ℂ M) :
    (sqZeroMap f u).snd = f u.snd := by
  simp [sqZeroMap]

/-- The representation carried by the square-zero extension: trivial on the scalar part
  and the given representation on the module part. -/
def sqZeroRep (ρ : Representation ℂ GaugeGroupI M) :
    Representation ℂ GaugeGroupI (TrivSqZeroExt ℂ M) where
  toFun g := sqZeroMap (ρ g)
  map_one' := by
    refine LinearMap.ext fun u => TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun u => TrivSqZeroExt.ext ?_ ?_ <;> simp [Module.End.mul_apply]

/-- The extended representation on the image of the module is the given one. -/
@[simp]
lemma sqZeroRep_inr (ρ : Representation ℂ GaugeGroupI M) (g : GaugeGroupI) (m : M) :
    sqZeroRep ρ g (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (ρ g m) := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [sqZeroRep]

/-- The extended representation acts by algebra maps, whatever the representation it
  extends. -/
lemma isMulRep_sqZeroRep (ρ : Representation ℂ GaugeGroupI M) : IsMulRep (sqZeroRep ρ) := by
  intro g u v
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [sqZeroRep]
  · simp [sqZeroRep, TrivSqZeroExt.snd_mul, op_smul_eq_smul]

end SquareZero

/-!

## Aside: the gauge form of the theorem, for `MassDimEight`

-/

/-- The gauge form on an algebra: a gauge invariant of the span joined with a gauge-stable
  submodule is a multiple of the trace contraction up to a gauge-invariant remainder, once
  the trace contraction is known to be gauge invariant. The multiplicativity hypothesis
  `hmul` is not used; `MassDimEight` passes it. -/
@[nolint unusedArguments]
theorem mem_span_sup_invariant_iff {B : Type*} [Ring B] [Algebra ℂ B]
    {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 8) → B}
    (hT : IsSU3BiAdjoint B repGauge T) (hmul : IsMulRep repGauge)
    (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (htc : ∀ g : GaugeGroupI, repGauge g hT.traceContraction = hT.traceContraction)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • hT.traceContraction + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  obtain ⟨c, y, hyS, hxy, -⟩ :=
    hT.mem_span_sup_su3_invariant_iff x S (fun U => hS (U, 1, 1)) hx fun U => hinv (U, 1, 1)
  refine ⟨c, y, hyS, hxy, fun g => ?_⟩
  rw [show y = x - c • hT.traceContraction from by rw [hxy]; abel, map_sub, map_smul,
    hinv g, htc g]

end IsSU3BiAdjoint

end StandardModel
