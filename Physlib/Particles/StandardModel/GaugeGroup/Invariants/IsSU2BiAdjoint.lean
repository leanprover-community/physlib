/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.RootDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
/-!
# Gauge tensors carrying two `su(2)` adjoint indices

A `W`-boson field strength `W^a` carries one isospin index `a`, running over the three Pauli
directions of `su(2)`. A product of two field strengths carries two, and the combination that
enters the Yang–Mills Lagrangian is the isospin trace `∑ a, W^a W^a`. This file proves the
group theory behind that choice, in the form the Standard Model files consume: among all
combinations of the components of such a product, the multiples of the trace are the only
ones every isospin rotation leaves alone. In the language of representation theory, the
adjoint of `SU(2)` is the vector representation of the rotation group,
`3 ⊗ 3 = 1 ⊕ 3 ⊕ 5` contains exactly one singlet, and that singlet is the dot product.

`IsSU2BiAdjoint B repGauge T` records the hypothesis. `T` is a family indexed by two isospin
indices and valued in a module `B` carrying a representation `repGauge` of the gauge group,
and an isospin rotation `U ∈ SU(2)` moves its components by two copies of the adjoint matrix
of `U`, as a rank two tensor `T^{a b}` should. Nothing is asked of the colour and hypercharge
factors, and the conclusions are accordingly about invariance under isospin.

The theorem, `mem_span_sup_su2_invariant_iff`, is stated modulo an isospin-stable submodule
`S`, because the Standard Model files handle many families at once and peel them off one at
a time: an isospin invariant in the span of the components joined with `S` is a multiple of
the trace contraction up to an isospin-invariant error in `S`.

The proof has two halves, and neither needs more than the module structure of `B`.

The first half is the linear algebra of `Invariants.Basic`. A vector of the span is
`∑ l, c l • T l` for a coefficient function `c` on pairs of isospin indices, and an isospin
rotation acts on `c` by the Kronecker square of its adjoint matrix, a unitary action. So an
invariant vector of the span is the contraction of an invariant coefficient
(`Family.exists_invariant_coeff`), and the question becomes a finite one.

The second half is a finite computation with four rotations. An invariant coefficient is a
`3 × 3` matrix fixed by every rotation. The three half turns about the isospin axes, the
elements `i σ₁`, `i σ₂`, `i σ₃` of `SU(2)`, each fix one Pauli direction and reverse the
other two, so they change the sign of every entry `c ![a, b]` with `a ≠ b`: the matrix is
diagonal. A third of a turn about the diagonal axis cycles the three Pauli directions, so the
diagonal entries agree. The matrix is a multiple of the identity and the vector a multiple
of the trace.

Section A sets up the adjoint matrix and the transformation law. Section B has the span, the
action on coefficients and the trace contraction. Section C computes the four rotations on
coefficients, section D is the finite computation, section E classifies the invariants of
the span, and section F divides out a stable submodule and proves the theorem. An aside at
the end holds what `MassDimEight` imports from here and the theorem does not use: the weight
basis of the adjoint and the gauge form of the theorem.
-/

@[expose] public section

namespace StandardModel

open Matrix PauliMatrix

/-!

## A. The adjoint action of `SU(2)` on an isospin index

## A.1. The adjoint matrix

An isospin rotation `U` acts on the Lie algebra `su(2)` by conjugation, `X ↦ U X U⁻¹`, and
its adjoint matrix is the matrix of that action in the Pauli basis, read off with the trace
pairing `(X, Y) ↦ ½ tr (X Y)`. The matrix is real, and orthogonal because conjugation
preserves the trace pairing; it is the `su(2)` block of `GaugeAlgebra.adjointMatrix` at the
gauge element `(1, U, 1)`, which is where those two facts are proved.

-/

/-- The adjoint matrix of an element of `SU(2)`: the trace pairing of the Pauli basis of
  `su(2)` with the Pauli basis conjugated by that element. -/
noncomputable def su2AdjointMatrix (U : specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    2⁻¹ * (Matrix.trace (pauliMatrix (Sum.inr i) *
      (U.1 * pauliMatrix (Sum.inr j) * star U.1))).re

/-- The entries of the adjoint matrix. -/
@[simp]
lemma su2AdjointMatrix_apply (U : specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 3) :
    su2AdjointMatrix U i j
      = 2⁻¹ * (Matrix.trace (pauliMatrix (Sum.inr i) *
          (U.1 * pauliMatrix (Sum.inr j) * star U.1))).re := rfl

/-- The rows of the adjoint matrix are orthonormal. -/
lemma sum_su2AdjointMatrix_row_mul (U : specialUnitaryGroup (Fin 2) ℂ) (c d : Fin 3) :
    ∑ a : Fin 3, su2AdjointMatrix U c a * su2AdjointMatrix U d a
      = if c = d then 1 else 0 :=
  GaugeAlgebra.sum_adjointMatrix_inr_inl_row_mul (1, U, 1) c d

/-- The adjoint matrix of the inverse is the transpose. -/
lemma su2AdjointMatrix_inv (U : specialUnitaryGroup (Fin 2) ℂ) (a b : Fin 3) :
    su2AdjointMatrix U⁻¹ a b = su2AdjointMatrix U b a := by
  have h := GaugeAlgebra.adjointMatrix_inv_apply (1, U, 1) (Sum.inr (Sum.inl a))
    (Sum.inr (Sum.inl b))
  rwa [show ((1, U, 1) : GaugeGroupI)⁻¹ = (1, U⁻¹, 1) from by simp] at h

/-!

## A.2. Bi-adjoint families

The transformation law carries one factor of the adjoint matrix per index, with the summed
index in the row slot. It is recorded as `IsSU2BiAdjointMat`, a relation between one element
of `SU(2)` and one linear map on `B` in which no other factor of the gauge group appears, so
that it can be applied to the maps a representation induces on a quotient. `IsSU2BiAdjoint`
asks it of the isospin rotations `repGauge (1, U, 1)` alone.

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with two
  adjoint indices: one factor of `su2AdjointMatrix U` per index, with the summed index in
  the row slot. -/
def IsSU2BiAdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 3) → B) : Prop :=
  ∀ l : Fin 2 → Fin 3,
    f (T l) = ∑ a : Fin 2 → Fin 3,
      (∏ i : Fin 2, ((su2AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a

/-- A family `T` of elements of `B`, indexed by two `su(2)` adjoint indices, transforms as a
  tensor `T^{a b}` under the isospin factor of the gauge group. Nothing is asked of the
  colour and hypercharge factors. -/
structure IsSU2BiAdjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2BiAdjointMat g (repGauge (1, g, 1)) T

namespace IsSU2BiAdjoint

/- `span`, `traceContraction` and `biVec` take the hypothesis `hT` only to hang off it by
dot notation, and `mem_span_sup_invariant_iff` keeps a hypothesis for its caller; each is
marked `nolint unusedArguments` where it is declared. -/
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 3) → B}

/-!

## B. Coefficients, their action and the trace

A vector of the span of the components is a contraction `∑ l, c l • T l` against a
coefficient function `c` on pairs of isospin indices, and the transformation law says exactly
that an isospin rotation moves such a contraction by moving `c` with the Kronecker square of
its adjoint matrix, `act U`. Orthogonality of the adjoint matrix makes `act U⁻¹` the
transpose of `act U`, and the matrix being real, `act U` commutes with conjugation: these are
the two hypotheses of `Family.exists_invariant_coeff`. The trace contraction
`∑ a, T ![a, a]` is the contraction against the Kronecker delta `traceCoeff`, and it is
isospin invariant because the delta is an invariant coefficient.

-/

/-- The span of the components. -/
@[nolint unusedArguments]
def span (hT : IsSU2BiAdjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span precisely when it is a linear combination of the
  components. -/
lemma mem_span_iff (hT : IsSU2BiAdjoint B repGauge T) (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 2 → Fin 3) → ℂ), x = ∑ d, c d • T d :=
  Family.mem_iSup_span_singleton_iff T x

/-- A sum over pairs of isospin indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 3) → M) :
    ∑ d : Fin 2 → Fin 3, F d = ∑ x : Fin 3, ∑ y : Fin 3, F ![x, y] :=
  Family.sum_pi_two F

/-- The action of `U ∈ SU(2)` on coefficient functions: the Kronecker square of its
  adjoint matrix. -/
noncomputable def act (U : specialUnitaryGroup (Fin 2) ℂ) :
    ((Fin 2 → Fin 3) → ℂ) →ₗ[ℂ] (Fin 2 → Fin 3) → ℂ :=
  Matrix.toLin' (Matrix.of fun a l =>
    ∏ i : Fin 2, ((su2AdjointMatrix U (a i) (l i) : ℝ) : ℂ))

/-- The action on coefficients, written out. -/
lemma act_apply (U : specialUnitaryGroup (Fin 2) ℂ) (c : (Fin 2 → Fin 3) → ℂ)
    (a : Fin 2 → Fin 3) :
    act U c a = ∑ l, (∏ i : Fin 2, ((su2AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) * c l := by
  simp [act, Matrix.mulVec, dotProduct]

/-- The transformation law in coefficient form: a map moving the components by `U` moves a
  contraction by `act U` on its coefficients. -/
lemma map_sum_smul {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU2BiAdjointMat U f T) (c : (Fin 2 → Fin 3) → ℂ) :
    f (∑ l, c l • T l) = ∑ a, act U c a • T a := by
  simp only [map_sum, map_smul, act_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hf l, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [smul_smul, mul_comm]

/-- The action of `U⁻¹` is the transpose of the action of `U`, the adjoint matrix being
  orthogonal. -/
lemma sum_act_mul (U : specialUnitaryGroup (Fin 2) ℂ) (c d : (Fin 2 → Fin 3) → ℂ) :
    ∑ a, act U c a * d a = ∑ l, c l * act U⁻¹ d l := by
  simp only [act_apply, su2AdjointMatrix_inv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring

/-- The action on coefficients commutes with complex conjugation, the adjoint matrix being
  real. -/
lemma act_star (U : specialUnitaryGroup (Fin 2) ℂ) (c : (Fin 2 → Fin 3) → ℂ) :
    act U (star c) = star (act U c) := by
  funext a
  simp [act_apply, star_sum, star_mul', Complex.conj_ofReal]

/-- The Kronecker delta on pairs of isospin indices: the coefficients of the trace. -/
def traceCoeff : (Fin 2 → Fin 3) → ℂ := fun l => if l 0 = l 1 then 1 else 0

/-- The Kronecker delta is an invariant coefficient: the rows of the adjoint matrix are
  orthonormal. -/
lemma act_traceCoeff (U : specialUnitaryGroup (Fin 2) ℂ) : act U traceCoeff = traceCoeff := by
  funext a
  rw [act_apply, sum_pi_two]
  have key : ∀ x y : Fin 3,
      (∏ i : Fin 2, ((su2AdjointMatrix U (a i) (![x, y] i) : ℝ) : ℂ)) * traceCoeff ![x, y]
        = if y = x then
            ((su2AdjointMatrix U (a 0) x * su2AdjointMatrix U (a 1) x : ℝ) : ℂ) else 0 := by
    intro x y
    by_cases h : y = x
    · subst h
      simp [traceCoeff, Fin.prod_univ_two]
    · simp [traceCoeff, Fin.prod_univ_two, h, Ne.symm h]
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Complex.ofReal_sum,
    sum_su2AdjointMatrix_row_mul]
  by_cases h : a 0 = a 1 <;> simp [traceCoeff, h]

/-- The trace contraction: the Kronecker contraction of the two isospin indices. -/
@[nolint unusedArguments]
def traceContraction (hT : IsSU2BiAdjoint B repGauge T) : B := ∑ a : Fin 3, T ![a, a]

/-- The trace is the contraction against the Kronecker delta. -/
lemma sum_traceCoeff_smul (T : (Fin 2 → Fin 3) → B) :
    ∑ l, traceCoeff l • T l = ∑ a : Fin 3, T ![a, a] := by
  rw [sum_pi_two]
  simp [traceCoeff, ite_smul]

/-- Any map moving the components by an `SU(2)` matrix fixes the trace contraction. -/
lemma map_traceContraction (hT : IsSU2BiAdjoint B repGauge T)
    {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B} (hf : IsSU2BiAdjointMat U f T) :
    f hT.traceContraction = hT.traceContraction := by
  rw [traceContraction, ← sum_traceCoeff_smul, map_sum_smul hf, act_traceCoeff]

/-- The trace contraction is isospin invariant. Nothing constrains the colour and
  hypercharge factors, which may well move it. -/
lemma repGauge_traceContraction (hT : IsSU2BiAdjoint B repGauge T)
    (U : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, U, 1) hT.traceContraction = hT.traceContraction :=
  hT.map_traceContraction (hT.repGauge_T U)

/-!

## C. Four isospin rotations on coefficients

The adjoint action of `SU(2)` is the rotation group acting on three-dimensional space, and
four rotations suffice for the classification. C.1 has the three half turns about the isospin
axes, and C.2 a third of a turn about the diagonal axis `σ₁ + σ₂ + σ₃`, which cycles the
three Pauli directions.

## C.1. The isospin flips

The element `i σ_k` of `SU(2)` conjugates `σ_k` to itself and the other two Pauli matrices
to their negatives: it is the half turn about the `k`-th isospin axis, its adjoint matrix is
diagonal with entries `±1`, and it multiplies a coefficient `c ![a, b]` by the product of
the signs of `a` and `b`.

-/

/-- The matrix of the `k`-th isospin flip, the half turn `i σ_k` about the `k`-th isospin
  axis. It is unitary, and its determinant is `1` because `i ^ 2` cancels the determinant
  `-1` of a Pauli matrix. -/
noncomputable def su2FlipMatrix : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, Complex.I; Complex.I, 0]
  | 1 => !![0, 1; -1, 0]
  | 2 => !![Complex.I, 0; 0, -Complex.I]

/-- The conjugate transpose of the `k`-th isospin flip, which is its inverse and its
  negative, the Pauli matrices being self-adjoint. -/
noncomputable def su2FlipStarMatrix : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, -Complex.I; -Complex.I, 0]
  | 1 => !![0, -1; 1, 0]
  | 2 => !![-Complex.I, 0; 0, Complex.I]

/-- The `k`-th isospin flip as an element of `SU(2)`. -/
noncomputable def su2Flip (k : Fin 3) : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨su2FlipMatrix k, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      fin_cases k <;> ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [su2FlipMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    · fin_cases k <;> simp [su2FlipMatrix, Matrix.det_fin_two_of]⟩

/-- The underlying matrix of an isospin flip. -/
lemma su2Flip_coe (k : Fin 3) : (su2Flip k).1 = su2FlipMatrix k := rfl

/-- The conjugate transpose of an isospin flip. -/
lemma star_su2FlipMatrix (k : Fin 3) :
    star (su2FlipMatrix k) = su2FlipStarMatrix k := by
  fin_cases k <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [su2FlipMatrix, su2FlipStarMatrix]

/-- The sign by which the `k`-th isospin flip scales each Pauli direction: `1` on its own
  axis and `-1` on the other two. -/
def su2FlipSign : Fin 3 → Fin 3 → ℤ
  | 0 => ![1, -1, -1]
  | 1 => ![-1, 1, -1]
  | 2 => ![-1, -1, 1]

/-- The adjoint matrix of an isospin flip is diagonal, with the sign of each Pauli direction
  on the diagonal. -/
lemma su2AdjointMatrix_su2Flip (k : Fin 3) (a b : Fin 3) :
    su2AdjointMatrix (su2Flip k) a b = if a = b then (su2FlipSign k b : ℝ) else 0 := by
  rw [su2AdjointMatrix_apply, su2Flip_coe, star_su2FlipMatrix]
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp only [su2FlipMatrix, su2FlipStarMatrix, su2FlipSign, pauliMatrix,
      Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply] <;>
    norm_num [Complex.ext_iff]

/-- An isospin flip multiplies a coefficient by the product of the signs of its two
  indices. -/
lemma act_su2Flip (k : Fin 3) (c : (Fin 2 → Fin 3) → ℂ) (a b : Fin 3) :
    act (su2Flip k) c ![a, b]
      = ((su2FlipSign k a : ℤ) : ℂ) * ((su2FlipSign k b : ℤ) : ℂ) * c ![a, b] := by
  rw [act_apply, sum_pi_two, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      su2AdjointMatrix_su2Flip, if_true, Complex.ofReal_intCast]
  · intro y _ hy
    simp [-su2AdjointMatrix_apply, su2AdjointMatrix_su2Flip, Ne.symm hy]
  · simp
  · intro x _ hx
    simp [-su2AdjointMatrix_apply, su2AdjointMatrix_su2Flip, Ne.symm hx]
  · simp

/-!

## C.2. A third of a turn about the diagonal axis

The element `(1 + i(σ₁ + σ₂ + σ₃))/2` of `SU(2)` is a rotation through a third of a turn
about the axis `σ₁ + σ₂ + σ₃`, and its adjoint matrix is the cyclic permutation of the
three Pauli directions. On coefficients it carries each diagonal entry to the next.

-/

/-- The `SU(2)` element `(1 + i(σ₁ + σ₂ + σ₃))/2`, a third of a turn about the diagonal
  axis of the three Pauli directions. -/
noncomputable def su2Cyc : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![(1 + Complex.I) / 2, (1 + Complex.I) / 2;
      (-1 + Complex.I) / 2, (1 - Complex.I) / 2], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose,
          Matrix.conjTranspose_apply, map_div₀, Complex.conj_I, map_ofNat] <;>
        ring_nf <;>
        simp [Complex.I_sq] <;>
        ring
    · simp [Matrix.det_fin_two, Complex.ext_iff]
      norm_num⟩

/-- The underlying matrix of the third of a turn. -/
lemma su2Cyc_coe :
    (su2Cyc : specialUnitaryGroup (Fin 2) ℂ).1
      = !![(1 + Complex.I) / 2, (1 + Complex.I) / 2;
          (-1 + Complex.I) / 2, (1 - Complex.I) / 2] := rfl

/-- The conjugate transpose of the third of a turn. -/
lemma star_su2Cyc_coe :
    star (su2Cyc : specialUnitaryGroup (Fin 2) ℂ).1
      = !![(1 - Complex.I) / 2, (-1 - Complex.I) / 2;
          (1 - Complex.I) / 2, (1 + Complex.I) / 2] := by
  rw [su2Cyc_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> ring

/-- The adjoint matrix of the third of a turn: the cyclic permutation of the three Pauli
  directions. -/
lemma su2AdjointMatrix_su2Cyc :
    su2AdjointMatrix su2Cyc = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext a b
  rw [su2AdjointMatrix_apply, star_su2Cyc_coe, su2Cyc_coe]
  fin_cases a <;> fin_cases b <;>
    simp only [pauliMatrix, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply] <;>
    norm_num [Complex.ext_iff]

/-- The third of a turn carries the second diagonal coefficient to the first. -/
lemma act_su2Cyc_zero_zero (c : (Fin 2 → Fin 3) → ℂ) :
    act su2Cyc c ![0, 0] = c ![1, 1] := by
  rw [act_apply, sum_pi_two, su2AdjointMatrix_su2Cyc]
  simp [Fin.sum_univ_three, Fin.prod_univ_two]

/-- The third of a turn carries the first diagonal coefficient to the third. -/
lemma act_su2Cyc_two_two (c : (Fin 2 → Fin 3) → ℂ) :
    act su2Cyc c ![2, 2] = c ![0, 0] := by
  rw [act_apply, sum_pi_two, su2AdjointMatrix_su2Cyc]
  simp [Fin.sum_univ_three, Fin.prod_univ_two]

/-!

## D. An invariant coefficient is a multiple of the Kronecker delta

The flip about the axis `a` reverses every other direction, so it changes the sign of
`c ![a, b]` for `b ≠ a`: an invariant coefficient is diagonal. The third of a turn cycles the
diagonal entries, so they agree.

-/

/-- An invariant coefficient is a multiple of the Kronecker delta. -/
theorem exists_smul_traceCoeff_of_act_eq {c : (Fin 2 → Fin 3) → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 2) ℂ, act U c = c) :
    ∃ z : ℂ, c = z • traceCoeff := by
  have hoff : ∀ a b : Fin 3, a ≠ b → c ![a, b] = 0 := by
    intro a b hab
    have hs : su2FlipSign a a = 1 ∧ su2FlipSign a b = -1 := by
      revert a b
      decide
    have h := congrFun (hc (su2Flip a)) ![a, b]
    rw [act_su2Flip, hs.1, hs.2] at h
    push_cast at h
    linear_combination (-1 / 2 : ℂ) * h
  have hdiag : ∀ a : Fin 3, c ![a, a] = c ![0, 0] := by
    have h1 := congrFun (hc su2Cyc) ![0, 0]
    have h2 := congrFun (hc su2Cyc) ![2, 2]
    rw [act_su2Cyc_zero_zero] at h1
    rw [act_su2Cyc_two_two] at h2
    intro a
    have ha : a = 0 ∨ a = 1 ∨ a = 2 := by
      revert a
      decide
    rcases ha with rfl | rfl | rfl
    · rfl
    · exact h1
    · exact h2.symm
  refine ⟨c ![0, 0], funext fun l => ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = ![a, b] := ⟨l 0, l 1, by ext i; fin_cases i <;> rfl⟩
  by_cases h : a = b
  · subst h
    simp [traceCoeff, hdiag]
  · simp [traceCoeff, h, hoff a b h]

/-!

## E. The isospin invariants of the span

The action on coefficients is unitary, by `sum_act_mul` and `act_star`, so
`Family.exists_invariant_coeff` writes an isospin invariant of the span as the contraction
of an invariant coefficient, and section D makes that coefficient a multiple of the delta.
The statement is made for any family of linear maps `φ U` obeying the law, not only for the
isospin rotations `repGauge (1, U, 1)`, so that section F can apply it in a quotient.

-/

/-- Every invariant in the span of a family obeying the law for a family of linear maps
  `φ U` is a multiple of the trace: the one singlet of `3 ⊗ 3`. -/
theorem exists_smul_sum_diag_of_invariant {φ : specialUnitaryGroup (Fin 2) ℂ → B →ₗ[ℂ] B}
    (hT : ∀ U, IsSU2BiAdjointMat U (φ U) T) {x : B} (hx : x ∈ ⨆ d, ℂ ∙ T d)
    (hinv : ∀ U, φ U x = x) :
    ∃ z : ℂ, x = z • ∑ a : Fin 3, T ![a, a] := by
  obtain ⟨c, rfl, hc⟩ := Family.exists_invariant_coeff T φ act
    (fun U c => map_sum_smul (hT U) c)
    (Family.sum_star_mul_of_transpose act sum_act_mul act_star) hx hinv
  obtain ⟨z, hz⟩ := exists_smul_traceCoeff_of_act_eq hc
  refine ⟨z, ?_⟩
  rw [hz, ← sum_traceCoeff_smul, Finset.smul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- Every isospin invariant in the span of the components is a multiple of the trace
  contraction. -/
theorem exists_smul_traceContraction_of_su2_invariant (hT : IsSU2BiAdjoint B repGauge T)
    {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) :
    ∃ z : ℂ, x = z • hT.traceContraction :=
  exists_smul_sum_diag_of_invariant hT.repGauge_T hx hinv

/-!

## F. The invariants modulo a stable submodule

The Standard Model files handle many families at once and peel them off one at a time, so
the classification is wanted modulo a submodule `S` in which the other families are parked.
The law descends to the quotient by an isospin-stable `S`, so section E applies there, and
`Family.exists_smul_add_of_mem_sup` lifts the result back.

-/

/-- The law descends to the quotient by a submodule stable under the map. -/
lemma isSU2BiAdjointMat_mapQ {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU2BiAdjointMat U f T) (S : Submodule ℂ B) (hS : ∀ y ∈ S, f y ∈ S) :
    IsSU2BiAdjointMat U (S.mapQ S f hS) fun l => S.mkQ (T l) := by
  intro l
  dsimp only
  rw [← LinearMap.comp_apply, Submodule.mapQ_mkQ, LinearMap.comp_apply, hf l, map_sum]
  exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- An isospin invariant of the span of the components joined with an isospin-stable
  submodule `S` is a multiple of the trace contraction up to an isospin-invariant remainder
  in `S`. -/
theorem mem_span_sup_su2_invariant_iff (hT : IsSU2BiAdjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, U, 1) y ∈ S)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • hT.traceContraction + y
      ∧ ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) y = y := by
  refine Family.exists_smul_add_of_mem_sup T (fun U => repGauge (1, U, 1)) S hS
    hT.traceContraction hT.repGauge_traceContraction (fun x hx hinv => ?_) hx hinv
  obtain ⟨z, hz⟩ := exists_smul_sum_diag_of_invariant
    (fun U => isSU2BiAdjointMat_mapQ (hT.repGauge_T U) S (hS U)) hx hinv
  exact ⟨z, by rw [hz, traceContraction, map_sum]⟩

/-!

## Aside: what `MassDimEight` imports from here

Nothing from here on is used by the theorem above. Each item exists because `MassDimEight`
imports it under this name.

## Aside: the weight basis of the adjoint

The Pauli basis of `su(2)` can be traded for the weight basis: the two root directions
`σ₁ ± i σ₂`, on which the Cartan generator `σ₃` acts by `±2`, and `σ₃` itself. `wtCoeff`
gives the Pauli coordinates of the weight basis, `biVec` contracts a bi-adjoint family
against two coordinate vectors, and `span_eq_wtSpan` says that the contractions against
weight vectors span the same submodule as the components.

-/

/-- The index type of the `su(2)` adjoint weight basis: the positive root, the negative
  root and the Cartan direction. -/
abbrev WeightIdx : Type := Fin 1 ⊕ Fin 1 ⊕ Fin 1

/-- The pair of Pauli indices making up the root direction of `su(2)`. -/
def rootPair : Fin 3 × Fin 3 := (0, 1)

/-- The root direction here is the `su(2)` root direction of the full gauge algebra. -/
lemma rootIdx_three :
    GaugeAlgebra.rootIdx 3
      = (Sum.inr (Sum.inl rootPair.1), Sum.inr (Sum.inl rootPair.2)) := rfl

/-- The Cartan direction here is the `su(2)` Cartan direction of the full gauge
  algebra. -/
lemma cartanIdx_two :
    GaugeAlgebra.cartanIdx 2 = Sum.inr (Sum.inl GaugeAlgebra.su2CartanId) := rfl

/-- Every Pauli index is one of the two members of the root pair or the Cartan index. -/
lemma eq_rootPair_or_cartanId (a : Fin 3) :
    a = rootPair.1 ∨ a = rootPair.2 ∨ a = GaugeAlgebra.su2CartanId := by
  revert a
  decide

/-- The Pauli coordinates of the `su(2)` adjoint weight basis: for the root the two
  combinations `x₁ ± i x₂` of the paired coordinates, and for the Cartan direction the
  coordinate itself. -/
noncomputable def wtCoeff : WeightIdx → Fin 3 → ℂ
  | Sum.inl _, a => (if a = rootPair.1 then 1 else 0)
      + Complex.I * (if a = rootPair.2 then 1 else 0)
  | Sum.inr (Sum.inl _), a => (if a = rootPair.1 then 1 else 0)
      - Complex.I * (if a = rootPair.2 then 1 else 0)
  | Sum.inr (Sum.inr _), a => if a = GaugeAlgebra.su2CartanId then 1 else 0

/-- The coordinate vector of a single Pauli direction. -/
def unitVec (a : Fin 3) : Fin 3 → ℂ := fun x => if x = a then 1 else 0

/-- The coordinate vector of the first member of the root pair, in the weight basis. -/
lemma unitVec_rootPair_fst :
    unitVec rootPair.1
      = (2 : ℂ)⁻¹ • (wtCoeff (Sum.inl 0) + wtCoeff (Sum.inr (Sum.inl 0))) := by
  funext x
  simp only [unitVec, wtCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The coordinate vector of the second member of the root pair, in the weight basis. -/
lemma unitVec_rootPair_snd :
    unitVec rootPair.2
      = (-(Complex.I / 2)) • (wtCoeff (Sum.inl 0) - wtCoeff (Sum.inr (Sum.inl 0))) := by
  funext x
  simp only [unitVec, wtCoeff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The Cartan direction is already a weight vector. -/
lemma unitVec_cartanId :
    unitVec GaugeAlgebra.su2CartanId = wtCoeff (Sum.inr (Sum.inr 0)) := rfl

/-- The contraction of the two isospin indices of `T` against a pair of coordinate
  vectors. -/
@[nolint unusedArguments]
noncomputable def biVec (hT : IsSU2BiAdjoint B repGauge T) (c₀ c₁ : Fin 3 → ℂ) : B :=
  ∑ d : Fin 2 → Fin 3, (c₀ (d 0) * c₁ (d 1)) • T d

variable (hT : IsSU2BiAdjoint B repGauge T)

/-- Contracting against a scaled coordinate vector on the left. -/
lemma biVec_smul_left (z : ℂ) (c₀ c₁ : Fin 3 → ℂ) :
    hT.biVec (z • c₀) c₁ = z • hT.biVec c₀ c₁ := by
  simp only [biVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul, mul_assoc]

/-- Contracting against a scaled coordinate vector on the right. -/
lemma biVec_smul_right (z : ℂ) (c₀ c₁ : Fin 3 → ℂ) :
    hT.biVec c₀ (z • c₁) = z • hT.biVec c₀ c₁ := by
  simp only [biVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul]
  exact Finset.sum_congr rfl fun d _ => by ring_nf

/-- Contracting against a sum of coordinate vectors on the left. -/
lemma biVec_add_left (c₀ c₀' c₁ : Fin 3 → ℂ) :
    hT.biVec (c₀ + c₀') c₁ = hT.biVec c₀ c₁ + hT.biVec c₀' c₁ := by
  simp only [biVec, Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

/-- Contracting against a difference of coordinate vectors on the left. -/
lemma biVec_sub_left (c₀ c₀' c₁ : Fin 3 → ℂ) :
    hT.biVec (c₀ - c₀') c₁ = hT.biVec c₀ c₁ - hT.biVec c₀' c₁ := by
  simp only [biVec, Pi.sub_apply, sub_mul, sub_smul, Finset.sum_sub_distrib]

/-- Contracting against a sum of coordinate vectors on the right. -/
lemma biVec_add_right (c₀ c₁ c₁' : Fin 3 → ℂ) :
    hT.biVec c₀ (c₁ + c₁') = hT.biVec c₀ c₁ + hT.biVec c₀ c₁' := by
  simp only [biVec, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]

/-- Contracting against a difference of coordinate vectors on the right. -/
lemma biVec_sub_right (c₀ c₁ c₁' : Fin 3 → ℂ) :
    hT.biVec c₀ (c₁ - c₁') = hT.biVec c₀ c₁ - hT.biVec c₀ c₁' := by
  simp only [biVec, Pi.sub_apply, mul_sub, sub_smul, Finset.sum_sub_distrib]

/-- Contracting against two single Pauli directions returns a component of `T`. -/
lemma biVec_unitVec (a b : Fin 3) : hT.biVec (unitVec a) (unitVec b) = T ![a, b] := by
  rw [biVec, sum_pi_two]
  simp [unitVec, ite_smul]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a) fun x _ hx => by simp [hx]]
  simp

/-- The join of the lines spanned by the contractions against pairs of weight vectors. -/
noncomputable def wtSpan (hT : IsSU2BiAdjoint B repGauge T) : Submodule ℂ B :=
  ⨆ k : WeightIdx × WeightIdx, ℂ ∙ hT.biVec (wtCoeff k.1) (wtCoeff k.2)

/-- Contracting a weight vector against a single Pauli direction stays in the join of the
  weight lines. -/
lemma biVec_wtCoeff_unitVec_mem (k : WeightIdx) (b : Fin 3) :
    hT.biVec (wtCoeff k) (unitVec b) ∈ hT.wtSpan := by
  have hgen : ∀ k' : WeightIdx, hT.biVec (wtCoeff k) (wtCoeff k') ∈ hT.wtSpan :=
    fun k' => Submodule.mem_iSup_of_mem (k, k') (Submodule.mem_span_singleton_self _)
  rcases eq_rootPair_or_cartanId b with rfl | rfl | rfl
  · rw [unitVec_rootPair_fst, hT.biVec_smul_right, hT.biVec_add_right]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hgen _) (hgen _))
  · rw [unitVec_rootPair_snd, hT.biVec_smul_right, hT.biVec_sub_right]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hgen _) (hgen _))
  · rw [unitVec_cartanId]
    exact hgen _

/-- Every component of `T` lies in the join of the weight lines. -/
lemma biVec_unitVec_mem (a b : Fin 3) :
    hT.biVec (unitVec a) (unitVec b) ∈ hT.wtSpan := by
  rcases eq_rootPair_or_cartanId a with rfl | rfl | rfl
  · rw [unitVec_rootPair_fst, hT.biVec_smul_left, hT.biVec_add_left]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (hT.biVec_wtCoeff_unitVec_mem _ _) (hT.biVec_wtCoeff_unitVec_mem _ _))
  · rw [unitVec_rootPair_snd, hT.biVec_smul_left, hT.biVec_sub_left]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (hT.biVec_wtCoeff_unitVec_mem _ _) (hT.biVec_wtCoeff_unitVec_mem _ _))
  · rw [unitVec_cartanId]
    exact hT.biVec_wtCoeff_unitVec_mem _ _

/-- The weight vectors span the components: the change of basis from the Pauli basis to
  the weight basis is invertible. -/
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

## Aside: the gauge form of the theorem

-/

/-- The gauge form on an algebra: a gauge invariant of the span joined with a gauge-stable
  submodule is a multiple of the trace contraction up to a gauge-invariant remainder, once
  the trace contraction is known to be gauge invariant. The multiplicativity hypothesis
  `hmul` is not used; `MassDimEight` passes it. -/
@[nolint unusedArguments]
theorem mem_span_sup_invariant_iff {B : Type*} [Ring B] [Algebra ℂ B]
    {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU2BiAdjoint B repGauge T) (hmul : IsMulRep repGauge)
    (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (htc : ∀ g : GaugeGroupI, repGauge g hT.traceContraction = hT.traceContraction)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • hT.traceContraction + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  obtain ⟨c, y, hyS, hxy, -⟩ :=
    hT.mem_span_sup_su2_invariant_iff x S (fun U => hS (1, U, 1)) hx fun U => hinv (1, U, 1)
  refine ⟨c, y, hyS, hxy, fun g => ?_⟩
  rw [show y = x - c • hT.traceContraction from by rw [hxy]; abel, map_sub, map_smul,
    hinv g, htc g]

end IsSU2BiAdjoint

end StandardModel
