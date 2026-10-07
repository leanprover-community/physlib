/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.TraceForm
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.Basic
/-!

# The adjoint representation of `SU(n)`

The adjoint representation of `SU(n)` and its complexification, defined as `x ↦ g x g†`.

## i. Overview

We define the adjont representation of `SU(n)` on its Lie algebra `su(n)` and its complexification.
The adjoint is defined by conjugation, `x ↦ g x g†`. It preserves the bracket, and its kernel is
the centre of `SU(n)`, the scalar matrices (A).

The contraction `adjointContr` of two real adjoint indices is the trace form `x ⊗ y ↦ tr (x y)` on
`su(n)`, which is real since `x` and `y` are hermitian, and invariant under the adjoint action by
the cyclicity of the trace. It is symmetric, invariant under the bracket, and positive definite
since `tr (x x) = tr (x x†)` vanishes only for `x = 0` (B.1).

The contraction `adjointℂContr` of two complex adjoint indices is its complexification. On the
underlying matrices it is the trace form `A ⊗ B ↦ tr (A B)`, and it is again symmetric, invariant
under the bracket and nondegenerate (B.2).

## ii. Key results

- `SULieAlgebra.adjoint` : the adjoint representation on `su(n)`.
- `SULieAlgebra.adjointℂ` : the adjoint representation on the complexification.
- `SULieAlgebra.adjoint_eq_iff` : the adjoint representation is faithful modulo the centre.
- `SULieAlgebra.adjointContr` : the contraction of two real adjoint indices.
- `SULieAlgebra.adjointℂContr` : the contraction of two complex adjoint indices.
- `SULieAlgebra.adjointContr_self_pos` : the real contraction is positive definite.
- `SULieAlgebra.adjointℂContr_nondegenerate` : the complex contraction is nondegenerate.
- `SULieAlgebra.end_eq_smul_id_of_commute_adjointℂ` : Schur's lemma for the complex adjoint
  representation.
- `SULieAlgebra.intertwiningMap_eq_smul_adjointℂContr` : every intertwiner `adj ⊗ adj → ℂ` is a
  multiple of the complex contraction.
- `SULieAlgebra.adjointContr_eq_killingForm` : the contraction is `-1 / (2n)` times the Killing
  form.

## iii. Table of contents

- A. The adjoint representation
  - A.1. The real adjoint representation
  - A.2. The complex adjoint representation
- B. The contraction of adjoint indices
  - B.1. The real case
  - B.2. The complex case
  - B.3. The Killing form

## iv. References

* None.

-/

@[expose] public section

open Matrix TensorProduct ComplexStarModule Kronecker LieAlgebra
open scoped ComplexOrder

namespace SULieAlgebra

/-!

## A. The adjoint representation

-/

/-!

### A.1. The real adjoint representation

-/

/-- The adjoint representation `x ↦ g x g†` of `SU(n)` on its real Lie algebra `su(n)`. -/
noncomputable def adjoint {n : ℕ} :
    Representation ℝ (specialUnitaryGroup (Fin n) ℂ) (SULieAlgebra n ℂ) :=
  conj.comp (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

/-- The underlying matrix of `adjoint g x` is `g x g†`. -/
@[simp]
lemma adjoint_val {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (x : SULieAlgebra n ℂ) :
    (adjoint g x).1 = g.1 * x.1 * star g.1 := rfl

/-- The adjoint representation preserves the bracket, so `SU(n)` acts on `su(n)` by Lie algebra
  automorphisms. -/
lemma adjoint_lie {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (x y : SULieAlgebra n ℂ) :
    adjoint g ⁅x, y⁆ = ⁅adjoint g x, adjoint g y⁆ :=
  conj_lie _ x y

/-- The kernel of the adjoint representation is the centre of `SU(n)`: `g` acts trivially exactly
  when it is a scalar matrix `c 1`. -/
lemma adjoint_eq_one_iff {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    adjoint g = 1 ↔ ∃ c : ℂ, g.1 = c • 1 := by
  have hg := (mem_specialUnitaryGroup_iff.mp g.2).1
  constructor
  · intro h
    -- `g x g† = x` for all `x`, so `g` commutes with `su(n)` and hence with every matrix
    have hx (x : SULieAlgebra n ℂ) : Commute g.1 x.1 := by
      have hx := congrArg Subtype.val (LinearMap.congr_fun h x)
      rw [adjoint_val, Module.End.one_apply] at hx
      calc g.1 * x.1 = g.1 * x.1 * star g.1 * g.1 := by
            rw [Matrix.mul_assoc _ (star g.1), hg.1, Matrix.mul_one]
        _ = x.1 * g.1 := by rw [hx]
    have hcen : g.1 ∈ Set.center (Matrix (Fin n) (Fin n) ℂ) :=
      Semigroup.mem_center_iff.mpr fun N => (commute_of_forall_commute_val hx N).symm.eq
    rw [Matrix.center_eq_range] at hcen
    obtain ⟨c, hc⟩ := hcen
    exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  · rintro ⟨c, hc⟩
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hcomm : g.1 * x.1 = x.1 * g.1 := by
      rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [adjoint_val, Module.End.one_apply, hcomm, Matrix.mul_assoc, hg.2, Matrix.mul_one]

/-- Two elements of `SU(n)` have the same adjoint action exactly when they differ by a scalar:
  the adjoint representation is faithful on `SU(n)` modulo its centre. -/
lemma adjoint_eq_iff {n : ℕ} (g h : specialUnitaryGroup (Fin n) ℂ) :
    adjoint g = adjoint h ↔ ∃ c : ℂ, g.1 = c • h.1 := by
  have hh := (mem_specialUnitaryGroup_iff.mp h.2).1
  have hval : (g * h⁻¹).1 = g.1 * star h.1 := rfl
  have key : adjoint g = adjoint h ↔ adjoint (g * h⁻¹) = 1 := by
    constructor
    · intro hgh
      rw [map_mul, hgh, ← map_mul, mul_inv_cancel, map_one]
    · intro h1
      rw [← one_mul (adjoint h), ← h1, ← map_mul, inv_mul_cancel_right]
  rw [key, adjoint_eq_one_iff, hval]
  refine exists_congr fun c => ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [← Matrix.mul_one g.1, ← hh.1, ← Matrix.mul_assoc, hc, Matrix.smul_mul, Matrix.one_mul]
  · rw [hc, Matrix.smul_mul, hh.2]

/-!

### A.2. The complex adjoint representation

-/

/-- The adjoint representation of `SU(n)` on the complexification `ℂ ⊗[ℝ] su(n)`: the
  complexification of the adjoint representation `adjoint` on `su(n)`. -/
noncomputable def adjointℂ {n : ℕ} :
    Representation ℂ (specialUnitaryGroup (Fin n) ℂ) (Complexification n) :=
  (Module.End.baseChangeHom ℝ ℂ (SULieAlgebra n ℂ) : Module.End ℝ _ →* Module.End ℂ _).comp
    adjoint

@[simp]
lemma adjointℂ_tmul {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (z : ℂ) (x : SULieAlgebra n ℂ) :
    adjointℂ g (z ⊗ₜ x) = z ⊗ₜ adjoint g x := rfl

/-- The complex adjoint representation preserves the bracket of the complexification, so `SU(n)`
  acts on `ℂ ⊗[ℝ] su(n)` by Lie algebra automorphisms. -/
lemma adjointℂ_lie {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (A B : Complexification n) :
    adjointℂ g ⁅A, B⁆ = ⁅adjointℂ g A, adjointℂ g B⁆ := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    induction B using TensorProduct.inductionOn with
    | tmul w y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, adjointℂ_tmul, adjointℂ_tmul, adjointℂ_tmul,
        LieAlgebra.ExtendScalars.bracket_tmul, adjoint_lie]
    | add B B' hB hB' =>
      rw [lie_add (L := Complexification n), map_add, hB, hB', map_add,
        lie_add (L := Complexification n)]
  | add A A' hA hA' =>
    rw [add_lie (L := Complexification n), map_add, hA, hA', map_add,
      add_lie (L := Complexification n)]

/-- The kernel of the complex adjoint representation is the centre of `SU(n)`, as for the real
  adjoint representation. -/
lemma adjointℂ_eq_one_iff {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    adjointℂ g = 1 ↔ ∃ c : ℂ, g.1 = c • 1 := by
  rw [← adjoint_eq_one_iff]
  refine ⟨fun h => LinearMap.ext fun x => Subtype.ext ?_, fun h => ?_⟩
  · have hx := congrArg toMatrixℂ (LinearMap.congr_fun h (1 ⊗ₜ x))
    rwa [adjointℂ_tmul, Module.End.one_apply, toMatrixℂ_tmul, toMatrixℂ_tmul, one_smul,
      one_smul] at hx
  · change Module.End.baseChangeHom ℝ ℂ _ (adjoint g) = 1
    rw [h, map_one]

/-- Two elements of `SU(n)` have the same complex adjoint action exactly when they differ by a
  scalar, as for the real adjoint representation. -/
lemma adjointℂ_eq_iff {n : ℕ} (g h : specialUnitaryGroup (Fin n) ℂ) :
    adjointℂ g = adjointℂ h ↔ ∃ c : ℂ, g.1 = c • h.1 := by
  rw [← adjoint_eq_iff]
  refine ⟨fun hgh => LinearMap.ext fun x => Subtype.ext ?_, fun hgh => ?_⟩
  · have hx := congrArg toMatrixℂ (LinearMap.congr_fun hgh (1 ⊗ₜ x))
    rwa [adjointℂ_tmul, adjointℂ_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, one_smul, one_smul] at hx
  · change Module.End.baseChangeHom ℝ ℂ _ (adjoint g) = Module.End.baseChangeHom ℝ ℂ _ (adjoint h)
    rw [hgh]

/-!

### A.2.1. Relation to underlying matrix

-/

/-- The adjoint representation conjugates the matrix, `M ↦ g M g†`. -/
@[simp]
lemma toMatrixℂ_adjointℂ {n} (g : specialUnitaryGroup (Fin n) ℂ) (A : Complexification n) :
    toMatrixℂ (adjointℂ g A) = g.1 * toMatrixℂ A * star g.1 := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    rw [adjointℂ_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, adjoint_val, Matrix.mul_smul,
      Matrix.smul_mul]
  | add A B hA hB => rw [map_add, map_add, hA, hB, map_add, Matrix.mul_add, Matrix.add_mul]

/-- Conjugation by any unitary matrix is the adjoint action of an element of `SU(n)`: a
  unitary matrix agrees with an element of `SU(n)` up to a phase, which conjugation does not
  see. -/
lemma exists_toMatrixℂ_adjointℂ_eq_unitary {n : ℕ} (U : unitaryGroup (Fin n) ℂ) :
    ∃ g : specialUnitaryGroup (Fin n) ℂ, ∀ A : Complexification n,
      toMatrixℂ (adjointℂ g A) = U.1 * toMatrixℂ A * star U.1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, fun A => Subsingleton.elim _ _⟩
  -- a phase `c` with `c ^ n = (det U)⁻¹`, of modulus one as `det U` is
  have hd : Complex.normSq U.1.det = 1 := by
    exact_mod_cast Complex.normSq_eq_conj_mul_self.trans
      (Unitary.star_mul_self_of_mem (det_of_mem_unitary U.2))
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ n = (U.1.det)⁻¹ := ⟨_, Complex.cpow_nat_inv_pow _ hn.ne'⟩
  have hc1 : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg c)
      hn.ne').1 (by rw [← map_pow, hc, map_inv₀, hd, inv_one]), Complex.ofReal_one]
  refine ⟨⟨c • U.1, mem_specialUnitaryGroup_iff.2 ⟨mem_unitaryGroup_iff.2 ?_, ?_⟩⟩, fun A => ?_⟩
  · rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc1, mem_unitaryGroup_iff.1 U.2,
      one_smul]
  · rw [det_smul, Fintype.card_fin, hc, inv_mul_cancel₀ fun h => by simp [h] at hd]
  · rw [toMatrixℂ_adjointℂ]
    change c • U.1 * toMatrixℂ A * star (c • U.1) = _
    rw [star_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc1, one_smul]

/-- The adjoint action realises any permutation `σ` of the coordinates: some element of `SU(n)`
  moves the entry `(x, y)` of every matrix to `(σ x, σ y)`. -/
lemma exists_toMatrixℂ_adjointℂ_apply_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∃ g : specialUnitaryGroup (Fin n) ℂ, ∀ A x y,
      toMatrixℂ (adjointℂ g A) (σ x) (σ y) = toMatrixℂ A x y := by
  have hP : Equiv.Perm.permMatrix ℂ σ⁻¹ ∈ unitaryGroup (Fin n) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix, inv_inv,
      ← permMatrix_mul, mul_inv_cancel, permMatrix_one]
  obtain ⟨g, hg⟩ := exists_toMatrixℂ_adjointℂ_eq_unitary ⟨_, hP⟩
  refine ⟨g, fun A x y => ?_⟩
  rw [hg]
  change (Equiv.Perm.permMatrix ℂ σ⁻¹ * toMatrixℂ A * star (Equiv.Perm.permMatrix ℂ σ⁻¹))
    (σ x) (σ y) = _
  rw [star_eq_conjTranspose, conjTranspose_permMatrix, inv_inv, Equiv.Perm.permMatrix,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp

/-- The adjoint action of a diagonal element of `SU(n)` scales the entry at `(x, y)` of the
  matrix by `d x * star (d y)`. -/
lemma toMatrixℂ_adjointℂ_apply_of_diagonal {n} {g : specialUnitaryGroup (Fin n) ℂ}
    {d : Fin n → ℂ} (hg : g.1 = diagonal d) (A : Complexification n) (x y : Fin n) :
    toMatrixℂ (adjointℂ g A) x y = d x * star (d y) * toMatrixℂ A x y := by
  rw [toMatrixℂ_adjointℂ, hg, star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal,
    diagonal_mul, Pi.star_apply]
  ring

/-- An eigenvector of the adjoint action of a diagonal element of `SU(n)`, with eigenvalue `c`,
  vanishes at the entries `(x, y)` with `d x * star (d y) ≠ c`. -/
lemma toMatrixℂ_apply_eq_zero_of_adjointℂ_eq_smul {n : ℕ} {g : specialUnitaryGroup (Fin n) ℂ}
    {d : Fin n → ℂ} (hg : g.1 = diagonal d) {A : Complexification n} {c : ℂ}
    (hA : adjointℂ g A = c • A) {x y : Fin n} (hxy : d x * star (d y) ≠ c) :
    toMatrixℂ A x y = 0 := by
  have h := congrArg (fun B => toMatrixℂ B x y) hA
  simp only [toMatrixℂ_adjointℂ_apply_of_diagonal hg, map_smul, Matrix.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.1 (show (d x * star (d y) - c) * toMatrixℂ A x y = 0 by
    linear_combination h)).resolve_left (sub_ne_zero.2 hxy)

/-- An element of the complexification supported at the entry `(p, q)` is an eigenvector of the
  adjoint action of a diagonal element of `SU(n)`, with eigenvalue `d p * star (d q)`. -/
lemma adjointℂ_eq_smul_of_toMatrixℂ_apply_eq_zero {n : ℕ} {g : specialUnitaryGroup (Fin n) ℂ}
    {d : Fin n → ℂ} (hg : g.1 = diagonal d) {A : Complexification n} {p q : Fin n}
    (hA : ∀ x y, ¬(x = p ∧ y = q) → toMatrixℂ A x y = 0) :
    adjointℂ g A = (d p * star (d q)) • A := by
  refine toMatrixℂ_injective (Matrix.ext fun x y => ?_)
  rw [toMatrixℂ_adjointℂ_apply_of_diagonal hg, map_smul, Matrix.smul_apply, smul_eq_mul]
  by_cases h : x = p ∧ y = q
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · rw [hA x y h, mul_zero, mul_zero]

lemma toMatrixℂ_adjointℂ_trace {n} (g : specialUnitaryGroup (Fin n) ℂ) (A : Complexification n) :
    (toMatrixℂ (adjointℂ g A)).trace = (toMatrixℂ A).trace := by
  rw [toMatrixℂ_adjointℂ, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, Matrix.mul_assoc,
    (mem_specialUnitaryGroup_iff.mp g.2).1.1, Matrix.mul_one]

/-!

## B. The contraction of adjoint indices

### B.1. The real case

-/

/-- The contraction of two real adjoint indices: the trace form `x ⊗ y ↦ tr (x y)` on `su(n)`,
  which is real since `x` and `y` are hermitian. -/
noncomputable def adjointContr {n : ℕ} : ((adjoint (n := n)).tprod adjoint).IntertwiningMap
    (Representation.trivial ℝ (specialUnitaryGroup (Fin n) ℂ) ℝ) where
  toLinearMap := TensorProduct.lift <|
    LinearMap.mk₂ ℝ (fun x y : SULieAlgebra n ℂ => (x.1 * y.1).trace.re)
      (fun x x' y => by simp [add_mul, trace_add])
      (fun r x y => by simp)
      (fun x y y' => by simp [mul_add, trace_add])
      (fun r x y => by simp)
  isIntertwining' g := TensorProduct.ext' fun x y => by
    have hg : star g.1 * g.1 = 1 := (mem_specialUnitaryGroup_iff.mp g.2).1.1
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply, lift.tmul, LinearMap.mk₂_apply, adjoint_val]
    rw [show g.1 * x.1 * star g.1 * (g.1 * y.1 * star g.1) = g.1 * (x.1 * y.1) * star g.1 by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star g.1), hg, Matrix.one_mul],
      Matrix.trace_mul_cycle, hg, Matrix.one_mul]

/-- The real contraction is the real part of the trace, `x ⊗ y ↦ re tr (x y)`. -/
@[simp]
lemma adjointContr_tmul {n : ℕ} (x y : SULieAlgebra n ℂ) :
    adjointContr (x ⊗ₜ y) = (x.1 * y.1).trace.re := rfl

/-- The adjoint representation preserves the real contraction, so `SU(n)` acts on `su(n)` by
  isometries. -/
lemma adjointContr_adjoint {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (x y : SULieAlgebra n ℂ) :
    adjointContr (adjoint g x ⊗ₜ adjoint g y) = adjointContr (x ⊗ₜ y) :=
  Representation.IntertwiningMap.isIntertwining _ _ adjointContr g (x ⊗ₜ y)

/-- The trace `tr (x y)` of two elements of `su(n)` is real, equal to their contraction. -/
lemma ofReal_adjointContr_tmul {n : ℕ} (x y : SULieAlgebra n ℂ) :
    (adjointContr (x ⊗ₜ y) : ℂ) = (x.1 * y.1).trace := by
  rw [adjointContr_tmul]
  refine Complex.conj_eq_iff_re.1 ?_
  change star (x.1 * y.1).trace = _
  rw [← trace_conjTranspose, conjTranspose_mul, ← star_eq_conjTranspose,
    ← star_eq_conjTranspose, x.star_val_eq, y.star_val_eq, trace_mul_comm]

lemma adjointContr_symm {n : ℕ} (x y : SULieAlgebra n ℂ) :
    adjointContr (x ⊗ₜ y) = adjointContr (y ⊗ₜ x) := by
  rw [adjointContr_tmul, adjointContr_tmul, trace_mul_comm]

/-- The real contraction is invariant under the bracket, `tr (⁅x, y⁆ z) = tr (x ⁅y, z⁆)`; in terms
  of generators, the structure constants `tr (T^a ⁅T^b, T^c⁆)` are totally antisymmetric. -/
lemma adjointContr_lie {n : ℕ} (x y z : SULieAlgebra n ℂ) :
    adjointContr (⁅x, y⁆ ⊗ₜ z) = adjointContr (x ⊗ₜ ⁅y, z⁆) := by
  rw [adjointContr_tmul, adjointContr_tmul, val_bracket, val_bracket, Matrix.smul_mul,
    Matrix.mul_smul, trace_smul, trace_smul, sub_mul, mul_sub, trace_sub, trace_sub,
    Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm y.1 (x.1 * z.1), Matrix.mul_assoc]

/-- The real contraction is positive semidefinite: `tr (x x) = tr (x x†) ≥ 0`. -/
lemma adjointContr_self_nonneg {n : ℕ} (x : SULieAlgebra n ℂ) : 0 ≤ adjointContr (x ⊗ₜ x) := by
  have h := (posSemidef_self_mul_conjTranspose x.1).trace_nonneg
  rw [← star_eq_conjTranspose, x.star_val_eq, ← ofReal_adjointContr_tmul] at h
  exact Complex.zero_le_real.mp h

/-- The real contraction of `x` with itself vanishes only for `x = 0`. -/
lemma adjointContr_self_eq_zero_iff {n : ℕ} (x : SULieAlgebra n ℂ) :
    adjointContr (x ⊗ₜ x) = 0 ↔ x = 0 := by
  refine ⟨fun hx => Subtype.ext (trace_mul_conjTranspose_self_eq_zero_iff.mp ?_),
    fun hx => by rw [hx, zero_tmul, map_zero]⟩
  rw [← star_eq_conjTranspose, x.star_val_eq, ← ofReal_adjointContr_tmul, hx, Complex.ofReal_zero]

/-- The real contraction is positive definite, making it an inner product on `su(n)`. -/
lemma adjointContr_self_pos {n : ℕ} {x : SULieAlgebra n ℂ} (hx : x ≠ 0) :
    0 < adjointContr (x ⊗ₜ x) :=
  (adjointContr_self_nonneg x).lt_of_ne fun h => hx ((adjointContr_self_eq_zero_iff x).mp h.symm)

lemma adjointContr_separating_left {n : ℕ} (x : SULieAlgebra n ℂ)
    (hx : ∀ y, adjointContr (x ⊗ₜ y) = 0) : x = 0 :=
  (adjointContr_self_eq_zero_iff x).mp (hx x)

lemma adjointContr_separating_right {n : ℕ} (y : SULieAlgebra n ℂ)
    (hy : ∀ x, adjointContr (x ⊗ₜ y) = 0) : y = 0 :=
  adjointContr_separating_left y fun x => by rw [adjointContr_symm, hy]

/-- The real contraction separates `su(n)`: `y ↦ (x ↦ re tr (x y))` is injective. -/
lemma adjointContr_flip_injective {n : ℕ} :
    Function.Injective (TensorProduct.curry (adjointContr (n := n)).toLinearMap).flip := by
  intro w w' h
  refine sub_eq_zero.1 (adjointContr_separating_right _ fun x => ?_)
  have hx := LinearMap.congr_fun h x
  simp only [LinearMap.flip_apply, TensorProduct.curry_apply] at hx
  rw [tmul_sub, map_sub, sub_eq_zero]
  exact hx

/-- The real contraction, as a bilinear form, is symmetric. -/
lemma adjointContr_isSymm {n : ℕ} :
    LinearMap.BilinForm.IsSymm (TensorProduct.curry (adjointContr (n := n)).toLinearMap) :=
  ⟨fun x y => adjointContr_symm x y⟩

/-- The real contraction, as a bilinear form, is nondegenerate. -/
lemma adjointContr_nondegenerate {n : ℕ} :
    (TensorProduct.curry (adjointContr (n := n)).toLinearMap).Nondegenerate :=
  ⟨fun x hx => adjointContr_separating_left x hx, fun y hy => adjointContr_separating_right y hy⟩

/-!

### B.2. The complex case

-/

/-- The contraction of two complex adjoint indices: the complexification of the real contraction
  `adjointContr`. -/
noncomputable def adjointℂContr {n : ℕ} : ((adjointℂ (n := n)).tprod adjointℂ).IntertwiningMap
    (Representation.trivial ℂ (specialUnitaryGroup (Fin n) ℂ) ℂ) where
  toLinearMap := TensorProduct.lift <| LinearMap.BilinForm.baseChange ℂ <|
    TensorProduct.curry (adjointContr (n := n)).toLinearMap
  isIntertwining' g := TensorProduct.ext' fun A B => by
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply]
    induction A using TensorProduct.inductionOn with
    | tmul z x =>
      induction B using TensorProduct.inductionOn with
      | tmul w y =>
        simp only [adjointℂ_tmul, lift.tmul, LinearMap.BilinForm.baseChange_tmul,
          TensorProduct.curry_apply, Representation.IntertwiningMap.toLinearMap_apply,
          adjointContr_adjoint]
      | add B B' hB hB' => rw [map_add, tmul_add, map_add, hB, hB', tmul_add, map_add]
    | add A A' hA hA' => rw [map_add, add_tmul, map_add, hA, hA', add_tmul, map_add]

/-- The adjoint representation preserves the complex contraction. -/
lemma adjointℂContr_adjointℂ {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ)
    (A B : Complexification n) :
    adjointℂContr (adjointℂ g A ⊗ₜ adjointℂ g B) = adjointℂContr (A ⊗ₜ B) := by
  have h := Representation.IntertwiningMap.isIntertwining _ _ (adjointℂContr (n := n)) g (A ⊗ₜ B)
  simpa only [Representation.tprod_apply, TensorProduct.map_tmul, Representation.trivial_apply]
    using h

/-- The contraction is the trace form, `A ⊗ B ↦ tr (A B)`. -/
lemma adjointℂContr_tmul (A B : Complexification n) :
    adjointℂContr (A ⊗ₜ B) = (toMatrixℂ A * toMatrixℂ B).trace := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    induction B using TensorProduct.inductionOn with
    | tmul w y =>
      change TensorProduct.lift _ ((z ⊗ₜ x) ⊗ₜ (w ⊗ₜ y)) = _
      rw [lift.tmul, LinearMap.BilinForm.baseChange_tmul, TensorProduct.curry_apply,
        Representation.IntertwiningMap.toLinearMap_apply, Complex.real_smul,
        ofReal_adjointContr_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, Matrix.smul_mul,
        Matrix.mul_smul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul]
      ring
    | add B B' hB hB' => rw [tmul_add, map_add, hB, hB', map_add, Matrix.mul_add, trace_add]
  | add A A' hA hA' => rw [add_tmul, map_add, hA, hA', map_add, Matrix.add_mul, trace_add]

/-- On the real elements `1 ⊗ x` of the complexification the complex contraction is the real
  contraction, so the two agree on real gauge fields. -/
lemma adjointℂContr_one_tmul {n : ℕ} (x y : SULieAlgebra n ℂ) :
    adjointℂContr ((1 ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)) = adjointContr (x ⊗ₜ y) := by
  rw [adjointℂContr_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, one_smul, one_smul,
    ofReal_adjointContr_tmul]

lemma adjointℂContr_symm {n} (A B : Complexification n) :
    adjointℂContr (A ⊗ₜ B) = adjointℂContr (B ⊗ₜ A) := by
  rw [adjointℂContr_tmul, adjointℂContr_tmul, Matrix.trace_mul_comm]

/-- The complex contraction is invariant under the bracket, `tr (⁅A, B⁆ C) = tr (A ⁅B, C⁆)`. -/
lemma adjointℂContr_lie {n} (A B C : Complexification n) :
    adjointℂContr (⁅A, B⁆ ⊗ₜ C) = adjointℂContr (A ⊗ₜ ⁅B, C⁆) := by
  rw [adjointℂContr_tmul, adjointℂContr_tmul, toMatrixℂ_lie, toMatrixℂ_lie, Matrix.smul_mul,
    Matrix.mul_smul, trace_smul, trace_smul, sub_mul, mul_sub, trace_sub, trace_sub,
    Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm (toMatrixℂ B) (toMatrixℂ A * toMatrixℂ C),
    Matrix.mul_assoc]

lemma adjointℂContr_separating_left {n} (A : Complexification n)
    (hA : ∀ B, adjointℂContr (A ⊗ₜ B) = 0) : A = 0 := by
  have h := hA (ofTracelessℂ (toMatrixℂ A)ᴴ
    (by rw [trace_conjTranspose, trace_toMatrixℂ, star_zero]))
  rw [adjointℂContr_tmul, toMatrixℂ_ofTracelessℂ, trace_mul_conjTranspose_self_eq_zero_iff] at h
  exact toMatrixℂ_injective (h.trans (map_zero _).symm)

lemma adjointℂContr_separating_right {n} (B : Complexification n)
    (hB : ∀ A, adjointℂContr (A ⊗ₜ B) = 0) : B = 0 :=
  adjointℂContr_separating_left B fun A => by rw [adjointℂContr_symm, hB]

/-- The contraction separates the complexification: `B ↦ (A ↦ tr (A B))` is injective. -/
lemma adjointℂContr_flip_injective :
    Function.Injective (TensorProduct.curry (adjointℂContr (n := n)).toLinearMap).flip := by
  intro w w' h
  refine sub_eq_zero.1 (adjointℂContr_separating_right _ fun A => ?_)
  have hA := LinearMap.congr_fun h A
  simp only [LinearMap.flip_apply, TensorProduct.curry_apply] at hA
  rw [tmul_sub, map_sub, sub_eq_zero]
  exact hA

/-- The complex contraction, as a bilinear form, is symmetric. -/
lemma adjointℂContr_isSymm {n : ℕ} :
    LinearMap.BilinForm.IsSymm (TensorProduct.curry (adjointℂContr (n := n)).toLinearMap) :=
  ⟨fun A B => adjointℂContr_symm A B⟩

/-- The complex contraction, as a bilinear form, is nondegenerate. -/
lemma adjointℂContr_nondegenerate {n : ℕ} :
    (TensorProduct.curry (adjointℂContr (n := n)).toLinearMap).Nondegenerate :=
  ⟨fun A hA => adjointℂContr_separating_left A hA,
    fun B hB => adjointℂContr_separating_right B hB⟩

/-!

### B.3. The Killing form

-/

/-- The contraction is the Killing form on the complexified Lie
  algebra, up to a factor of `-1/(2n)`. -/
lemma adjointℂContr_eq_killingForm {n : ℕ} (A B : Complexification n) :
    adjointℂContr (A ⊗ₜ B) = -(1 / (2 * (n : ℂ))) * killingForm ℂ (Complexification n) A B := by
  set K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
    -(1 ⊗ₖ (toMatrixℂ A * toMatrixℂ B) - (toMatrixℂ B)ᵀ ⊗ₖ toMatrixℂ A
      - (toMatrixℂ A)ᵀ ⊗ₖ toMatrixℂ B + (toMatrixℂ B * toMatrixℂ A)ᵀ ⊗ₖ 1)
  let e : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] (Fin n × Fin n → ℂ) :=
    LinearEquiv.ofBijective ⟨⟨vec, vec_add⟩, vec_smul⟩ vec_bijective
  set F := e.symm.conj (toLin' K)
  have hF (M : Matrix (Fin n) (Fin n) ℂ) :
      F M = -(toMatrixℂ A * (toMatrixℂ B * M - M * toMatrixℂ B)
        - (toMatrixℂ B * M - M * toMatrixℂ B) * toMatrixℂ A) := by
    apply e.injective
    simp only [F, e, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply,
      LinearMap.coe_mk, AddHom.coe_mk, toLin'_apply, K, neg_mulVec, sub_mulVec, add_mulVec,
      kronecker_mulVec_vec, transpose_transpose, transpose_one, Matrix.mul_one, Matrix.one_mul,
      ← vec_sub, ← vec_add, ← vec_neg]
    congr 1
    noncomm_ring
  have h1 : toMatrixℂ ∘ₗ (ad ℂ (Complexification n) A ∘ₗ ad ℂ (Complexification n) B)
      = F ∘ₗ toMatrixℂ := by
    refine LinearMap.ext fun M => ?_
    simp only [LinearMap.comp_apply, ad_apply, toMatrixℂ_lie, hF, Matrix.mul_smul,
      Matrix.smul_mul, ← smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul]
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective toMatrixℂ
    (LinearMap.ker_eq_bot.2 toMatrixℂ_injective)
  have h2 : (toMatrixℂ ∘ₗ π) ∘ₗ F = F := by
    refine LinearMap.ext fun M => ?_
    have hM : (F M).trace = 0 := by
      rw [hF, trace_neg, trace_sub, trace_mul_comm, sub_self, neg_zero]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← toMatrixℂ_ofTracelessℂ (F M) hM,
      ← LinearMap.comp_apply π, hπ, LinearMap.id_apply]
  have hK : killingForm ℂ (Complexification n) A B = -(2 * n) * adjointℂContr (A ⊗ₜ B) := by
    rw [killingForm_apply_apply, ← LinearMap.id_comp (ad ℂ (Complexification n) A ∘ₗ _), ← hπ,
      LinearMap.comp_assoc, h1, LinearMap.trace_comp_comm', LinearMap.comp_assoc,
      ← Module.End.mul_eq_comp, LinearMap.trace_mul_comm, Module.End.mul_eq_comp, h2,
      adjointℂContr_tmul]
    simp only [F, LinearMap.trace_conj', trace_toLin'_eq, K, trace_neg, trace_sub, trace_add,
      trace_kronecker, trace_one, trace_transpose, trace_toMatrixℂ, Fintype.card_fin, mul_zero,
      trace_mul_comm (toMatrixℂ B)]
    ring
  rw [hK]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [adjointℂContr_tmul, Matrix.trace]
  · have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

/-- The contraction is the Killing form on the Lie algebra, up to a factor of `-1/(2n)`. -/
lemma adjointContr_eq_killingForm {n : ℕ} (x y : SULieAlgebra n ℂ) :
    adjointContr (x ⊗ₜ y) = -(1 / (2 * (n : ℝ))) * killingForm ℝ (SULieAlgebra n ℂ) x y := by
  have h := adjointℂContr_eq_killingForm (1 ⊗ₜ x) (1 ⊗ₜ y)
  rw [adjointℂContr_one_tmul, killingForm, LieModule.traceForm_baseChange,
    LinearMap.BilinForm.baseChange_tmul, mul_one, Complex.real_smul, mul_one] at h
  apply Complex.ofReal_injective
  push_cast
  exact h


/-!

## C. The adjoint and endomorphisms

-/

/-- An endomorphism commuting with the adjoint action keeps an element supported at an
  off-diagonal entry `(p, q)` supported there. -/
lemma toMatrixℂ_apply_eq_zero_of_comp_eq {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) {p q : Fin n} (hpq : p ≠ q)
    {A : Complexification n} (hA : ∀ x y, ¬(x = p ∧ y = q) → toMatrixℂ A x y = 0)
    (x y : Fin n) (hxy : ¬(x = p ∧ y = q)) : toMatrixℂ (T A) x y = 0 := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 5 := ⟨_, Complex.isPrimitiveRoot_exp 5 (by norm_num)⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  set e : Fin n → ℤ := fun x => if x = p then 1 else if x = q then -1 else 0 with he
  have hphase (x y : Fin n) : ζ ^ e x * star (ζ ^ e y) = ζ ^ (e x - e y) := by
    rw [star_zpow₀, Complex.star_def, ← Complex.inv_eq_conj (hζ.norm'_eq_one (by norm_num)),
      _root_.inv_zpow, ← _root_.zpow_neg, ← zpow_add₀ hζ0, sub_eq_add_neg]
  have hkey : ζ ^ (e x - e y) ≠ ζ ^ (e p - e q) := by
    rw [Ne, ← div_eq_one_iff_eq (zpow_ne_zero _ hζ0), ← zpow_sub₀ hζ0, hζ.zpow_eq_one_iff_dvd]
    simp only [he]
    split_ifs <;> omega
  have hmem : diagonal (fun x => ζ ^ e x) ∈ specialUnitaryGroup (Fin n) ℂ := by
    rw [mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
        diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext x
      rw [Pi.star_apply, hphase, sub_self, zpow_zero]
    · rw [det_diagonal,
        Finset.prod_congr rfl fun x _ => (show ζ ^ e x = (if x = p then ζ else 1) *
          (if x = q then ζ⁻¹ else 1) by simp only [he]; split_ifs <;> simp_all),
        Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq',
        ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _), mul_inv_cancel₀ hζ0]
  have hTA : adjointℂ ⟨_, hmem⟩ (T A) = ζ ^ (e p - e q) • T A := by
    rw [← LinearMap.comp_apply (adjointℂ _), ← hT, LinearMap.comp_apply,
      adjointℂ_eq_smul_of_toMatrixℂ_apply_eq_zero rfl hA, map_smul, hphase]
  exact toMatrixℂ_apply_eq_zero_of_adjointℂ_eq_smul rfl hTA (by rwa [hphase])

/-- An endomorphism commuting with the adjoint action acts by a scalar on the elements supported
  at an off-diagonal entry `(p, q)`. -/
lemma end_eq_smul_of_toMatrixℂ_apply_eq_zero {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) {p q : Fin n} (hpq : p ≠ q) :
    ∃ μ : ℂ, ∀ A : Complexification n, (∀ x y, ¬(x = p ∧ y = q) → toMatrixℂ A x y = 0) →
      T A = μ • A := by
  obtain ⟨E, hE⟩ : ∃ E : Complexification n, toMatrixℂ E = single p q 1 :=
    ⟨_, toMatrixℂ_ofTracelessℂ _ (trace_single_eq_of_ne _ _ _ hpq)⟩
  have hsupp (B : Complexification n) (hB : ∀ x y, ¬(x = p ∧ y = q) → toMatrixℂ B x y = 0) :
      B = toMatrixℂ B p q • E := by
    refine toMatrixℂ_injective (Matrix.ext fun x y => ?_)
    rw [map_smul, hE, Matrix.smul_apply, single_apply]
    by_cases h : x = p ∧ y = q
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [hB x y h, ite_eq_right fun h' => h ⟨h'.1.symm, h'.2.symm⟩, smul_zero]
  have hEs (x y : Fin n) (h : ¬(x = p ∧ y = q)) : toMatrixℂ E x y = 0 := by
    rw [hE, single_apply, ite_eq_right fun h' => h ⟨h'.1.symm, h'.2.symm⟩]
  have hTE := hsupp (T E) (toMatrixℂ_apply_eq_zero_of_comp_eq hT hpq hEs)
  refine ⟨toMatrixℂ (T E) p q, fun A hA => ?_⟩
  rw [hsupp A hA, map_smul, smul_comm, ← hTE]

/-- An endomorphism commuting with the adjoint action acts by a scalar on the elements with zero
  diagonal. -/
lemma end_eq_smul_of_toMatrixℂ_diag_eq_zero {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) :
    ∃ μ : ℂ, ∀ A : Complexification n, (toMatrixℂ A).diag = 0 → T A = μ • A := by
  rcases lt_or_ge n 2 with hn | hn
  · -- with at most one coordinate, a matrix with zero diagonal vanishes
    have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 (by omega)
    refine ⟨0, fun A hA => ?_⟩
    rw [show A = 0 from toMatrixℂ_injective (Matrix.ext fun x y => by
      rw [Subsingleton.elim x y, map_zero]; exact congr_fun hA y), map_zero, smul_zero]
  -- the scalar `μ` at an off-diagonal entry `(i, j)` is moved to any `(p, q)` by a permutation
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin n, i ≠ j := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  obtain ⟨μ, hμ⟩ := end_eq_smul_of_toMatrixℂ_apply_eq_zero hT hij
  have hμ' (p q : Fin n) (hpq : p ≠ q) (B : Complexification n)
      (hB : ∀ x y, ¬(x = p ∧ y = q) → toMatrixℂ B x y = 0) : T B = μ • B := by
    have hr := (Equiv.swap i p).injective.ne hij
    rw [Equiv.swap_apply_left] at hr
    obtain ⟨g, hg⟩ :=
      exists_toMatrixℂ_adjointℂ_apply_perm (Equiv.swap (Equiv.swap i p j) q * Equiv.swap i p)
    have hsupp (x y : Fin n) (h : ¬(x = i ∧ y = j)) :
        toMatrixℂ (adjointℂ g⁻¹ B) x y = 0 := by
      rw [← hg, Representation.self_inv_apply]
      refine hB _ _ fun h' => h ⟨(Equiv.injective _) (h'.1.trans ?_),
        (Equiv.injective _) (h'.2.trans ?_)⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hr hpq]
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [← Representation.self_inv_apply adjointℂ g B, ← LinearMap.comp_apply T, hT,
      LinearMap.comp_apply, hμ _ hsupp, map_smul]
  -- an element with zero diagonal is a sum of elements supported at off-diagonal entries
  refine ⟨μ, fun A hA => ?_⟩
  have htr (p q : Fin n) : (single p q (toMatrixℂ A p q)).trace = 0 := by
    by_cases h : p = q
    · rw [h, show toMatrixℂ A q q = 0 from congr_fun hA q, single_zero, trace_zero]
    · exact trace_single_eq_of_ne _ _ _ h
  have hsum : A = ∑ p, ∑ q, ofTracelessℂ _ (htr p q) := toMatrixℂ_injective (by
    simp only [map_sum, toMatrixℂ_ofTracelessℂ]
    exact matrix_eq_sum_single _)
  rw [hsum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : p = q
  · subst h
    rw [show ofTracelessℂ _ (htr p p) = 0 from toMatrixℂ_injective (by
      rw [toMatrixℂ_ofTracelessℂ, map_zero, show toMatrixℂ A p p = 0 from congr_fun hA p,
        single_zero]), map_zero, smul_zero]
  · exact hμ' p q h _ fun x y hxy => by
      rw [toMatrixℂ_ofTracelessℂ, single_apply, ite_eq_right fun h' => hxy ⟨h'.1.symm, h'.2.symm⟩]

/-- An endomorphism commuting with the adjoint action, acting by `μ` on the elements with zero
  diagonal, also acts by `μ` on the element `E_pp - E_qq`. -/
lemma end_eq_smul_of_toMatrixℂ_eq_single_sub_single {n : ℕ}
    {T : Module.End ℂ (Complexification n)} (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) {μ : ℂ}
    (hμ : ∀ A : Complexification n, (toMatrixℂ A).diag = 0 → T A = μ • A) {p q : Fin n}
    {A : Complexification n} (hA : toMatrixℂ A = single p p 1 - single q q 1) : T A = μ • A := by
  by_cases hpq : p = q
  · subst hpq
    rw [show A = 0 from toMatrixℂ_injective (by rw [hA, sub_self, map_zero]), map_zero, smul_zero]
  set s : ℂ := (((√2)⁻¹ : ℝ) : ℂ)
  have hs : s ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt zero_le_two]
    push_cast
    ring
  set U : Matrix (Fin n) (Fin n) ℂ := 1 - single p p 1 - single q q 1 +
    s • (single p p 1 + single p q 1 + single q p 1 - single q q 1) with hU
  have hUs : star U = U := by
    simp only [hU, star_eq_conjTranspose, conjTranspose_add, conjTranspose_sub,
      conjTranspose_smul, conjTranspose_one, conjTranspose_single, star_one, s,
      Complex.star_def, Complex.conj_ofReal]
    module
  have hUU : U * U = 1 ∧ U * (single p p 1 - single q q 1) * U = single p q 1 + single q p 1 := by
    constructor <;>
    simp only [hU, mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.zero_mul, single_mul_single_same, single_mul_single_of_ne _ _ _ _ hpq,
      single_mul_single_of_ne _ _ _ _ (Ne.symm hpq), mul_one] <;>
    match_scalars <;> first | ring1 | linear_combination 2 * hs
  obtain ⟨g, hg⟩ := exists_toMatrixℂ_adjointℂ_eq_unitary
    ⟨U, mem_unitaryGroup_iff.2 (by rw [hUs, hUU.1])⟩
  have hgA : (toMatrixℂ (adjointℂ g A)).diag = 0 := by
    rw [hg]
    change (U * toMatrixℂ A * star U).diag = 0
    rw [hA, hUs, hUU.2]
    funext x
    simp only [diag_apply, Matrix.add_apply, single_apply, Pi.zero_apply]
    split_ifs <;> simp_all
  rw [← Representation.inv_self_apply adjointℂ g A, ← LinearMap.comp_apply T, hT,
    LinearMap.comp_apply, hμ _ hgA, map_smul, Representation.inv_self_apply]

/-- An endomorphism of the complexification commuting with the adjoint action is a scalar: the
  complex adjoint representation satisfies Schur's lemma. -/
lemma end_eq_smul_id_of_commute_adjointℂ {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) : ∃ μ : ℂ, T = μ • LinearMap.id := by
  obtain ⟨μ, hμ⟩ := end_eq_smul_of_toMatrixℂ_diag_eq_zero hT
  refine ⟨μ, LinearMap.ext fun A => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact toMatrixℂ_injective (Matrix.ext fun x => x.elim0)
  -- `A` is an element with zero diagonal plus a combination of the elements `E_pp - E_ii`
  obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have htr (p : Fin n) : (single p p (1 : ℂ) - single i i 1).trace = 0 := by
    rw [trace_sub, trace_single_eq_same, trace_single_eq_same, sub_self]
  have hdiag : (toMatrixℂ (A - ∑ p, toMatrixℂ A p p • ofTracelessℂ _ (htr p))).diag = 0 := by
    funext x
    simp only [map_sub, map_sum, map_smul, toMatrixℂ_ofTracelessℂ, diag_apply, Matrix.sub_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    rw [show ∑ p, toMatrixℂ A p p = (toMatrixℂ A).trace from rfl, trace_toMatrixℂ]
    simp [single_apply]
  rw [← sub_add_cancel A (∑ p, toMatrixℂ A p p • ofTracelessℂ _ (htr p)), map_add, hμ _ hdiag,
    map_sum, smul_add, Finset.smul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
  rw [map_smul, end_eq_smul_of_toMatrixℂ_eq_single_sub_single hT hμ (toMatrixℂ_ofTracelessℂ _ _),
    smul_comm]


/-- Every bilinear form on the complexification is the contraction against an endomorphism,
  the contraction being nondegenerate. -/
lemma exists_eq_adjointℂContr_tmul {n : ℕ}
    (B : Complexification n ⊗[ℂ] Complexification n →ₗ[ℂ] ℂ) :
    ∃ T : Module.End ℂ (Complexification n), ∀ A C, B (A ⊗ₜ C) = adjointℂContr (T A ⊗ₜ C) :=
  ⟨(LinearMap.BilinForm.toDual _ adjointℂContr_nondegenerate).symm.toLinearMap ∘ₗ curry B,
    fun A C => (LinearMap.BilinForm.apply_toDual_symm_apply
      (hB := adjointℂContr_nondegenerate) (curry B A) C).symm⟩

/-- The endomorphism representing an invariant bilinear form commutes with the adjoint
  action. -/
lemma adjointℂ_comp_eq_of_adjointℂContr_tmul {n : ℕ}
    (B : ((adjointℂ (n := n)).tprod adjointℂ).IntertwiningMap
      (Representation.trivial ℂ (specialUnitaryGroup (Fin n) ℂ) ℂ))
    {T : Module.End ℂ (Complexification n)} (hT : ∀ A C, B (A ⊗ₜ C) = adjointℂContr (T A ⊗ₜ C))
    (g : specialUnitaryGroup (Fin n) ℂ) :
    T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T := by
  have hB (A C : Complexification n) : B (adjointℂ g A ⊗ₜ adjointℂ g C) = B (A ⊗ₜ C) := by
    simpa only [Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply] using Representation.IntertwiningMap.isIntertwining _ _ B g
        (A ⊗ₜ C)
  refine LinearMap.ext fun A => sub_eq_zero.1 (adjointℂContr_separating_left _ fun C => ?_)
  rw [sub_tmul, map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, ← hT,
    ← Representation.self_inv_apply adjointℂ g C, hB, hT, adjointℂContr_adjointℂ]

/-- Every intertwiner `adj ⊗ adj → ℂ` is a multiple of the contraction: up to scale, the
  contraction is the unique `SU(n)`-invariant bilinear form on the complexification. -/
lemma intertwiningMap_eq_smul_adjointℂContr {n : ℕ}
    (B : ((adjointℂ (n := n)).tprod adjointℂ).IntertwiningMap
      (Representation.trivial ℂ (specialUnitaryGroup (Fin n) ℂ) ℂ)) :
    ∃ z : ℂ, B = z • adjointℂContr := by
  obtain ⟨T, hT⟩ := exists_eq_adjointℂContr_tmul B.toLinearMap
  obtain ⟨μ, hμ⟩ :=
    end_eq_smul_id_of_commute_adjointℂ (adjointℂ_comp_eq_of_adjointℂContr_tmul B hT)
  refine ⟨μ, Representation.IntertwiningMap.ext (TensorProduct.ext' fun A C => ?_)⟩
  rw [hT, hμ, LinearMap.smul_apply, LinearMap.id_apply, ← smul_tmul', map_smul]
  rfl

end SULieAlgebra
