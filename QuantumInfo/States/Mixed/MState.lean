/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/
module

public import QuantumInfo.ForMathlib.ContinuousLinearMap
public import QuantumInfo.ForMathlib.ComplexLaplaceTransform
public import QuantumInfo.ForMathlib.ContinuousSup
public import QuantumInfo.ForMathlib.Filter
public import QuantumInfo.ForMathlib.HermitianMat
public import QuantumInfo.ForMathlib.HermitianOp
public import QuantumInfo.ForMathlib.Isometry
public import QuantumInfo.ForMathlib.LinearEquiv
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.Minimax
public import QuantumInfo.ForMathlib.Misc
public import QuantumInfo.ForMathlib.PartialTrace
public import QuantumInfo.ForMathlib.StdBasis
public import QuantumInfo.ForMathlib.Unitary
public import QuantumInfo.ClassicalInfo.Distribution
public import QuantumInfo.States.Pure.Braket

public import Mathlib.Logic.Equiv.Basic

/-!
Finite dimensional quantum mixed states, ρ.

A state is stored basis-freely, as a positive unit-trace operator on a finite dimensional Hilbert
space: this is `DensityOp E`. A preferred orthonormal basis -- a `StdBasis ℂ E ι` instance -- turns
that operator into a density *matrix* `ρ.M : HermitianMat ι ℂ`, and every matrix-level fact below
is derived from an operator-level one through `HermitianOp.toMat`. The abbreviation `MState d` is
`DensityOp (EuclideanSpace ℂ d)`, whose preferred basis is the computational one; it carries the
"classical" interpretation of the diagonal entries as a probability distribution over `d`.

Important definitions:
 * `instMixable`: the `Mixable` instance allowing convex combinations of `MState`s
 * `ofClassical`: Mixed states representing classical distributions
 * `purity`: The purity `Tr[ρ^2]` of a state
 * `spectrum`: The spectrum of the matrix
 * `uniform`: The maximally mixed state
 * `mix`: The total state corresponding to an ensemble
 * `average`: Averages a function over an ensemble, with appropriate weights
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open BigOperators
open ComplexConjugate
open HermitianMat
open scoped Matrix ComplexOrder

/-- A **mixed quantum state** on a finite-dimensional Hilbert space: a positive operator of unit
trace.

The state is stored as an *operator* so that it does not depend on a choice of basis. Given a
preferred orthonormal basis -- that is, a `StdBasis ℂ E ι` instance -- `DensityOp.M` is the density
*matrix*, and the matrix-level facts below are all derived from the operator-level ones through
`HermitianOp.toMat`. -/
structure DensityOp (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] where
  /-- The density operator. -/
  op : HermitianOp E
  /-- A density operator is positive semidefinite. -/
  op_nonneg : 0 ≤ op
  /-- A density operator has unit trace. -/
  op_trace : op.trace = 1

/-- A **mixed quantum state** on a system whose preferred basis is indexed by `d`.

This is `DensityOp` on `EuclideanSpace ℂ d`, so `ρ.M : HermitianMat d ℂ` is the density matrix in
the computational basis. -/
abbrev MState (d : Type*) [Fintype d] [DecidableEq d] : Type _ :=
  DensityOp (EuclideanSpace ℂ d)

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]

variable (ψ φ : Ket d)
variable (ρ σ : MState d)

namespace DensityOp

section Operator

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]

/-- The **density matrix** of a state, in the preferred basis. -/
@[coe] def M (ρ : DensityOp E) : HermitianMat ι ℂ :=
  ρ.op.toMat

@[simp]
theorem toMat_op (ρ : DensityOp E) : ρ.op.toMat = (M ρ : HermitianMat ι ℂ) :=
  rfl

theorem nonneg (ρ : DensityOp E) : 0 ≤ (M ρ : HermitianMat ι ℂ) := by
  rw [M, ← HermitianOp.toMat_zero (E := E) (ι := ι), HermitianOp.toMat_le_toMat]
  exact ρ.op_nonneg

@[simp]
theorem tr (ρ : DensityOp E) : (M ρ : HermitianMat ι ℂ).trace = 1 := by
  rw [M, HermitianOp.trace_toMat]
  exact ρ.op_trace

/-- Build a state from its density matrix in the preferred basis. -/
def ofMat (A : HermitianMat ι ℂ) (h₁ : 0 ≤ A) (h₂ : A.trace = 1) : DensityOp E where
  op := HermitianOp.ofMat A
  op_nonneg := by
    rw [← HermitianOp.toMat_le_toMat (ι := ι)]
    simpa using h₁
  op_trace := by
    rw [← HermitianOp.trace_toMat (ι := ι)]
    simpa using h₂

@[simp]
theorem M_ofMat (A : HermitianMat ι ℂ) (h₁ : 0 ≤ A) (h₂ : A.trace = 1) :
    (M (ofMat (E := E) A h₁ h₂) : HermitianMat ι ℂ) = A := by
  simp [M, ofMat]

/-- Two states with the same density operator are equal. -/
theorem ext_op {ρ σ : DensityOp E} (h : ρ.op = σ.op) : ρ = σ := by
  cases ρ; cases σ; simp_all

/-- Two states with the same density matrix are equal. -/
@[ext] theorem ext {ρ σ : DensityOp E} (h : (M ρ : HermitianMat ι ℂ) = M σ) : ρ = σ :=
  ext_op (HermitianOp.toMat_injective (ι := ι) h)

@[simp]
theorem ofMat_M (ρ : DensityOp E) :
    ofMat (M ρ : HermitianMat ι ℂ) ρ.nonneg ρ.tr = ρ :=
  DensityOp.ext (by simp)

/-- The underlying `Matrix` of a state. Prefer `DensityOp.M` for the `HermitianMat`. -/
def m (ρ : DensityOp E) : Matrix ι ι ℂ := (M ρ : HermitianMat ι ℂ).mat

@[simp]
theorem mat_M (ρ : DensityOp E) : (M ρ : HermitianMat ι ℂ).mat = m ρ := by
  rfl

@[simp]
theorem m_ofMat (A : HermitianMat ι ℂ) (h₁ : 0 ≤ A) (h₂ : A.trace = 1) :
    (m (ofMat (E := E) A h₁ h₂) : Matrix ι ι ℂ) = A.mat := by
  rw [← mat_M, M_ofMat]

theorem pos (ρ : DensityOp E) : 0 < (M ρ : HermitianMat ι ℂ) := by
  refine (nonneg ρ).lt_of_ne' fun h ↦ ?_
  have h₁ : (M ρ : HermitianMat ι ℂ).trace = 1 := tr ρ
  rw [h] at h₁
  simp at h₁

theorem psd (ρ : DensityOp E) : (m ρ : Matrix ι ι ℂ).PosSemidef :=
  HermitianMat.zero_le_iff.mp ρ.nonneg

/-- Every mixed state is Hermitian. -/
theorem Hermitian (ρ : DensityOp E) : (m ρ : Matrix ι ι ℂ).IsHermitian :=
  (M ρ : HermitianMat ι ℂ).H

@[simp]
theorem tr' (ρ : DensityOp E) : (m ρ : Matrix ι ι ℂ).trace = 1 := by
  rw [← mat_M, ← HermitianMat.trace_eq_trace_rc, ρ.tr]
  simp

theorem ext_m {ρ₁ ρ₂ : DensityOp E} (h : (m ρ₁ : Matrix ι ι ℂ) = m ρ₂) : ρ₁ = ρ₂ :=
  DensityOp.ext (HermitianMat.ext h)

/-- The map from mixed states to their matrices is injective -/
theorem m_inj : Function.Injective (m (E := E) (ι := ι)) :=
  fun _ _ h ↦ ext_m h

theorem M_Injective : Function.Injective (M (E := E) (ι := ι)) :=
  fun _ _ h ↦ DensityOp.ext h

-- Could have used properties of ρ.spectrum
theorem eigenvalue_nonneg (ρ : DensityOp E) : ∀ i, 0 ≤ (ρ.Hermitian (ι := ι)).eigenvalues i := by
  rw [← Matrix.PosSemidef.nonneg_iff_eigenvalue_nonneg (ρ.Hermitian (ι := ι))]
  exact ρ.nonneg

-- Could have used properties of ρ.spectrum
theorem eigenvalue_le_one (ρ : DensityOp E) : ∀ i, (ρ.Hermitian (ι := ι)).eigenvalues i ≤ 1 := by
  intro i
  have h := Finset.single_le_sum (f := (M ρ : HermitianMat ι ℂ).H.eigenvalues)
    (fun y _ ↦ (ρ.psd (ι := ι)).eigenvalues_nonneg y) (Finset.mem_univ i)
  rwa [(M ρ : HermitianMat ι ℂ).sum_eigenvalues_eq_trace, ρ.tr] at h

theorem le_one (ρ : DensityOp E) : (M ρ : HermitianMat ι ℂ) ≤ 1 := by
  open MatrixOrder in
  suffices h : (m ρ : Matrix ι ι ℂ) ≤ (1 : ℝ) • 1 by
    rw [one_smul] at h
    exact h
  rw [← Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff (ρ.Hermitian (ι := ι))]
  exact eigenvalue_le_one ρ

end Operator

section PartialTrace

/-! ### Partial traces

The reduced states of a state on a tensor product. These are the basis-free versions; the
`MState`-level partial traces on a product index type are `MState.traceLeft` and
`MState.traceRight`, and the two agree through `DensityOp.traceLeft_M`. -/

open scoped TensorProduct

variable {E F ι κ : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

section Left

/-- The **partial trace** of a state over the left factor: the reduced state on `F`. -/
def traceLeft (ρ : DensityOp (E ⊗[ℂ] F)) : DensityOp F where
  op := ρ.op.traceLeft
  op_nonneg := HermitianOp.traceLeft_nonneg _ ρ.op_nonneg
  op_trace := by rw [HermitianOp.trace_traceLeft, ρ.op_trace]

@[simp]
theorem op_traceLeft (ρ : DensityOp (E ⊗[ℂ] F)) : ρ.traceLeft.op = ρ.op.traceLeft :=
  rfl

/-- **Matrix analogue of `DensityOp.traceLeft`.** -/
@[simp]
theorem traceLeft_M [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]
    [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ] (ρ : DensityOp (E ⊗[ℂ] F)) :
    (M ρ.traceLeft : HermitianMat κ ℂ) = (M ρ : HermitianMat (ι × κ) ℂ).traceLeft := by
  rw [M, M, op_traceLeft, HermitianOp.toMat_traceLeft (ι := ι)]

end Left

section Right

/-- The **partial trace** of a state over the right factor: the reduced state on `E`. -/
def traceRight (ρ : DensityOp (E ⊗[ℂ] F)) : DensityOp E where
  op := ρ.op.traceRight
  op_nonneg := HermitianOp.traceRight_nonneg _ ρ.op_nonneg
  op_trace := by rw [HermitianOp.trace_traceRight, ρ.op_trace]

@[simp]
theorem op_traceRight (ρ : DensityOp (E ⊗[ℂ] F)) : ρ.traceRight.op = ρ.op.traceRight :=
  rfl

/-- **Matrix analogue of `DensityOp.traceRight`.** -/
@[simp]
theorem traceRight_M [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]
    [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ] (ρ : DensityOp (E ⊗[ℂ] F)) :
    (M ρ.traceRight : HermitianMat ι ℂ) = (M ρ : HermitianMat (ι × κ) ℂ).traceRight := by
  rw [M, M, op_traceRight, HermitianOp.toMat_traceRight (κ := κ)]

end Right

end PartialTrace

section Congr

/-! ### Transport along an isometry

A linear isometry equivalence `E ≃ₗᵢ[ℂ] F` carries states on `E` to states on `F`. The case of
interest is `StdBasis.equiv`, which identifies two spaces whose preferred bases share an index
type; along it the density matrix is literally unchanged, which is what lets a state on
`EuclideanSpace ℂ (d₁ × d₂)` be read as a state on a tensor product. -/

variable {E F ι : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Transport a state along a linear isometry equivalence. -/
def congr (ρ : DensityOp E) (e : E ≃ₗᵢ[ℂ] F) : DensityOp F where
  op := ρ.op.congr e
  op_nonneg := HermitianOp.congr_nonneg ρ.op_nonneg e
  op_trace := by rw [HermitianOp.trace_congr, ρ.op_trace]

@[simp]
theorem op_congr (ρ : DensityOp E) (e : E ≃ₗᵢ[ℂ] F) : (ρ.congr e).op = ρ.op.congr e :=
  rfl

@[simp]
theorem congr_congr_symm (ρ : DensityOp E) (e : E ≃ₗᵢ[ℂ] F) : (ρ.congr e).congr e.symm = ρ := by
  refine ext_op (HermitianOp.ext ?_)
  rw [op_congr, op_congr, HermitianOp.op_congr, HermitianOp.op_congr,
    ← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.symm_apply_apply]

@[simp]
theorem congr_symm_congr (ρ : DensityOp F) (e : E ≃ₗᵢ[ℂ] F) : (ρ.congr e.symm).congr e = ρ := by
  simpa using congr_congr_symm ρ e.symm

/-- **Matrix analogue of `DensityOp.congr`** along `StdBasis.equiv`: the density matrix is
unchanged. -/
@[simp]
theorem M_congr [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [StdBasis ℂ F ι] (ρ : DensityOp E) :
    (M (ρ.congr (StdBasis.equiv ℂ E F ι)) : HermitianMat ι ℂ) = (M ρ : HermitianMat ι ℂ) := by
  rw [M, M, op_congr, HermitianOp.toMat_congr_equiv]

/-- **Matrix analogue of `DensityOp.congr`** along an isometry that carries the preferred basis of
`E` to that of `F` up to a relabelling `σ` of the index: the density matrix is relabelled along
`σ`. -/
theorem M_congr_of_stdBasis {κ : Type*} [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [Fintype κ]
    [DecidableEq κ] [StdBasis ℂ F κ] (ρ : DensityOp E) (e : E ≃ₗᵢ[ℂ] F) (σ : ι ≃ κ)
    (he : ∀ i, e (stdBasis (𝕜 := ℂ) (E := E) i) = stdBasis (𝕜 := ℂ) (E := F) (σ i)) :
    (M (ρ.congr e) : HermitianMat κ ℂ) = (M ρ : HermitianMat ι ℂ).reindex σ := by
  rw [M, M, op_congr, HermitianOp.toMat_congr_of_stdBasis _ e σ he]

variable (F) in
/-- Read a state on `E` as a state on any other space whose preferred basis has the same index
type, by matching up the two preferred bases. The density matrix is unchanged: `M_transport`. -/
noncomputable def transport [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [StdBasis ℂ F ι]
    (ρ : DensityOp E) : DensityOp F :=
  ρ.congr (StdBasis.equiv ℂ E F ι)

/-- **Matrix analogue of `DensityOp.transport`**: the density matrix is unchanged. -/
@[simp]
theorem M_transport [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [StdBasis ℂ F ι]
    (ρ : DensityOp E) : (M (ρ.transport F) : HermitianMat ι ℂ) = (M ρ : HermitianMat ι ℂ) :=
  M_congr ρ

@[simp]
theorem transport_self [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] (ρ : DensityOp E) :
    ρ.transport E = ρ :=
  DensityOp.ext (M_transport ρ)

@[simp]
theorem transport_transport [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [StdBasis ℂ F ι]
    (ρ : DensityOp E) : (ρ.transport F).transport E = ρ :=
  DensityOp.ext (by rw [M_transport, M_transport])

/-- Every state is the transport of a state on the Euclidean space with the same index type. Used
to reduce a basis-free statement to its index-level counterpart: `obtain ⟨μ, rfl⟩ :=
ρ.exists_transport_eq` replaces `ρ` by `μ.transport _` throughout. -/
theorem exists_transport_eq [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] (ρ : DensityOp E) :
    ∃ μ : MState ι, μ.transport E = ρ :=
  ⟨ρ.transport _, transport_transport ρ⟩

end Congr

end DensityOp

namespace MState

open DensityOp

instance instCoe : Coe (MState d) (HermitianMat d ℂ) := ⟨DensityOp.M⟩

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `DensityOp.M`: it is always positive (`0 < ρ.M`). -/
@[positivity DensityOp.M _]
meta def evalMStateM : PositivityExt where eval {_u _α} _zα pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    let .const _ lvls := e.getAppFn | throwError "not an application of DensityOp.M"
    pure (.positive (mkAppN (.const ``DensityOp.pos lvls) e.getAppArgs))

--TODO: There should be a bunch of places where we can use `positivity` to prove things,
-- that are currently proved manually.
example (ρ : MState d) : 0 < ρ.M := by positivity

variable (d) in
/-- The matrices corresponding to MStates are `Convex ℝ` -/
theorem convex :
    Convex ℝ (Set.range (DensityOp.M (E := EuclideanSpace ℂ d) (ι := d))) := by
  simp only [Convex, Set.mem_range, StarConvex,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro x y a b ha hb hab
  replace hab : a + b = (1 : ℂ) := by norm_cast
  have := HermitianMat.convex_cone x.nonneg y.nonneg ha hb
  exact ⟨DensityOp.ofMat _ this (by simpa using mod_cast hab), by simp⟩

instance instMixable : Mixable (HermitianMat d ℂ) (MState d) where
  to_U := DensityOp.M
  to_U_inj := DensityOp.ext
  mkT {u} := fun h ↦
    ⟨DensityOp.ofMat u (h.casesOn fun t ht ↦ ht ▸ t.nonneg)
      (h.casesOn fun t ht ↦ ht ▸ t.tr), by simp⟩
  convex := convex d

/-- Mixing states mixes their density matrices. -/
@[simp]
theorem mix_M (p : Prob) (ρ σ : MState d) :
    (p [ρ ↔ σ]).M = (p : ℝ) • ρ.M + (1 - (p : ℝ)) • σ.M := by
  have h : Mixable.to_U (p [ρ ↔ σ] : MState d)
      = (p : ℝ) • Mixable.to_U ρ + ((1 - p : Prob) : ℝ) • Mixable.to_U σ :=
    (Mixable.mkT _).2
  have hU (τ : MState d) : Mixable.to_U τ = τ.M := rfl
  simpa [hU] using h

@[simp]
theorem mix_m (p : Prob) (ρ σ : MState d) :
    (p [ρ ↔ σ]).m = (p : ℝ) • ρ.m + (1 - (p : ℝ)) • σ.m := by
  rw [← mat_M, mix_M]
  simp

--An MState is a witness that d is nonempty.
include ρ in
theorem nonempty : Nonempty d := by
  by_contra h
  simpa [HermitianMat.trace_eq_re_trace, not_nonempty_iff.mp h] using ρ.tr


open scoped RealInnerProductSpace InnerProductSpace

/-- The inner product of two MState's, as a real number between 0 and 1. -/
scoped instance : Inner Prob (MState d) where
  inner := fun ρ σ ↦ ⟨⟪ρ.M, σ.M⟫,
    inner_ge_zero ρ.nonneg σ.nonneg,
    (inner_le_mul_trace ρ.nonneg σ.nonneg).trans (by simp)⟩

theorem inner_def : ⟪ρ, σ⟫_Prob = ⟨⟪ρ.M, σ.M⟫,
    inner_ge_zero ρ.nonneg σ.nonneg,
    (inner_le_mul_trace ρ.nonneg σ.nonneg).trans (by simp)⟩ := by
  rfl

theorem val_inner : (⟪ρ, σ⟫_Prob : ℝ) = ⟪ρ.M, σ.M⟫ := by
  rfl

section exp_val

def exp_val_ℂ (T : Matrix d d ℂ) : ℂ :=
  (T * ρ.m).trace

--TODO: Bundle as a ContinuousLinearMap.
/-- The **expectation value** of an operator on a quantum state. -/
def exp_val (T : HermitianMat d ℂ) : ℝ :=
  ⟪ρ.M, T⟫

theorem exp_val_nonneg {T : HermitianMat d ℂ} (h : 0 ≤ T) : 0 ≤ ρ.exp_val T :=
  inner_ge_zero ρ.nonneg h

--TODO: Positivity extension for `MState.exp_val`. (Use the `inner` extension that we need
-- to write first.)

@[simp]
theorem exp_val_zero : ρ.exp_val 0 = 0 := by
  simp [MState.exp_val]

@[simp]
theorem exp_val_one : ρ.exp_val 1 = 1 := by
  simp [MState.exp_val]

theorem exp_val_le_one {T : HermitianMat d ℂ} (h : T ≤ 1) : ρ.exp_val T ≤ 1 := by
  have hmono := inner_mono ρ.nonneg h
  rwa [inner_one ρ.M, ρ.tr] at hmono

theorem exp_val_prob {T : HermitianMat d ℂ} (h : 0 ≤ T ∧ T ≤ 1) :
    0 ≤ ρ.exp_val T ∧ ρ.exp_val T ≤ 1 :=
  ⟨ρ.exp_val_nonneg h.1, ρ.exp_val_le_one h.2⟩

theorem exp_val_sub (A B : HermitianMat d ℂ) :
    ρ.exp_val (A - B) = ρ.exp_val A - ρ.exp_val B := by
  simp [exp_val, inner_sub_right]

/-- If a PSD observable `A` has expectation value of 0 on a state `ρ`, it must entirely contain the
support of `ρ` in its kernel. -/
theorem exp_val_eq_zero_iff {A : HermitianMat d ℂ} (hA₁ : 0 ≤ A) :
    ρ.exp_val A = 0 ↔ ρ.M.support ≤ A.ker := by
  exact inner_zero_iff ρ.nonneg hA₁

/-- If an observable `A` has expectation value of 1 on a state `ρ`, it must entirely contain the
support of `ρ` in its 1-eigenspace. -/
theorem exp_val_eq_one_iff {A : HermitianMat d ℂ} (hA₂ : A ≤ 1) :
    ρ.exp_val A = 1 ↔ ρ.M.support ≤ (1 - A).ker := by
  rw [← exp_val_eq_zero_iff ρ (A := 1 - A) (HermitianMat.zero_le_iff.mpr hA₂)]
  rw [exp_val_sub, exp_val_one]
  rw [sub_eq_zero, eq_comm]

theorem exp_val_add (A B : HermitianMat d ℂ) :
    ρ.exp_val (A + B) = ρ.exp_val A + ρ.exp_val B := by
  simp [exp_val, inner_add_right]

@[simp]
theorem exp_val_smul (r : ℝ) (A : HermitianMat d ℂ) :
    ρ.exp_val (r • A) = r * ρ.exp_val A := by
  simp [MState.exp_val]

@[gcongr]
theorem exp_val_le_exp_val (ρ : MState d) {A B : HermitianMat d ℂ} (h : A ≤ B) :
    ρ.exp_val A ≤ ρ.exp_val B := by
  simp only [MState.exp_val]
  refine inner_mono ρ.nonneg h

end exp_val

section pure

/-- A mixed state can be constructed as a pure state arising from a ket. -/
def pure (ψ : Ket d) : MState d :=
  DensityOp.ofMat ⟨Matrix.vecMulVec ψ (ψ : Bra d), (Matrix.PosSemidef.outer_self_conj ψ).1⟩
    (HermitianMat.zero_le_iff.mpr (.outer_self_conj ψ))
    (by
      have h₁ (x : d) : (Matrix.vecMulVec (ψ : d → ℂ) ((ψ : Bra d) : d → ℂ)).diag x
          = (Complex.normSq (ψ x) : ℂ) := by
        rw [Matrix.diag_apply, Matrix.vecMulVec_apply, Bra.eq_conj, mul_comm,
          Complex.normSq_eq_conj_mul_self]
      rw [HermitianMat.trace_eq_re_trace, HermitianMat.mat_mk, Matrix.trace]
      simp_rw [h₁]
      rw [← Complex.ofReal_sum]
      simpa using ψ.normalized)

@[simp]
theorem pure_M (ψ : Ket d) :
    (pure ψ).M = ⟨Matrix.vecMulVec ψ (ψ : Bra d), (Matrix.PosSemidef.outer_self_conj ψ).1⟩ := by
  rw [pure, M_ofMat]

/-- The overlap of two pure states is the squared magnitude of their bracket. -/
theorem pure_inner : ⟪pure ψ, pure φ⟫_Prob = ‖Braket.dot ψ φ‖^2 := by
  simp [MState.inner_def, HermitianMat.inner_def, pure_M, Matrix.vecMulVec_mul_vecMulVec,
    Braket.dot_eq_dotProduct, Matrix.trace_smul]
  rw [show ((ψ : d → ℂ) ⬝ᵥ ((φ : Bra d) : d → ℂ)) =
      conj (((ψ : Bra d) : d → ℂ) ⬝ᵥ (φ : d → ℂ)) from by
    change (ψ : d → ℂ) ⬝ᵥ star (φ : d → ℂ) =
      conj (((ψ : Bra d) : d → ℂ) ⬝ᵥ (φ : d → ℂ))
    rw [Matrix.dotProduct_star (ψ : d → ℂ) (φ : d → ℂ)]
    congr 1
    exact dotProduct_comm (φ : d → ℂ) (star (ψ : d → ℂ))]
  simpa [Complex.normSq_apply] using
    Complex.normSq_eq_norm_sq (((ψ : Bra d) : d → ℂ) ⬝ᵥ (φ : d → ℂ))

@[simp]
theorem pure_apply {i j : d} : (pure ψ).m i j = (ψ i) * conj (ψ j) := by
  rw [← mat_M, pure_M, mat_mk]
  simp [Matrix.vecMulVec_apply, Bra.eq_conj]

@[simp]
theorem pure_M_apply {i j : d} : (pure ψ).M i j = (ψ i) * conj (ψ j) := by
  rw [← mat_apply, mat_M, pure_apply]

theorem pure_mul_self : (pure ψ).m * (pure ψ).m = (pure ψ : Matrix d d ℂ) := by
  rw [show ((pure ψ : Matrix d d ℂ)) = (pure ψ).m from rfl, ← mat_M, pure_M]
  simp [Matrix.vecMulVec_mul_vecMulVec, ← Braket.dot_eq_dotProduct]

/-- Sandwiching a state between two copies of the projector `∣ψ⟩⟨ψ∣` gives that projector back,
scaled by the expectation value `⟨ψ∣σ∣ψ⟩`. -/
theorem conj_pure : σ.M.conj (pure ψ).M.mat = (σ.exp_val (pure ψ).M) • (pure ψ).M := by
  set u : d → ℂ := fun i ↦ ψ i with hu
  set v : d → ℂ := fun i ↦ conj (ψ i) with hv
  have hmat : (pure ψ).m = Matrix.vecMulVec u v := by
    rw [← mat_M, pure_M, HermitianMat.mat_mk]
    ext i j
    simp [Matrix.vecMulVec_apply, Bra.eq_conj, hu, hv]
  have hsc : ((σ.exp_val (pure ψ).M : ℝ) : ℂ) = (v ᵥ* σ.m) ⬝ᵥ u := by
    rw [← RCLike.ofReal_eq_complex_ofReal, exp_val, HermitianMat.inner_eq_trace_rc,
      mat_M, mat_M, hmat, Matrix.mul_vecMulVec, ← Matrix.dotProduct_mulVec, dotProduct_comm]
    rfl
  ext1
  rw [HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat, HermitianMat.mat_smul]
  simp only [mat_M, hmat]
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, ← hsc]
  ext i j
  simp [Complex.real_smul]

/-- The projectors onto the standard basis states sum to the identity. -/
theorem sum_pure_basis : ∑ i : d, (pure (Ket.basis i)).M = 1 := by
  ext1
  rw [show (∑ i : d, (pure (Ket.basis i)).M).mat = ∑ i : d, ((pure (Ket.basis i)).M).mat from
    map_sum (HermitianMat.matₗ (R := ℝ)) _ _]
  ext i j
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Bra.eq_conj, Ket.basis, Ket.apply,
    Matrix.one_apply, apply_ite, eq_comm]

/-- The purity of a state is Tr[ρ^2]. This is a `Prob`, because it is always
between zero and one. -/
def purity (ρ : MState d) : Prob := ⟪ρ, ρ⟫_Prob

/-- The eigenvalue spectrum of a mixed quantum state, as a `Distribution`. -/
def spectrum (ρ : MState d) : ProbDistribution d :=
  ProbDistribution.mk'
    (ρ.M.H.eigenvalues ·)
    (ρ.psd.eigenvalues_nonneg ·)
    (by rw [sum_eigenvalues_eq_trace, ρ.tr])

/-- The spectrum of a pure state is (1,0,0,...), i.e. a constant distribution. -/
theorem spectrum_pure_eq_constant :
    ∃ i, (pure ψ).spectrum = ProbDistribution.constant i := by
  let ρ := pure ψ
  -- Prove 1 is in the spectrum of pure ψ by exhibiting an eigenvector with value 1.
  have : ∃i, (pure ψ).spectrum i = 1 := by
    simp [spectrum, ProbDistribution.mk']
    have hEig : ∃i, (pure ψ).M.H.eigenvalues i = 1 := by
      -- Prove ψ is an eigenvector of ρ = pure ψ
      have hv : ρ.M *ᵥ ψ = ψ := by
        ext
        simp_rw [ρ, pure_M, Matrix.mulVec, mat_mk, Matrix.vecMulVec_apply, dotProduct,
        Bra.apply', Ket.apply, mul_assoc, ← Finset.mul_sum, ← Complex.normSq_eq_conj_mul_self,
        ← Complex.ofReal_sum, ← Ket.apply, ψ.normalized, Complex.ofReal_one, mul_one]
      let U : Matrix.unitaryGroup d ℂ := star ρ.M.H.eigenvectorUnitary -- Diagonalizing unitary of ρ
      let w : d → ℂ := U *ᵥ ψ
      -- Prove w = U ψ is an eigenvector of the diagonalized matrix of ρ = pure ψ
      have hDiag : Matrix.diagonal (RCLike.ofReal ∘ ρ.M.H.eigenvalues) *ᵥ w = w := by
        simp_rw [← Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary,
        eq_comm, Unitary.conjStarAlgAut_apply,
        ← Matrix.mulVec_mulVec, w, U, Matrix.mulVec_mulVec] -- Uses spectral theorem
        simp_all
        rw [←Matrix.mulVec_mulVec, hv]
      -- Prove w = U ψ is nonzero by contradiction
      have hwNonZero : ∃j, w j ≠ 0 := by
        by_contra hwZero
        simp at hwZero
        rw [←funext_iff] at hwZero
        -- If w is zero, then ψ is zero, since U is invertible
        have hψZero : ∀x, ψ x = 0 := by
          apply congr_fun
          -- Prove U is invertible
          have hUdetNonZero : (U : Matrix d d ℂ).det ≠ 0 := by
            by_contra hDetZero
            obtain ⟨u, huUni⟩ := U
            have h0uni: 0 ∈ unitary ℂ := by
              rw [←hDetZero]
              simp
              exact Matrix.det_of_mem_unitary huUni
            rw [Unitary.mem_iff] at h0uni
            simp_all
          exact Matrix.eq_zero_of_mulVec_eq_zero hUdetNonZero hwZero
        -- Reach an contradiction that ψ has norm 0
        have hψn := Ket.normalized ψ
        have hnormZero : ∀ x : d, Complex.normSq (ψ x) = 0 := fun x => by
          rw [hψZero x, Complex.normSq_zero]
        have hsumZero : ∑ x : d, Complex.normSq (ψ x) = 0 := by
          apply Finset.sum_eq_zero
          intros x _
          exact hnormZero x
        simp_all
      obtain ⟨j, hwNonZero'⟩ := hwNonZero
      have hDiagj := congr_fun hDiag j
      rw [Matrix.mulVec_diagonal, mul_eq_right₀ hwNonZero'] at hDiagj
      use j
      simpa [ρ] using hDiagj
    obtain ⟨i, hEig'⟩ := hEig
    use i
    ext
    simpa using hEig'
  --If 1 is in a distribution, the distribution is a constant.
  obtain ⟨i, hi⟩ := this
  use i
  exact ProbDistribution.constant_of_exists_one hi

/-- If the spectrum of a mixed state is (1,0,0...) i.e. a constant distribution, it is
 a pure state. -/
theorem pure_of_constant_spectrum (h : ∃ i, ρ.spectrum = ProbDistribution.constant i) :
    ∃ ψ, ρ = pure ψ := by
  obtain ⟨i, h'⟩ := h
  -- Translate assumption to eigenvalues being (1,0,0,...)
  have hEig : ρ.M.H.eigenvalues = fun x => if x = i then 1 else 0 := by
    ext x
    simp [spectrum, ProbDistribution.constant, ProbDistribution.mk'] at h'
    rw [Subtype.mk.injEq] at h'
    have h'x := congr_fun h' x
    rw [if_congr (Eq.comm) (Eq.refl 1) (Eq.refl 0)]
    rw [Prob.ext_iff] at h'x
    dsimp at h'x
    rw [h'x]
    split_ifs
    case pos => rfl
    case neg => rfl
  -- Choose the eigenvector v of ρ with eigenvalue 1 to make ψ
  let ⟨u, huUni⟩ := ρ.M.H.eigenvectorUnitary -- Diagonalizing unitary of ρ
  let D : Matrix d d ℂ := Matrix.diagonal (RCLike.ofReal ∘ ρ.M.H.eigenvalues) -- Diagonal matrix of ρ
  let v : EuclideanSpace ℂ d := ρ.M.H.eigenvectorBasis i
  -- Prove v is normalized
  have hUvNorm : ∑ x, ‖v x‖^2 = 1 := by
    have hinnerv : Inner.inner ℂ v v = 1 := by
      have := ρ.M.H.eigenvectorBasis.orthonormal
      rw [orthonormal_iff_ite] at this
      convert this i i
      simp
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.mul_conj'] at hinnerv
    rw [← Fintype.sum_equiv (Equiv.refl d) _ (fun x => (Complex.ofReal ‖v x‖) ^ 2) (fun x => Complex.ofReal_pow ‖v x‖ 2)] at hinnerv
    rw [← Complex.ofReal_sum Finset.univ (fun x => ‖v x‖ ^ 2), Complex.ofReal_eq_one] at hinnerv
    exact hinnerv
  let ψ : Ket d := ⟨v, hUvNorm⟩ -- Construct ψ
  use ψ
  ext j k
  -- Use spectral theorem to prove that ρ = pure ψ
  rw [Matrix.IsHermitian.spectral_theorem ρ.M.H, Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
  simp [ψ, v, hEig]
  have hsum : ∀ x ∈ Finset.univ, x ∉ ({i} : Finset d) → (ρ.M.H.eigenvectorBasis x j) * (↑(if x = i then 1 else 0) : ℝ) * (starRingEnd ℂ) (ρ.Hermitian.eigenvectorBasis x k) = 0 := by
    intros x hx hxnoti
    rw [Finset.mem_singleton] at hxnoti
    rw [if_neg hxnoti, Complex.ofReal_zero]
    ring
  simp_rw [←Finset.sum_subset (Finset.subset_univ {i}) hsum, Finset.sum_singleton, reduceIte, Complex.ofReal_one, mul_one]
  rfl

/-- A state ρ is pure iff its spectrum is (1,0,0,...) i.e. a constant distribution. -/
theorem pure_iff_constant_spectrum : (∃ ψ, ρ = pure ψ) ↔
    ∃ i, ρ.spectrum = ProbDistribution.constant i :=
  ⟨fun h ↦ h.rec fun ψ h₂ ↦ h₂ ▸ spectrum_pure_eq_constant ψ,
  pure_of_constant_spectrum ρ⟩

theorem pure_iff_purity_one : (∃ ψ, ρ = pure ψ) ↔ ρ.purity = 1 := by
  --purity = exp(-Collision entropy)
  --purity eq 1 iff collision entropy is zero
  --entropy is zero iff distribution is constant
  --distribution is constant iff pure
  constructor <;> intro h;
  · obtain ⟨w, rfl⟩ := h
    have h₁ : ((⟪(pure w).M, (pure w).M⟫ : ℝ) : ℂ) = 1 := by
      rw [← RCLike.ofReal_eq_complex_ofReal, HermitianMat.inner_eq_trace_rc, mat_M, pure_mul_self]
      exact (pure w).tr'
    ext
    show (⟪(pure w).M, (pure w).M⟫ : ℝ) = 1
    exact_mod_cast h₁
  · --TODO Cleanup
    -- Apply the theorem that states a mixed state is pure if and only if its spectrum is constant.
    apply (pure_iff_constant_spectrum ρ).mpr;
    have h_eigenvalues : ∑ i, (ρ.spectrum i).val ^ 2 = 1 := by
      -- By definition of purity, we know that the sum of the squares of the eigenvalues is equal to the trace of ρ squared.
      have h_trace_sq : ∑ i, (ρ.spectrum i).val ^ 2 = (ρ.purity : ℝ) := by
        have h_eig : ((∑ i, ρ.M.H.eigenvalues i ^ 2 : ℝ) : ℂ) = (ρ.M.mat * ρ.M.mat).trace := by
          have := Matrix.IsHermitian.spectral_theorem ρ.M.H
          conv_rhs => rw [this]
          simp [Matrix.trace_mul_comm, Matrix.mul_assoc]
          exact Finset.sum_congr rfl fun _ _ => by ring
        have h_pur : ((ρ.purity : ℝ) : ℂ) = (ρ.M.mat * ρ.M.mat).trace := by
          rw [show (ρ.purity : ℝ) = ⟪ρ.M, ρ.M⟫ from rfl,
            ← RCLike.ofReal_eq_complex_ofReal, HermitianMat.inner_eq_trace_rc]
        have h_sp (i : d) : (ρ.spectrum i).val = ρ.M.H.eigenvalues i := by
          simp [spectrum, ProbDistribution.mk']
        simp only [h_sp]
        exact_mod_cast h_eig.trans h_pur.symm
      simp_all only [Set.Icc.coe_one]
    have h_eigenvalues : ∑ i, (ρ.spectrum i).val * ((ρ.spectrum i).val - 1) = 0 := by
      simp_all [ sq, mul_sub ];
    -- Since each term in the sum is non-positive and their sum is zero, each term must be zero.
    have h_each_zero : ∀ i, (ρ.spectrum i).val * ((ρ.spectrum i).val - 1) = 0 := by
      have h_each_zero : ∀ i, (ρ.spectrum i).val * ((ρ.spectrum i).val - 1) ≤ 0 := by
        exact fun i => by nlinarith only [ show ( ρ.spectrum i : ℝ ) ≥ 0 by exact_mod_cast ( ρ.spectrum i ) |>.2.1, show ( ρ.spectrum i : ℝ ) ≤ 1 by exact_mod_cast ( ρ.spectrum i ) |>.2.2 ] ;
      exact fun i => le_antisymm ( h_each_zero i ) ( by simpa [ h_eigenvalues ] using Finset.single_le_sum ( fun i _ => neg_nonneg.mpr ( h_each_zero i ) ) ( Finset.mem_univ i ) );
    -- Since each term in the sum is non-positive and their sum is zero, each term must be zero. Therefore, for each i, either (ρ.spectrum i).val = 0 or (ρ.spectrum i).val = 1.
    have h_each_zero : ∀ i, (ρ.spectrum i).val = 0 ∨ (ρ.spectrum i).val = 1 := by
      exact fun i => mul_eq_zero.mp ( h_each_zero i ) |> Or.imp id fun h => by linarith;
    have h_sum_one : ∑ i, (ρ.spectrum i).val = 1 := by
      grind;
    obtain ⟨i, hi⟩ : ∃ i, (ρ.spectrum i).val = 1 := by
      contrapose! h_sum_one; aesop;
    -- Since the sum of the eigenvalues is 1 and one of them is 1, the remaining eigenvalues must sum to 0. Given that each eigenvalue is either 0 or 1, the only way their sum can be 0 is if all of them are 0.
    have h_sum_zero : ∑ j ∈ Finset.univ.erase i, (ρ.spectrum j).val = 0 := by
      rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ i ), hi ] at h_sum_one ; linarith;
    rw [ Finset.sum_eq_zero_iff_of_nonneg ] at h_sum_zero
    · simp_all only [Finset.sum_const_zero, mul_eq_zero, Set.Icc.coe_eq_zero, Set.Icc.coe_eq_one,
        ProbDistribution.normalized, Finset.mem_erase, ne_eq, Finset.mem_univ, and_true]
      apply Exists.intro
      · ext x : 2
        simp_all only [ProbDistribution.constant_eq]
        split
        next h_1 =>
          subst h_1
          simp_all only [Set.Icc.coe_one, Set.Icc.coe_eq_one]
          exact hi
        next h_1 =>
          simp_all only [Set.Icc.coe_zero, Set.Icc.coe_eq_zero]
          apply h_sum_zero
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [not_true_eq_false]
    · intro i_1 a
      simp_all only [Finset.sum_const_zero, mul_eq_zero, Set.Icc.coe_eq_zero, Set.Icc.coe_eq_one,
        ProbDistribution.normalized, Finset.mem_univ, Finset.sum_erase_eq_sub, Set.Icc.coe_one, sub_self, Finset.mem_erase,
        ne_eq, and_true, Prob.zero_le_coe]

--TODO: Would be better if there was an `MState.eigenstate` or similar (maybe extending
-- a similar thing for `HermitianMat`) and then this could be an equality with that, as
-- an explicit formula, instead of this `Exists`.
theorem spectralDecomposition (ρ : MState d) :
    ∃ (ψs : d → Ket d), ρ.M = ∑ i, (ρ.spectrum i : ℝ) • (MState.pure (ψs i)).M := by
  use (fun i ↦ ⟨(ρ.M.H.eigenvectorUnitary · i), Matrix.unitaryGroup_row_norm _ i⟩)
  ext i j
  nth_rw 1 [ρ.M.H.spectral_theorem]
  --TODO Cleanup
  simp only [Complex.coe_algebraMap, spectrum, ProbDistribution.mk',
    ProbDistribution.funlike_apply, Matrix.IsHermitian.eigenvectorUnitary_apply]
  rw [HermitianMat.mat_finset_sum]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Finset.sum_apply, Finset.sum_apply, Matrix.mul_apply]
  congr!
  simp only [Matrix.mul_diagonal, Matrix.IsHermitian.eigenvectorUnitary_apply,
    mul_comm, Matrix.star_apply, RCLike.star_def]
  simp only [Function.comp_apply, mat_M, mat_apply, HermitianMat.smul_apply, Complex.real_smul,
    pure_M_apply, Ket.apply]
  ring

end pure

section prod

def prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : MState (d₁ × d₂) :=
  DensityOp.ofMat (ρ₁.M ⊗ₖ ρ₂.M)
    (HermitianMat.zero_le_iff.mpr (ρ₁.psd.PosSemidef_kronecker ρ₂.psd))
    (by simp)

@[simp]
theorem prod_M (ρ₁ : MState d₁) (ρ₂ : MState d₂) : (prod ρ₁ ρ₂).M = ρ₁.M ⊗ₖ ρ₂.M := by
  rw [prod, M_ofMat]

@[simp]
theorem prod_m (ρ₁ : MState d₁) (ρ₂ : MState d₂) :
    (prod ρ₁ ρ₂).m = Matrix.kroneckerMap (· * ·) ρ₁.m ρ₂.m := by
  rw [← mat_M, prod_M, kronecker_mat, mat_M, mat_M]

infixl:100 " ⊗ᴹ " => MState.prod

theorem prod_inner_prod (ξ1 ψ1 : MState d₁) (ξ2 ψ2 : MState d₂) :
    ⟪ξ1 ⊗ᴹ ξ2, ψ1 ⊗ᴹ ψ2⟫_Prob = ⟪ξ1, ψ1⟫_Prob * ⟪ξ2, ψ2⟫_Prob := by
  ext1
  simp only [inner_def, Prob.coe_mul, ← Complex.ofReal_inj]
  --Lots of this should actually be facts about HermitianMat first
  simp only [prod_M, Complex.ofReal_mul]
  simp only [← RCLike.ofReal_eq_complex_ofReal, inner_eq_trace_rc]
  simp only [kronecker, ← Matrix.trace_kronecker]
  simp only [mat_M, mat_mk, Matrix.mul_kronecker_mul]

/-- The product of pure states is a pure product state , `Ket.prod`. -/
theorem pure_prod_pure (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : pure (ψ₁ ⊗ᵠ ψ₂) = (pure ψ₁) ⊗ᴹ (pure ψ₂) := by
  ext : 3
  simp [Ket.prod, Ket.apply, Matrix.vecMulVec_apply, Bra.eq_conj, kronecker_apply]
  ring

end prod

/-- A representation of a classical distribution as a quantum state, diagonal in the given basis. -/
def ofClassical (dist : ProbDistribution d) : MState d :=
  DensityOp.ofMat (diagonal ℂ (fun x ↦ dist x))
    (by simp [zero_le_iff, diagonal, Matrix.posSemidef_diagonal_iff])
    (by simp [trace_diagonal])

@[simp]
theorem coe_ofClassical (dist : ProbDistribution d) :
    (ofClassical dist).M = diagonal ℂ (dist ·) := by
  rw [ofClassical, M_ofMat]

theorem ofClassical_pow (dist : ProbDistribution d) (p : ℝ) :
    (ofClassical dist).M ^ p = diagonal ℂ (fun i ↦ (dist i) ^ p) := by
  rw [coe_ofClassical, diagonal_pow]

/-- The maximally mixed state. -/
def uniform [Nonempty d] : MState d :=
  ofClassical ProbDistribution.uniform

/-- There is exactly one state on a dimension-1 system. -/
--note that this still takes (and uses) the `Fintype d` and `DecidableEq d` instances on `MState d`.
--Even though instances for those can be derived from `Unique d`, we want this `Unique` instance to
--apply on `@MState d ?x ?y` for _any_ x and y.
instance instUnique [Unique d] : Unique (MState d) where
  default := @uniform _ _ _ _
  uniq := by
    intro ρ
    ext
    have h₁ := ρ.tr
    have h₂ := (@uniform _ _ _ _ : MState d).tr
    simp [Matrix.trace, Unique.eq_default, -DensityOp.tr, HermitianMat.trace_eq_re_trace] at h₁ h₂ ⊢
    apply Complex.ext
    · exact h₁.trans h₂.symm
    · rw [complex_im_eq_zero, complex_im_eq_zero]

/-- There exists a mixed state for every nonempty `d`.
Here, the maximally mixed one is chosen. -/
instance instInhabited [Nonempty d] : Inhabited (MState d) where
  default := uniform

lemma default_eq [Nonempty d] : (default : MState d) = uniform := rfl

@[simp]
theorem M_default [Unique d] : (default : MState d).M = 1 := by
  show (uniform : MState d).M = 1
  rw [uniform, coe_ofClassical]
  ext1
  ext i j
  simp [Subsingleton.elim i j]

section ptrace

/-- Partial tracing out the left half of a system. -/
def traceLeft (ρ : MState (d₁ × d₂)) : MState d₂ :=
  DensityOp.ofMat ρ.M.traceLeft (zero_le_iff.mpr ρ.psd.traceLeft) (by simp [trace])

@[simp]
theorem traceLeft_M (ρ : MState (d₁ × d₂)) : (traceLeft ρ).M = ρ.M.traceLeft := by
  rw [traceLeft, M_ofMat]

@[simp]
theorem traceLeft_m (ρ : MState (d₁ × d₂)) : (traceLeft ρ).m = ρ.m.traceLeft := by
  rw [← mat_M, traceLeft_M, traceLeft_mat, mat_M]

/-- Partial tracing out the right half of a system. -/
def traceRight (ρ : MState (d₁ × d₂)) : MState d₁ :=
  DensityOp.ofMat ρ.M.traceRight (zero_le_iff.mpr ρ.psd.traceRight) (by simp [trace])

@[simp]
theorem traceRight_M (ρ : MState (d₁ × d₂)) : (traceRight ρ).M = ρ.M.traceRight := by
  rw [traceRight, M_ofMat]

@[simp]
theorem traceRight_m (ρ : MState (d₁ × d₂)) : (traceRight ρ).m = ρ.m.traceRight := by
  rw [← mat_M, traceRight_M, traceRight_mat, mat_M]

section Tensor

open scoped TensorProduct

/-- A bipartite state, read as a state on an honest tensor product.

`MState (d₁ × d₂)` is a state on `EuclideanSpace ℂ (d₁ × d₂)`, whose preferred basis happens to be
indexed by a product; this transports it along `StdBasis.equiv` to the tensor product of the two
factors, where the basis-free partial traces `DensityOp.traceLeft` and `DensityOp.traceRight`
live. -/
noncomputable def toTensor (ρ : MState (d₁ × d₂)) :
    DensityOp (EuclideanSpace ℂ d₁ ⊗[ℂ] EuclideanSpace ℂ d₂) :=
  ρ.transport _

@[simp]
theorem M_toTensor (ρ : MState (d₁ × d₂)) : (M ρ.toTensor : HermitianMat (d₁ × d₂) ℂ) = ρ.M :=
  DensityOp.M_transport ρ

section Factors

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [StdBasis ℂ E d₁]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [StdBasis ℂ F d₂]

/-- The index-level partial trace is the operator-level one, read through `DensityOp.transport`. -/
@[simp]
theorem traceLeft_transport (ρ : MState (d₁ × d₂)) :
    (ρ.transport (E ⊗[ℂ] F)).traceLeft = ρ.traceLeft.transport F := by
  ext1
  rw [DensityOp.traceLeft_M (ι := d₁), DensityOp.M_transport, DensityOp.M_transport, traceLeft_M]

/-- The index-level partial trace is the operator-level one, read through `DensityOp.transport`. -/
@[simp]
theorem traceRight_transport (ρ : MState (d₁ × d₂)) :
    (ρ.transport (E ⊗[ℂ] F)).traceRight = ρ.traceRight.transport E := by
  ext1
  rw [DensityOp.traceRight_M (κ := d₂), DensityOp.M_transport, DensityOp.M_transport, traceRight_M]

end Factors

/-- The index-level partial trace is the operator-level one, read through `MState.toTensor`. -/
@[simp]
theorem traceLeft_toTensor (ρ : MState (d₁ × d₂)) : ρ.toTensor.traceLeft = ρ.traceLeft := by
  rw [toTensor, traceLeft_transport, DensityOp.transport_self]

/-- The index-level partial trace is the operator-level one, read through `MState.toTensor`. -/
@[simp]
theorem traceRight_toTensor (ρ : MState (d₁ × d₂)) : ρ.toTensor.traceRight = ρ.traceRight := by
  rw [toTensor, traceRight_transport, DensityOp.transport_self]

end Tensor

/-- Taking the direct product on the left and tracing it back out gives the same state. -/
@[simp]
theorem traceLeft_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : (ρ₁ ⊗ᴹ ρ₂).traceLeft = ρ₂ := by
  ext1
  simp [prod]

/-- Taking the direct product on the right and tracing it back out gives the same state. -/
@[simp]
theorem traceRight_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : (ρ₁ ⊗ᴹ ρ₂).traceRight = ρ₁ := by
  ext1
  simp [prod]

end ptrace

-- TODO: direct sum (by zero-padding)

--TODO: Spectra of left- and right- partial traces of a pure state are equal.

/-- Spectrum of direct product. There is a permutation σ so that the spectrum of the direct product of
  ρ₁ and ρ₂, as permuted under σ, is the pairwise products of the spectra of ρ₁ and ρ₂. -/
theorem spectrum_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : ∃(σ : d₁ × d₂ ≃ d₁ × d₂),
    ∀i, ∀j, (ρ₁ ⊗ᴹ ρ₂).spectrum (σ (i, j)) = (ρ₁.spectrum i) * (ρ₂.spectrum j) := by
  --TODO Cleanup
  by_contra! h;
  -- Apply `Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal` to $A \otimes B$ and $U_A \otimes U_B$ and the diagonal entries.
  obtain ⟨σ, hσ⟩ : ∃ σ : d₁ × d₂ ≃ d₁ × d₂, (ρ₁.prod ρ₂).M.H.eigenvalues ∘ σ = fun (i, j) => ((ρ₁.spectrum i) * (ρ₂.spectrum j)) := by
    have h_unitary : ∃ U : Matrix (d₁ × d₂) (d₁ × d₂) ℂ, U ∈ Matrix.unitaryGroup (d₁ × d₂) ℂ ∧ (ρ₁.prod ρ₂).M = U * Matrix.diagonal (fun (i, j) => ((ρ₁.spectrum i) * (ρ₂.spectrum j)) : d₁ × d₂ → ℂ) * Matrix.conjTranspose U := by
      -- Let $U_A$ and $U_B$ be the eigenvector unitaries of $\rho_1$ and $\rho_2$, respectively.
      obtain ⟨U_A, hU_A⟩ : ∃ U_A : Matrix d₁ d₁ ℂ, U_A ∈ Matrix.unitaryGroup d₁ ℂ ∧ ρ₁.M = U_A * Matrix.diagonal (fun i => (ρ₁.spectrum i : ℂ)) * Matrix.conjTranspose U_A := by
        have := ρ₁.M.H.spectral_theorem;
        refine' ⟨ _, _, this ⟩;
        simp
      obtain ⟨U_B, hU_B⟩ : ∃ U_B : Matrix d₂ d₂ ℂ, U_B ∈ Matrix.unitaryGroup d₂ ℂ ∧ ρ₂.M = U_B * Matrix.diagonal (fun j => (ρ₂.spectrum j : ℂ)) * Matrix.conjTranspose U_B := by
        have := ρ₂.M.H.spectral_theorem;
        refine' ⟨ _, _, this ⟩;
        simp
      refine' ⟨ Matrix.kroneckerMap ( fun x y => x * y ) U_A U_B, _, _ ⟩;
      · simp_all only [ne_eq, Matrix.mem_unitaryGroup_iff, mat_M, Matrix.star_kron];
        have h_unitary : Matrix.kroneckerMap (fun x y => x * y) U_A U_B * Matrix.kroneckerMap (fun x y => x * y) (Star.star U_A) (Star.star U_B) = 1 := by
          have h_unitary : Matrix.kroneckerMap (fun x y => x * y) U_A U_B * Matrix.kroneckerMap (fun x y => x * y) (Star.star U_A) (Star.star U_B) = Matrix.kroneckerMap (fun x y => x * y) (U_A * Star.star U_A) (U_B * Star.star U_B) := by
            ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp [ Matrix.mul_apply, Matrix.kroneckerMap_apply ]
            ring_nf
            erw [ Finset.sum_product ]
            simp [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]
            exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
          simp_all only [zero_mul, implies_true, mul_zero, mul_one, Matrix.kroneckerMap_one_one]
        exact h_unitary
      · simp_all [ MState.prod, Matrix.mul_assoc, Matrix.mul_kronecker_mul ];
        congr 2;
        · ext ⟨ i, j ⟩ ⟨ i', j' ⟩ ; by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [ hi, hj ];
        · ext i j; simp [ Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply ] ;
    obtain ⟨ U, hU₁, hU₂ ⟩ := h_unitary;
    apply Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal;
    exact hU₁;
    convert hU₂ using 1;
    norm_num +zetaDelta at *;
  obtain ⟨ i, j, h ⟩ := h σ; have := congr_fun hσ ( i, j ) ; simp_all [ MState.spectrum ] ;
  exact h ( by exact Subtype.ext this )

theorem sInf_spectrum_prod (ρ : MState d) (σ : MState d₂) :
    sInf (_root_.spectrum ℝ (ρ ⊗ᴹ σ).m) = sInf (_root_.spectrum ℝ ρ.m) * sInf (_root_.spectrum ℝ σ.m) := by
  rcases isEmpty_or_nonempty d with _ | _; · simp
  rcases isEmpty_or_nonempty d₂ with _ | _; · simp
  rw [DensityOp.m, prod_M, HermitianMat.spectrum_prod, ← DensityOp.m, ← DensityOp.m]
  apply csInf_mul_nonneg
  · exact ContinuousFunctionalCalculus.spectrum_nonempty _ ρ.M.H
  · rw [DensityOp.m, ρ.M.H.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    apply ρ.eigenvalue_nonneg
  · exact ContinuousFunctionalCalculus.spectrum_nonempty _ σ.M.H
  · rw [DensityOp.m, σ.M.H.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    apply σ.eigenvalue_nonneg

--TODO: Spectrum of direct sum. Spectrum of partial trace?

/-- A mixed state is separable iff it can be written as a convex combination of product mixed states. -/
def IsSeparable (ρ : MState (d₁ × d₂)) : Prop :=
  ∃ ρLRs : Finset (MState d₁ × MState d₂), --Finite set of (ρL, ρR) pairs
    ∃ ps : ProbDistribution ρLRs, --ProbDistribution over those pairs, an ensemble
      ρ.M = ∑ ρLR : ρLRs, (ps ρLR : ℝ) • (Prod.fst ρLR.val).M ⊗ₖ (Prod.snd ρLR.val).M

/-- A product state `MState.prod` is separable. -/
theorem IsSeparable_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : IsSeparable (ρ₁ ⊗ᴹ ρ₂) := by
  let only := (ρ₁, ρ₂)
  use { only }, ProbDistribution.constant ⟨only, Finset.mem_singleton_self only⟩
  simp [prod, Unique.eq_default, only]

theorem eq_of_sum_eq_pure {d : Type*} [Fintype d] [DecidableEq d]
    {ι : Type*} {s : Finset ι} {p : ι → ℝ} {ρs : ι → MState d}
    {ρ : MState d} (h_pure : ρ.purity = 1) (h_sum : ρ.M = ∑ i ∈ s, p i • (ρs i).M)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1) (i : ι) (hi : i ∈ s) (hpi : 0 < p i) :
    ρs i = ρ := by
  have h_trace : ∀ j ∈ s, 0 < p j → (⟪ρ.M, (ρs j).M⟫ = 1) := by
    have h_tr_pure : ∑ j ∈ s, p j • ⟪ρ.M, (ρs j).M⟫ = 1 := by
      have h_tr_pure : ⟪ρ.M, ∑ j ∈ s, p j • (ρs j).M⟫ = ∑ j ∈ s, p j • ⟪ρ.M, (ρs j).M⟫ := by
        simp [ HermitianMat.inner_def, ← val_eq_coe ];
        rw [AddSubgroup.val_finsetSum]
        simp [Finset.mul_sum]
      rw [ ← h_tr_pure, ← h_sum ];
      convert h_pure using 1;
      exact beq_eq_beq.mp rfl;
    have h_tr_le_one : ∀ j ∈ s, ⟪ρ.M, (ρs j).M⟫ ≤ 1 := by
      intro j hj
      have h_tr_le_one_j : ⟪ρ.M, (ρs j).M⟫ ≤ ρ.M.trace * (ρs j).M.trace := by
        apply HermitianMat.inner_le_mul_trace
        · exact ρ.nonneg;
        · exact (ρs j).nonneg;
      simp_all only [smul_eq_mul, tr, mul_one, ge_iff_le]
      exact h_tr_le_one_j.trans ( h_sum ▸ ρ.tr.le );
    intro j hj hj_pos
    by_contra h_contra;
    have h_tr_lt_one : ∑ j ∈ s, p j • ⟪ρ.M, (ρs j).M⟫ < ∑ j ∈ s, p j := by
      apply Finset.sum_lt_sum;
      · exact fun i hi => mul_le_of_le_one_right ( hp_nonneg i hi ) ( h_tr_le_one i hi );
      · exact ⟨ j, hj, mul_lt_of_lt_one_right hj_pos ( lt_of_le_of_ne ( h_tr_le_one j hj ) h_contra ) ⟩;
    linarith;
  have h_eq : ρ.M = (ρs i).M := by
    have h_eq : ⟪ρ.M - (ρs i).M, ρ.M - (ρs i).M⟫ = 0 := by
      have h_eq : ⟪ρ.M - (ρs i).M, ρ.M - (ρs i).M⟫ = ⟪ρ.M, ρ.M⟫ - 2 * ⟪ρ.M, (ρs i).M⟫ + ⟪(ρs i).M, (ρs i).M⟫ := by
        simp only [HermitianMat.inner_def, IsMaximalSelfAdjoint.RCLike_selfadjMap, mat_sub, mat_M,
          RCLike.re_to_complex];
        simp [ Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_mul_comm ( ρ.m ) ]
        ring
      have h_eq : ⟪ρ.M, ρ.M⟫ = 1 ∧ ⟪(ρs i).M, (ρs i).M⟫ ≤ 1 := by
        have h_eq : ⟪ρ.M, ρ.M⟫ = 1 := by
          convert h_pure using 1;
          exact beq_eq_beq.mp rfl;
        have h_eq : ∀ (A : HermitianMat d ℂ), 0 ≤ A → A.trace = 1 → ⟪A, A⟫ ≤ 1 := by
          intros A hA_nonneg hA_trace
          have h_eq : ⟪A, A⟫ ≤ A.trace * A.trace := by
            apply HermitianMat.inner_le_mul_trace hA_nonneg hA_nonneg;
          aesop;
        exact ⟨ by assumption, h_eq _ (ρs i).nonneg (ρs i).tr ⟩;
      linarith [ h_trace i hi hpi, (ρ.M - (ρs i).M).inner_self_nonneg ];
    -- Since the inner product of a matrix with itself is zero if and only if the matrix is zero, we have ρ.M - (ρs i).M = 0.
    have h_zero : ρ.M - (ρs i).M = 0 := by
      apply inner_self_eq_zero.mp h_eq;
    exact eq_of_sub_eq_zero h_zero;
  exact DensityOp.ext h_eq.symm

theorem purity_prod {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ₁ : MState d₁) (ρ₂ : MState d₂) : (ρ₁ ⊗ᴹ ρ₂).purity = ρ₁.purity * ρ₂.purity := by
  exact prod_inner_prod ρ₁ ρ₁ ρ₂ ρ₂

theorem pure_eq_pure_iff {d : Type*} [Fintype d] [DecidableEq d] (ψ φ : Ket d) :
    pure ψ = pure φ ↔ ∃ z : ℂ, ‖z‖ = 1 ∧ ψ.vec = z • φ.vec := by
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · -- By definition of pure state, we have that ψ.vec * conj ψ.vec = φ.vec * conj φ.vec.
    have h_eq : ∀ i j, ψ.vec i * starRingEnd ℂ (ψ.vec j) = φ.vec i * starRingEnd ℂ (φ.vec j) := by
      intro i j;
      replace h := congr_arg ( fun ρ => ρ.M.mat i j ) h ; aesop;
    -- Let $k$ be such that $\varphi_k \neq 0$.
    obtain ⟨k, hk⟩ : ∃ k, φ.vec k ≠ 0 := by
      exact φ.exists_ne_zero;
    -- Let $z = \frac{\psi_k}{\varphi_k}$. Then $|z| = 1$.
    obtain ⟨z, hz⟩ : ∃ z : ℂ, ψ.vec k = z * φ.vec k ∧ ‖z‖ = 1 := by
      specialize h_eq k k
      simp_all only [ne_eq]
      refine' ⟨ ψ.vec k / φ.vec k, _, _ ⟩ <;> simp_all [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
      rw [ div_eq_iff ] <;> norm_cast at * <;> aesop;
    refine' ⟨ z, hz.2, funext fun i => _ ⟩;
    specialize h_eq i k
    simp_all
    -- Since $\overline{z} \cdot \overline{\varphi_k} \neq 0$, we can divide both sides of the equation by $\overline{z} \cdot \overline{\varphi_k}$.
    have h_div : ψ.vec i * starRingEnd ℂ z = φ.vec i := by
      exact mul_left_cancel₀ ( show starRingEnd ℂ ( φ.vec k ) ≠ 0 from by simpa [ Complex.ext_iff ] using hk ) ( by linear_combination' h_eq );
    rw [ ← h_div, mul_left_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq ] ; aesop;
  · cases h
    rename_i h
    obtain ⟨left, right⟩ := h
    -- Since $|w| = 1$, we have $w \overline{w} = 1$, which simplifies the matrix to $\phi \overline{\phi}^T$.
    have h_simp : ∀ i j, ψ.vec i * star (ψ.vec j) = φ.vec i * star (φ.vec j) := by
      simp [ *, Complex.ext_iff ];
      intro i j; rw [ Complex.norm_def ] at left; simp_all [ Complex.normSq ];
      grind +ring;
    exact DensityOp.ext_m ( by ext i j; simpa [ Matrix.vecMulVec, Ket.apply ] using h_simp i j )

/-- Two kets are phase-equivalent if and only if their pure states are equal. -/
theorem PhaseEquiv_iff_pure_eq {d : Type*} [Fintype d] [DecidableEq d] (ψ φ : Ket d) :
    Ket.PhaseEquiv.r ψ φ ↔ MState.pure ψ = MState.pure φ := by
  exact (pure_eq_pure_iff ψ φ).symm

/-- `MState.pure` descends to the quotient `KetUpToPhase`. -/
def pureQ {d : Type*} [Fintype d] [DecidableEq d] : KetUpToPhase d → MState d :=
  @Quotient.lift _ _ Ket.PhaseEquiv MState.pure (fun a b h => (PhaseEquiv_iff_pure_eq a b).mp h)

@[simp]
theorem pureQ_mk {d : Type*} [Fintype d] [DecidableEq d] (ψ : Ket d) :
    pureQ (Quotient.mk Ket.PhaseEquiv ψ) = MState.pure ψ := rfl

theorem pureQ_injective {d : Type*} [Fintype d] [DecidableEq d] : Function.Injective (pureQ (d := d)) := by
  intro a b h
  induction a using Quotient.ind
  induction b using Quotient.ind
  simp [pureQ] at h
  exact Quotient.sound ((PhaseEquiv_iff_pure_eq _ _).mpr h)

theorem pure_separable_imp_IsProd {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) (h : IsSeparable (pure ψ)) : ψ.IsProd := by
  obtain ⟨ ρLRs, ps, hps ⟩ := h;
  -- Since `pure ψ` is pure (`purity = 1`), by `MState.eq_of_sum_eq_pure`, for any `k` with `p_k > 0`, we have `pure ψ = ρL_k ⊗ᴹ ρR_k`.
  obtain ⟨k, hk⟩ : ∃ k : { x : MState d₁ × MState d₂ // x ∈ ρLRs }, 0 < (ps k : ℝ) ∧ (MState.pure ψ).M = (k.val.1).M ⊗ₖ (k.val.2).M := by
    have h_pure : (MState.pure ψ).purity = 1 := by
      exact ( pure_iff_purity_one _ ).mp ⟨ ψ, rfl ⟩;
    obtain ⟨k, hk⟩ : ∃ k : { x : MState d₁ × MState d₂ // x ∈ ρLRs }, 0 < (ps k : ℝ) := by
      exact ⟨ Classical.choose ( show ∃ k : ρLRs, 0 < ( ps k : ℝ ) from by exact not_forall_not.mp fun h => by have := ps.2; simp_all ), Classical.choose_spec ( show ∃ k : ρLRs, 0 < ( ps k : ℝ ) from by exact not_forall_not.mp fun h => by have := ps.2; simp_all) ⟩;
    refine' ⟨ k, hk, _ ⟩;
    convert MState.eq_of_sum_eq_pure h_pure _ _ _ k _ _;
    rotate_left;
    exact Finset.univ;
    use fun x => ( ps x : ℝ );
    use fun x => MState.prod x.val.1 x.val.2;
    all_goals norm_cast;
    · simpa using hps
    · exact fun i a => unitInterval.nonneg (ps i);
    · exact ps.2;
    · exact Finset.mem_univ k;
    · constructor
      · intro a
        exact DensityOp.ext (by simpa using a.symm)
      · intro a
        rw [← a]
        simp
  -- Since `pure ψ` is pure (`purity = 1`), by `MState.pure_iff_purity_one`, `ρL_k = pure ξ` and `ρR_k = pure φ` for some `ξ, φ`.
  have hprod : pure ψ = k.val.1 ⊗ᴹ k.val.2 := DensityOp.ext (by simpa using hk.2)
  have h_purity : (pure ψ).purity = (k.val.1).purity * (k.val.2).purity := by
    rw [hprod, MState.purity_prod]
  have h_purity_one : (pure ψ).purity = 1 := (pure_iff_purity_one _).mp ⟨ψ, rfl⟩
  rw [h_purity, Prob.mul_eq_one_iff] at h_purity_one
  obtain ⟨ξ, hξ⟩ : ∃ ξ : MState d₁, k.val.1 = ξ ∧ ξ.purity = 1 :=
    ⟨k.val.1, rfl, h_purity_one.1⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : MState d₂, k.val.2 = φ ∧ φ.purity = 1 :=
    ⟨k.val.2, rfl, h_purity_one.2⟩
  -- Since `ξ` and `φ` are pure states, we have `ξ = pure ξ'` and `φ = pure φ'` for some `ξ', φ'`.
  obtain ⟨ξ', hξ'⟩ : ∃ ξ' : Ket d₁, ξ = MState.pure ξ' := by
    have := MState.pure_iff_purity_one ξ;
    exact this.mpr hξ.2
  obtain ⟨φ', hφ'⟩ : ∃ φ' : Ket d₂, φ = MState.pure φ' := by
    have := MState.pure_iff_purity_one φ; aesop;
  -- Since `pure ψ = pure ξ ⊗ᵠ pure φ`, we have `ψ = ξ ⊗ᵠ φ` up to a global phase `z`.
  have h_eq : (pure ψ).M = (pure (ξ' ⊗ᵠ φ')).M := by
    rw [ hk.2, hξ.1, hξ', hφ.1, hφ', MState.pure_prod_pure ];
    simp
  -- Since `pure ψ = pure (ξ' ⊗ᵠ φ')`, we have `ψ = ξ' ⊗ᵠ φ'` up to a global phase `z`.
  have h_eq_ket : ∃ z : ℂ, ‖z‖ = 1 ∧ ψ.vec = z • (ξ' ⊗ᵠ φ').vec := by
    have := MState.pure_eq_pure_iff ψ ( ξ' ⊗ᵠ φ' );
    exact this.mp ( DensityOp.ext h_eq );
  obtain ⟨ z, hz₁, hz₂ ⟩ := h_eq_ket;
  use ⟨ fun i => z * ξ' i, ?_ ⟩, φ';
  ext ⟨ i, j ⟩
  have hz := congr_fun hz₂ ( i, j )
  simp only [ Ket.prod, Ket.apply, Pi.smul_apply, smul_eq_mul ] at hz ⊢
  linear_combination hz
  simp [ hz₁]
  simpa [ Complex.normSq_eq_norm_sq, Ket.apply ] using ξ'.normalized'

/-- A pure state is separable iff the ket is a product state. -/
theorem pure_separable_iff_IsProd (ψ : Ket (d₁ × d₂)) :
    IsSeparable (pure ψ) ↔ ψ.IsProd := by
  apply Iff.intro
  · exact pure_separable_imp_IsProd ψ
  · rintro ⟨ ξ, φ, rfl ⟩
    rw [pure_prod_pure ξ φ]
    exact IsSeparable_prod _ _;

/--
A mixed state is pure if and only if its rank is 1.
-/
theorem pure_iff_rank_eq_one {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    (∃ ψ, ρ = pure ψ) ↔ ρ.m.rank = 1 := by
  constructor <;> intro h;
  · obtain ⟨w, rfl⟩ := h
    have hm : (pure w).m = Matrix.vecMulVec (w : d → ℂ) (conj (w : d → ℂ)) := by
      ext i j
      rw [pure_apply]
      rfl
    rw [hm]
    -- The rank of the outer product of a vector with itself is 1.
    have h_rank : ∀ (v : d → ℂ), v ≠ 0 → Matrix.rank (Matrix.vecMulVec v (conj v)) = 1 := by
      intro v hv_ne_zero
      have h_outer_product : ∀ (u : d → ℂ), ∃ (c : ℂ), Matrix.mulVec (Matrix.vecMulVec v (conj v)) u = c • v := by
        intro u
        use ∑ i, (starRingEnd ℂ (v i)) * (u i);
        ext i; simp [ Matrix.vecMulVec, Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
      apply le_antisymm
      · have h_outer_product : LinearMap.range (Matrix.mulVecLin (Matrix.vecMulVec v (conj v))) ≤ Submodule.span ℂ {v} := by
          rintro x ⟨ u, rfl ⟩ ; obtain ⟨ c, hc ⟩ := h_outer_product u; aesop;
        exact le_trans ( Submodule.finrank_mono h_outer_product ) ( finrank_span_le_card _ ) |> le_trans <| by simp ;
      · contrapose! hv_ne_zero; simp_all [ Matrix.rank, Submodule.eq_bot_iff ] ;
        ext i; specialize hv_ne_zero ( Pi.single i 1 ) ; simp_all [ Matrix.vecMulVec ] ;
        simpa using congr_fun hv_ne_zero i;
    exact h_rank _ ( fun h => by simpa [ h ] using w.exists_ne_zero );
  · -- Since ρ is Hermitian and has rank 1, it must be of the form |ψ⟩⟨ψ| for some ket ψ.
    obtain ⟨ψ, hψ⟩ : ∃ ψ : d → ℂ, ρ.m = Matrix.of (fun i j => ψ i * star (ψ j)) := by
      -- Since ρ is Hermitian and has rank 1, it must be of the form |ψ⟩⟨ψ| for some ket ψ. Use this fact.
      have h_pure : ∃ ψ : d → ℂ, ρ.m = Matrix.of (fun i j => ψ i * star (ψ j)) := by
        have h_rank : ρ.m.rank = 1 := h
        have h_herm : ρ.m.IsHermitian := by
          exact ρ.M.property
        have := h_herm.spectral_theorem;
        -- Since the rank of ρ.m is 1, the diagonal matrix in the spectral theorem must have exactly one non-zero entry.
        obtain ⟨i, hi⟩ : ∃ i : d, h_herm.eigenvalues i ≠ 0 ∧ ∀ j : d, j ≠ i → h_herm.eigenvalues j = 0 := by
          have h_diag : ∑ i : d, (if h_herm.eigenvalues i = 0 then 0 else 1) = 1 := by
            have h_diag : Matrix.rank (Matrix.diagonal (h_herm.eigenvalues)) = 1 := by
              have h_diag : Matrix.rank (Matrix.diagonal (h_herm.eigenvalues)) = Matrix.rank (ρ.m) := by
                exact Eq.symm (Matrix.IsHermitian.rank_eq_rank_diagonal h_herm);
              exact h_diag.trans h_rank;
            rw [ Matrix.rank_diagonal ] at h_diag;
            simp [ Finset.sum_ite ];
            rw [ Fintype.card_subtype ] at h_diag ; exact h_diag;
          obtain ⟨i, hi⟩ : ∃ i : d, h_herm.eigenvalues i ≠ 0 := by
            exact not_forall.mp fun h => by simp [ h ] at h_diag;
          rw [ ← Finset.add_sum_erase _ _ ( Finset.mem_univ i ) ] at h_diag;
          exact ⟨ i, hi, fun j hj => Classical.not_not.1 fun hj' => absurd h_diag ( by rw [ if_neg hi ] ; exact ne_of_gt ( lt_add_of_pos_right _ ( lt_of_lt_of_le ( by simp [ hj' ] ) ( Finset.single_le_sum ( fun x _ => by positivity ) ( Finset.mem_erase.2 ⟨ hj, Finset.mem_univ j ⟩ ) ) ) ) ) ⟩;
        -- Since the diagonal matrix in the spectral theorem has exactly one non-zero entry, we can write ρ.m as |ψ⟩⟨ψ| for some ket ψ.
        use fun j => (h_herm.eigenvectorUnitary : Matrix d d ℂ) j i * Real.sqrt (h_herm.eigenvalues i);
        convert this using 1
        ext j k; simp [ Matrix.mul_apply, Matrix.diagonal ]
        ring_nf
        rw [ Finset.sum_eq_single i ] <;> simp +contextual [ hi ];
        exact Or.inl <| Or.inl <| mod_cast Real.sq_sqrt <| by
          have := ρ.psd.eigenvalues_nonneg i;
          exact this
      exact h_pure;
    have h_norm : ∑ x, Complex.normSq (ψ x) = 1 := by
      have := ρ.tr';
      simp_all [ Complex.ext_iff, Matrix.trace ];
      simpa only [ Complex.normSq_apply, mul_comm ] using this.1;
    use ⟨ψ, by
      simpa [ Complex.normSq_eq_norm_sq ] using h_norm⟩
    generalize_proofs at *;
    refine' DensityOp.ext_m _ ; aesop

/--
A ket on a product space is a product state if and only if its coefficient matrix has rank 1.
-/
theorem Ket.IsProd_iff_rank_eq_one {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) :
    ψ.IsProd ↔ (Matrix.of (fun i j => ψ (i, j))).rank = 1 := by
  rw [ Ket.IsProd_iff_mul_eq_mul ];
  constructor;
  · intro h;
    obtain ⟨ξ, ψ', hξψ'⟩ : ∃ ξ : d₁ → ℂ, ∃ ψ' : d₂ → ℂ, ∀ i j, ψ (i, j) = ξ i * ψ' j := by
      -- Let's choose any $j₀$ such that $\psi(i, j₀) \neq 0$ for some $i$.
      obtain ⟨j₀, hj₀⟩ : ∃ j₀ : d₂, ∃ i₀ : d₁, ψ (i₀, j₀) ≠ 0 := by
        have := ψ.exists_ne_zero;
        exact ⟨ this.choose.2, this.choose.1, this.choose_spec ⟩;
      choose i₀ hi₀ using hj₀;
      exact ⟨ fun i => ψ ( i, j₀ ) / ψ ( i₀, j₀ ), fun j => ψ ( i₀, j ), fun i j => by rw [ div_mul_eq_mul_div, eq_div_iff hi₀ ] ; linear_combination h i i₀ j j₀ ⟩;
    -- Since the matrix is a product of two vectors, its rank is 1.
    have h_rank : Matrix.rank (Matrix.of (fun i j => ξ i * ψ' j)) ≤ 1 := by
      -- The range of the matrix is spanned by the single vector ξ.
      have h_range : LinearMap.range (Matrix.mulVecLin (Matrix.of (fun i j => ξ i * ψ' j))) ≤ Submodule.span ℂ {ξ} := by
        rintro x ⟨ y, rfl ⟩;
        rw [ Submodule.mem_span_singleton ];
        exact ⟨ ∑ j, ψ' j * y j, by ext i; simp [ Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ⟩;
      exact le_trans ( Submodule.finrank_mono h_range ) ( finrank_span_le_card _ ) |> le_trans <| by norm_num;
    cases h_rank.eq_or_lt <;> simp_all [ Matrix.rank, Submodule.eq_bot_iff ];
    · convert ‹Module.finrank ℂ ( LinearMap.range ( Matrix.mulVecLin ( Matrix.of fun i j => ξ i * ψ' j ) ) ) = 1› using 3 ; aesop;
      · aesop;
      · ext; simp [hξψ'];
      · have hof : (Matrix.of fun i j => ψ (i, j)) = (Matrix.of fun i j => ξ i * ψ' j) := by
          ext i j
          simp [hξψ']
        rw [hof]
    · have := ψ.exists_ne_zero
      simp_all only [ne_eq, mul_eq_zero, not_or, Prod.exists, exists_and_left, exists_and_right]
      obtain ⟨left, right⟩ := this
      obtain ⟨w, h_2⟩ := left
      obtain ⟨w_1, h_3⟩ := right
      rename_i h_1
      specialize h_1 ( Pi.single w_1 1 )
      simp_all [ funext_iff]
  · rw [ Matrix.rank ];
    rw [ finrank_eq_one_iff' ]
    intro a i₁ i₂ j₁ j₂
    simp_all only [ne_eq, Subtype.forall, LinearMap.mem_range, Matrix.mulVecBilin_apply, forall_exists_index,
      Subtype.exists, Submodule.mk_eq_zero, SetLike.mk_smul_mk, Subtype.mk.injEq, forall_apply_eq_imp_iff,
      exists_and_left, exists_prop]
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    obtain ⟨w_1, h⟩ := left_1
    subst h
    obtain ⟨ c, hc ⟩ := right ( Pi.single j₁ 1 ) ;
    obtain ⟨ d, hd ⟩ := right ( Pi.single j₂ 1 ) ;
    simp_all only [funext_iff, Matrix.mulVec, Matrix.of_apply, Pi.zero_apply, not_forall,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
      Matrix.col_apply]
    rw [ ← hc i₁, ← hd i₁, ← hc i₂, ← hd i₂ ] ; ring

/-- A pure state is separable iff the partial trace on the left is pure. -/
theorem pure_separable_iff_traceLeft_pure (ψ : Ket (d₁ × d₂)) : IsSeparable (pure ψ) ↔
    ∃ ψ₁, pure ψ₁ = (pure ψ).traceLeft := by
  have h1 := MState.pure_separable_iff_IsProd ψ;
  have h2 := Ket.IsProd_iff_rank_eq_one ψ;
  have h3 := MState.pure_iff_rank_eq_one ( ( MState.pure ψ ).traceLeft )
  simp_all
  have h4 : Matrix.rank ((MState.pure ψ).m.traceLeft) = Matrix.rank (Matrix.of (fun i j => ψ (i, j))) := by
    have h4 : (MState.pure ψ).m.traceLeft = Matrix.transpose (Matrix.conjTranspose (Matrix.of (fun i j => ψ (i, j))) * Matrix.of (fun i j => ψ (i, j))) := by
      ext i j
      simp [ Matrix.traceLeft, Matrix.mul_apply ] ;
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _;
    rw [ h4, Matrix.rank_transpose, Matrix.rank_conjTranspose_mul_self ];
  grind

--TODO: Separable states are convex

section purification

/-- The purification of a mixed state. Always uses the full dimension of the Hilbert space (d) to
 purify, so e.g. an existing pure state with d=4 still becomes d=16 in the purification. The defining
 property is `MState.traceRight_of_purify`; see also `MState.purify'` for the bundled version. -/
def purify (ρ : MState d) : Ket (d × d) where
  vec := fun (i,j) ↦
    let ρ2 := ρ.Hermitian.eigenvectorUnitary i j
    ρ2 * (ρ.Hermitian.eigenvalues j).sqrt
  normalized' := by
    have h₁ := fun i ↦ ρ.psd.eigenvalues_nonneg i
    simp only [Complex.norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, h₁, Real.sq_sqrt,
      Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_mul]
    have : ∀ x, ∑ i : d, ‖ρ.Hermitian.eigenvectorUnitary i x‖ ^ 2 = 1 :=
      Matrix.unitaryGroup_row_norm ρ.Hermitian.eigenvectorUnitary
    apply @RCLike.ofReal_injective ℂ
    simp_rw [this, one_mul, Matrix.IsHermitian.sum_eigenvalues_eq_trace]
    exact ρ.tr'

/-- The defining property of purification, that tracing out the purifying system gives the
 original mixed state. -/
@[simp]
theorem purify_spec (ρ : MState d) : (pure ρ.purify).traceRight = ρ := by
  -- The spectral theorem, written out entrywise.
  have h_spectral : ∀ i j, ∑ x, ρ.Hermitian.eigenvectorUnitary i x *
      (ρ.Hermitian.eigenvalues x : ℂ) *
      starRingEnd ℂ (ρ.Hermitian.eigenvectorUnitary j x) = (ρ.M : Matrix d d ℂ) i j := by
    intro i j
    have h : (ρ.M : Matrix d d ℂ) = Matrix.of (fun i j => ∑ x,
        ρ.Hermitian.eigenvectorUnitary i x * (ρ.Hermitian.eigenvalues x : ℂ) *
        starRingEnd ℂ (ρ.Hermitian.eigenvectorUnitary j x)) := by
      conv_lhs => rw [mat_M, ρ.Hermitian.spectral_theorem]
      ext i j
      simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    exact (congr_fun (congr_fun h i) j).symm
  ext i j
  simp_rw [purify, traceRight, HermitianMat.traceRight, Matrix.traceRight]
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply, m_ofMat, mat_M, pure_apply,
    mat_mk, Matrix.of_apply, Ket.apply, map_mul, Complex.conj_ofReal]
  show _ = (ρ.M : Matrix d d ℂ) i j
  rw [← h_spectral i j]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hs : ((ρ.Hermitian.eigenvalues x : ℝ) : ℂ) =
      (√(ρ.Hermitian.eigenvalues x) : ℂ) * (√(ρ.Hermitian.eigenvalues x) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (ρ.eigenvalue_nonneg x)]
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply, hs]
  ring

/-- `MState.purify` bundled with its defining property `MState.traceRight_of_purify`. -/
def purifyX (ρ : MState d) : { ψ : Ket (d × d) // (pure ψ).traceRight = ρ } :=
  ⟨ρ.purify, ρ.purify_spec⟩

end purification

def relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : MState d₂ :=
  DensityOp.ofMat (ρ.M.reindex e.symm) (by simp [zero_le_iff, ρ.psd]) (by simp [trace])

@[simp]
theorem relabel_M (ρ : MState d₁) (e : d₂ ≃ d₁) : (ρ.relabel e).M = ρ.M.reindex e.symm := by
  rw [relabel, M_ofMat]

@[simp]
theorem relabel_m (ρ : MState d₁) (e : d₂ ≃ d₁) :
    (ρ.relabel e).m = ρ.m.submatrix e e := by
  rw [← mat_M, relabel_M]
  rfl

@[simp]
theorem relabel_refl {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    ρ.relabel (Equiv.refl d) = ρ := by
  ext
  simp

/-- Relabeling a pure state by a bijection yields another pure state. -/
theorem relabel_pure_exists (ψ : Ket d₁) (e : d₂ ≃ d₁) :
    ∃ ψ' : Ket d₂, (pure ψ).relabel e = pure ψ' := by
  have hnorm : ∑ i, ‖ψ (e i)‖ ^ 2 = 1 := by
    rw [← ψ.normalized', Fintype.sum_equiv e]
    congr!
  refine ⟨⟨fun i => ψ (e i), hnorm⟩, ?_⟩
  ext i j
  simp [reindex_apply, Ket.apply, Matrix.vecMulVec_apply, Bra.eq_conj]

@[simp]
theorem relabel_relabel {d d₂ d₃ : Type*}
    [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]
    (ρ : MState d) (e : d₂ ≃ d) (e₂ : d₃ ≃ d₂) : (ρ.relabel e).relabel e₂ = ρ.relabel (e₂.trans e) := by
  ext
  simp [reindex_apply]

theorem eq_relabel_iff {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ : MState d₁) (σ : MState d₂) (h : d₁ ≃ d₂) :
    ρ = σ.relabel h ↔ ρ.relabel h.symm = σ := by
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

theorem relabel_comp {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      [Fintype d₃] [DecidableEq d₃] (ρ : MState d₁) (e : d₂ ≃ d₁) (f : d₃ ≃ d₂) :
    (ρ.relabel e).relabel f = ρ.relabel (f.trans e) := by
  ext
  simp [reindex_apply]

theorem relabel_cast {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂]
       (ρ : MState d₁) (e : d₂ = d₁) :
    ρ.relabel (Equiv.cast e) = cast (by have := e.symm; congr <;> (apply Subsingleton.helim; congr)) ρ := by
  ext i j
  simp only [relabel_M, mat_reindex, mat_M, Matrix.reindex_apply, Matrix.submatrix_apply]
  subst e
  congr!
  symm
  apply cast_heq

@[simp]
theorem spectrum_relabel {ρ : MState d} (e : d₂ ≃ d) :
    _root_.spectrum ℝ (ρ.relabel e).m = _root_.spectrum ℝ ρ.m := by
  ext1 v
  rw [spectrum.mem_iff] --TODO make a plain `Matrix` version of this
  rw [Algebra.algebraMap_eq_smul_one v]
  rw [MState.relabel_m, ← Matrix.submatrix_one_equiv e]
  rw [← Matrix.smul_apply, ← Matrix.submatrix_smul]
  rw [← Matrix.sub_apply, ← Matrix.submatrix_sub]
  rw [Matrix.isUnit_submatrix_equiv]
  rw [← Algebra.algebraMap_eq_smul_one v, ← spectrum.mem_iff]

/-- The purity of a state is invariant under relabeling of the basis. -/
@[simp]
theorem purity_relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : (ρ.relabel e).purity = ρ.purity := by
  simp [purity, inner_def, -inner_self_eq_norm_sq_to_K]
--TODO: Swap and assoc for kets.
--TODO: Connect these to unitaries (when they can be)

/-- The heterogeneous SWAP gate that exchanges the left and right halves of a quantum system.
  This can apply even when the two "halves" are of different types, as opposed to (say) the SWAP
  gate on quantum circuits that leaves the qubit dimensions unchanged. Notably, it is not unitary. -/
def SWAP (ρ : MState (d₁ × d₂)) : MState (d₂ × d₁) :=
  ρ.relabel (Equiv.prodComm d₁ d₂).symm

@[simp]
theorem SWAP_M (ρ : MState (d₁ × d₂)) : ρ.SWAP.M = ρ.M.reindex (Equiv.prodComm d₁ d₂) := by
  rw [SWAP, relabel_M, Equiv.symm_symm]

@[simp]
theorem SWAP_m (ρ : MState (d₁ × d₂)) : ρ.SWAP.m =
    ρ.m.submatrix (Equiv.prodComm d₁ d₂).symm (Equiv.prodComm d₁ d₂).symm := by
  rw [SWAP, relabel_m]

/--
The multiset of values in the spectrum of a relabeled state is the same as the multiset of values in the spectrum of the original state.
-/
lemma multiset_spectrum_relabel_eq {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ : MState d₁) (e : d₂ ≃ d₁) :
    Multiset.map (ρ.relabel e).spectrum Finset.univ.val = Multiset.map ρ.spectrum Finset.univ.val := by
  have h_charpoly : Matrix.charpoly (ρ.relabel e).m = Matrix.charpoly ρ.m := by
    simpa [relabel_m] using Matrix.charpoly_reindex e.symm ρ.m
  have h_eigenvalues : Multiset.map (ρ.relabel e).M.H.eigenvalues Finset.univ.val = Multiset.map ρ.M.H.eigenvalues Finset.univ.val := by
    have h_eigenvalues : Polynomial.roots (Matrix.charpoly (ρ.relabel e).m) = Polynomial.roots (Matrix.charpoly ρ.m) := by
      rw [h_charpoly];
    have := ρ.M.H.roots_charpoly_eq_eigenvalues
    have := (ρ.relabel e).M.H.roots_charpoly_eq_eigenvalues
    simp_all only [relabel_m, mat_M, Complex.coe_algebraMap, Function.comp_apply, relabel_M,
      mat_reindex, Matrix.reindex_apply, Equiv.symm_symm]
    replace this := congr_arg ( fun m => m.map ( fun x => x.re ) ) this
    aesop;
  unfold MState.spectrum;
  ext
  rename_i a
  simp_all only [relabel_m, relabel_M, mat_reindex, mat_M, Matrix.reindex_apply, Equiv.symm_symm]
  obtain ⟨val, property⟩ := a
  obtain ⟨left, right⟩ := property
  convert congr_arg ( fun m => Multiset.count val m ) h_eigenvalues using 1;
  · rw [ Multiset.count_map, Multiset.count_map ];
    simp [ Subtype.ext_iff ];
    congr! 2;
  · erw [ Multiset.count_map, Multiset.count_map ];
    congr! 2;
    exact beq_eq_beq.mp rfl

theorem spectrum_SWAP (ρ : MState (d₁ × d₂)) : ∃ e, ρ.SWAP.spectrum.relabel e = ρ.spectrum := by
  -- Apply the lemma exists_equiv_of_multiset_map_eq with the appropriate parameters.
  obtain ⟨w, h⟩ := exists_equiv_of_multiset_map_eq (fun p => ρ.spectrum p) (fun p => ρ.SWAP.spectrum p)
    (ρ.multiset_spectrum_relabel_eq (Equiv.prodComm _ _).symm ▸ rfl)
  use w
  ext x
  simp_rw [h]
  rfl

@[simp]
theorem SWAP_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.SWAP = ρ := by
  ext
  simp [SWAP, reindex_apply]

@[simp]
theorem traceLeft_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceLeft = ρ.traceRight := by
  ext
  simp [SWAP, reindex_apply, traceLeft_apply, traceRight_apply]

@[simp]
theorem traceRight_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceRight = ρ.traceLeft := by
  ext
  simp [SWAP, reindex_apply, traceLeft_apply, traceRight_apply]

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc (ρ : MState ((d₁ × d₂) × d₃)) : MState (d₁ × d₂ × d₃) :=
  ρ.relabel (Equiv.prodAssoc d₁ d₂ d₃).symm

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc' (ρ : MState (d₁ × d₂ × d₃)) : MState ((d₁ × d₂) × d₃) :=
  ρ.SWAP.assoc.SWAP.assoc.SWAP

/-- `MState.assoc'` is the relabelling along `Equiv.prodAssoc`; the chain of swaps and associators
in its definition composes to that single permutation. -/
theorem assoc'_eq_relabel (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc' = ρ.relabel (Equiv.prodAssoc d₁ d₂ d₃) := by
  apply DensityOp.ext_m
  ext ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩
  simp [assoc', assoc, SWAP]

@[simp]
theorem assoc_M (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.M = ρ.M.reindex (Equiv.prodAssoc d₁ d₂ d₃) := by
  rw [assoc, relabel_M, Equiv.symm_symm]

@[simp]
theorem assoc_m (ρ : MState ((d₁ × d₂) × d₃)) : ρ.assoc.m =
    ρ.m.submatrix (Equiv.prodAssoc d₁ d₂ d₃).symm (Equiv.prodAssoc d₁ d₂ d₃).symm := by
  rw [assoc, relabel_m]

@[simp]
theorem assoc'_M (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.M = ρ.M.reindex (Equiv.prodAssoc d₁ d₂ d₃).symm := by
  rw [assoc'_eq_relabel, relabel_M]

@[simp]
theorem assoc'_m (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.m = ρ.m.submatrix (Equiv.prodAssoc d₁ d₂ d₃) (Equiv.prodAssoc d₁ d₂ d₃) := by
  rw [assoc'_eq_relabel, relabel_m]

@[simp]
theorem assoc_assoc' (ρ : MState (d₁ × d₂ × d₃)) : ρ.assoc'.assoc = ρ := by
  ext
  simp [assoc, assoc', SWAP, reindex_apply]

@[simp]
theorem assoc'_assoc (ρ : MState ((d₁ × d₂) × d₃)) : ρ.assoc.assoc' = ρ := by
  ext
  simp [assoc, assoc', SWAP, reindex_apply]

@[simp]
theorem traceLeft_right_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceRight = ρ.traceRight.traceLeft := by
  ext
  simpa [assoc, reindex_apply, traceLeft_apply, traceRight_apply]
    using Finset.sum_comm

@[simp]
theorem traceRight_left_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceLeft = ρ.traceLeft.traceRight := by
  rw [← ρ.assoc'.traceLeft_right_assoc, assoc_assoc']

@[simp]
theorem traceRight_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceRight = ρ.traceRight.traceRight := by
  ext
  simp [assoc, reindex_apply, traceRight_apply, Fintype.sum_prod_type]

@[simp]
theorem traceLeft_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceLeft = ρ.traceLeft.traceLeft := by
  ext
  simp [assoc', traceLeft_apply]

@[simp]
theorem traceLeft_left_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceLeft = ρ.traceLeft := by
  simp [← traceLeft_assoc']

@[simp]
theorem traceRight_right_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceRight = ρ.traceRight := by
  simp [assoc']

/-- **Matrix analogue of unit trace**: a density matrix, being PSD with trace one, has trace
norm one. -/
@[simp]
theorem traceNorm_eq_one (ρ : MState d) : ρ.m.traceNorm = 1 :=
  have := calc (ρ.m.traceNorm : ℂ)
    _ = ρ.m.trace := ρ.psd.traceNorm_eq_trace
    _ = 1 := ρ.tr'
  Complex.ofReal_eq_one.mp this

section TensorRearrange

/-! ### Rearranging tensor factors, operator-side

`MState.SWAP` and `MState.assoc` relabel the index type of a composite system; read through
`DensityOp.transport`, they are the tensor-product isometries of Mathlib. -/

open scoped TensorProduct

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [StdBasis ℂ E d₁]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [StdBasis ℂ F d₂]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [StdBasis ℂ G d₃]

/-- Swapping the two halves of a bipartite state is `TensorProduct.commIsometry`. -/
theorem SWAP_transport (ρ : MState (d₁ × d₂)) :
    ρ.SWAP.transport (F ⊗[ℂ] E) = (ρ.transport (E ⊗[ℂ] F)).congr (TensorProduct.commIsometry ℂ E F)
    := by
  ext1
  rw [DensityOp.M_congr_of_stdBasis _ _ (Equiv.prodComm d₁ d₂) StdBasis.commIsometry_stdBasis,
    DensityOp.M_transport, DensityOp.M_transport, SWAP_M]

/-- Reassociating a tripartite state is `TensorProduct.assocIsometry`. -/
theorem assoc_transport (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.transport (E ⊗[ℂ] (F ⊗[ℂ] G)) =
      (ρ.transport ((E ⊗[ℂ] F) ⊗[ℂ] G)).congr (TensorProduct.assocIsometry ℂ E F G) := by
  ext1
  rw [DensityOp.M_congr_of_stdBasis _ _ (Equiv.prodAssoc d₁ d₂ d₃)
    StdBasis.assocIsometry_stdBasis, DensityOp.M_transport, DensityOp.M_transport, assoc_M]

/-- Reassociating a tripartite state the other way is `TensorProduct.assocIsometry.symm`. -/
theorem assoc'_transport (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.transport ((E ⊗[ℂ] F) ⊗[ℂ] G) =
      (ρ.transport (E ⊗[ℂ] (F ⊗[ℂ] G))).congr (TensorProduct.assocIsometry ℂ E F G).symm := by
  have h := assoc_transport (E := E) (F := F) (G := G) ρ.assoc'
  rw [assoc_assoc'] at h
  rw [h, DensityOp.congr_congr_symm]

end TensorRearrange

--TODO: This naming is very inconsistent. Should be better about "prod" vs "kron"

theorem relabel_kron (ρ : MState d₁) (σ : MState d₂) (e : d₃ ≃ d₁) :
    ((ρ.relabel e) ⊗ᴹ σ) = (ρ ⊗ᴹ σ).relabel (e.prodCongr (Equiv.refl d₂)) := by
  ext i j
  simp [reindex_apply, kronecker_apply]

theorem kron_relabel (ρ : MState d₁) (σ : MState d₂) (e : d₃ ≃ d₂) :
    (ρ ⊗ᴹ σ.relabel e) = (ρ ⊗ᴹ σ).relabel ((Equiv.refl d₁).prodCongr e) := by
  ext i j
  simp [reindex_apply, kronecker_apply]

theorem prod_assoc (ρ : MState d₁) (σ : MState d₂) (τ : MState d₃) :
    (ρ ⊗ᴹ (σ ⊗ᴹ τ)) = (ρ ⊗ᴹ σ ⊗ᴹ τ).relabel (Equiv.prodAssoc d₁ d₂ d₃).symm := by
  ext : 2
  simp [-Matrix.kronecker_assoc']
  exact (Matrix.kronecker_assoc' ρ.m σ.m τ.m).symm

section topology

/-- Mixed states inherit the subspace topology from matrices -/
instance : TopologicalSpace (MState d) :=
  TopologicalSpace.induced DensityOp.M inferInstance

/-- The projection from mixed states to their Hermitian matrices is an embedding -/
theorem toMat_IsEmbedding :
    Topology.IsEmbedding (DensityOp.M : MState d → HermitianMat d ℂ) where
  eq_induced := rfl
  injective := DensityOp.M_Injective

instance : T3Space (MState d) :=
  Topology.IsEmbedding.t3Space toMat_IsEmbedding

instance : CompactSpace (MState d) := by
  constructor
  rw [(Topology.IsInducing.induced DensityOp.M).isCompact_iff]
  suffices IsCompact (Set.Icc 0 1 ∩ { m | m.trace = 1} : Set (HermitianMat d ℂ)) by
    convert this
    ext1 m
    constructor
    · rintro ⟨ρ, _, rfl⟩
      simp [ρ.nonneg, ρ.le_one]
    · simpa using fun m_pos _ m_tr ↦ ⟨DensityOp.ofMat m m_pos m_tr, by simp⟩
  apply isCompact_Icc.inter_right
  refine isClosed_eq ?_ continuous_const
  rw [funext trace_eq_re_trace]
  fun_prop

noncomputable instance : MetricSpace (MState d) :=
  MetricSpace.induced DensityOp.M DensityOp.M_Injective inferInstance

theorem dist_eq (x y : MState d) : dist x y = dist x.M y.M := by
  rfl

instance : BoundedSpace (MState d) where
  bounded_univ :=
    CompactSpace.isCompact_univ.isBounded

@[fun_prop]
theorem Continuous_HermitianMat : Continuous (DensityOp.M : MState d → HermitianMat d ℂ) :=
  continuous_iff_le_induced.mpr fun _ => id

@[fun_prop]
theorem Continuous_Matrix : Continuous (DensityOp.m : MState d → Matrix d d ℂ) := by
  unfold DensityOp.m
  fun_prop

theorem image_M_isBounded (S : Set (MState d)) : Bornology.IsBounded (DensityOp.M '' S) := by
  rw [← Bornology.isBounded_induced]
  exact Bornology.IsBounded.all S

end topology

section finprod

variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀(i :ι), Fintype (dI i)] [∀(i :ι), DecidableEq (dI i)]

def piProd (ρi : (i:ι) → MState (dI i)) : MState ((i:ι) → dI i) :=
  DensityOp.ofMat
    ⟨Matrix.piProd (fun i ↦ (ρi i).m), Matrix.IsHermitian.piProd (fun i ↦ (ρi i).Hermitian)⟩
    (by
      rw [zero_le_iff]
      exact Matrix.PosSemidef.piProd (fun i => psd (ρi i)))
    (by simp [trace, Matrix.trace_piProd])

@[simp]
theorem piProd_M (ρi : (i:ι) → MState (dI i)) :
    (piProd ρi).M =
      ⟨Matrix.piProd (fun i ↦ (ρi i).m), Matrix.IsHermitian.piProd (fun i ↦ (ρi i).Hermitian)⟩ := by
  rw [piProd, M_ofMat]

/-- The n-copy "power" of a mixed state, with the standard basis indexed by pi types. -/
def npow (ρ : MState d) (n : ℕ) : MState (Fin n → d) :=
  piProd (fun _ ↦ ρ)

@[inherit_doc]
infixl:110 " ⊗ᴹ^ " => MState.npow

end finprod

section posdef

theorem PosDef.kron {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    {σ₁ : MState d₁} {σ₂ : MState d₂} (hσ₁ : σ₁.m.PosDef) (hσ₂ : σ₂.m.PosDef) : (σ₁ ⊗ᴹ σ₂).m.PosDef := by
  rw [prod_m]
  exact hσ₁.kron hσ₂

theorem PosDef.relabel {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    {ρ : MState d₁} (hρ : ρ.m.PosDef) (e : d₂ ≃ d₁) : (ρ.relabel e).m.PosDef := by
  simpa [relabel_m] using Matrix.PosDef.reindex hρ e.symm

/-- If both states positive definite, so is their mixture. -/
theorem PosDef_mix {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₁ : σ₁.m.PosDef) (hσ₂ : σ₂.m.PosDef) (p : Prob) : (p [σ₁ ↔ σ₂]).m.PosDef := by
  rw [mix_m]
  exact Matrix.PosDef.Convex hσ₁ hσ₂ p.zero_le_coe (sub_nonneg.mpr Prob.coe_le_one) (by ring)

/-- If one state is positive definite and the mixture is nondegenerate, their mixture is also positive definite. -/
theorem PosDef_mix_of_ne_zero {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₁ : σ₁.m.PosDef) (p : Prob) (hp : p ≠ 0) : (p [σ₁ ↔ σ₂]).m.PosDef := by
  rw [mix_m]
  have hp' : (0 : ℝ) < (p : ℝ) :=
    Prob.zero_le_coe.lt_of_ne fun h ↦ hp (Prob.ext (by simpa using h.symm))
  exact (hσ₁.smul hp').add_posSemidef (σ₂.psd.rsmul (sub_nonneg.mpr Prob.coe_le_one))

/-- If the second state is positive definite and the mixture is nondegenerate, their mixture is also positive definite. -/
theorem PosDef_mix_of_ne_one {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₂ : σ₂.m.PosDef) (p : Prob) (hp : p ≠ 1) : (p [σ₁ ↔ σ₂]).m.PosDef := by
  rw [mix_m]
  have hp' : (0 : ℝ) < 1 - (p : ℝ) :=
    sub_pos.mpr <| Prob.coe_le_one.lt_of_ne fun h ↦ hp (Prob.ext (by simpa using h))
  exact (hσ₂.smul hp').posSemidef_add (σ₁.psd.rsmul Prob.zero_le_coe)

theorem uniform_posDef {d : Type*} [Nonempty d] [Fintype d] [DecidableEq d] :
    (uniform (d := d)).m.PosDef := by
  simp [uniform, ofClassical, m, HermitianMat.diagonal]
  exact Fintype.card_pos

theorem posDef_of_unique {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) [Unique d] : ρ.m.PosDef := by
  rw [Subsingleton.allEq ρ uniform]
  exact uniform_posDef

end posdef

end MState
