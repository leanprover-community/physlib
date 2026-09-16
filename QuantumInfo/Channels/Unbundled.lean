/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-! # Properties of Matrix Maps

Building on `MatrixMap`s, this defines the properties: `IsTracePreserving`, `Unital`,
`IsHermitianPreserving`, `IsPositive` and `IsCompletelyPositive`. They have basic facts
such as closure under composition, addition, and scaling.

These are the *unbundled* versions, which just state the relevant properties of a given `MatrixMap`.
The bundled versions are `HPMap`, `UnitalMap`, `TPMap`, `PMap`, and `CPMap` respectively, given
in Bundled.lean.
-/

@[expose] public section

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

namespace MatrixMap

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable {κ 𝕜 : Type*} [Fintype κ] [RCLike 𝕜]

section tp

variable {R : Type*} [Semiring R]
variable {M : MatrixMap A B R} {M₂ : MatrixMap B C R}

/-- A linear matrix map is *trace preserving* if trace of the output equals trace of the input. -/
def IsTracePreserving (M : MatrixMap A B R) : Prop :=
  ∀ (x : Matrix A A R), (M x).trace = x.trace

set_option backward.isDefEq.respectTransparency false in
/-- A map is trace preserving iff the partial trace of the Choi matrix is the identity. -/
theorem IsTracePreserving_iff_trace_choi [DecidableEq A] (M : MatrixMap A B R) : M.IsTracePreserving
    ↔ M.choi_matrix.traceLeft = 1 := by
  constructor
  · intro h
    ext a₁ a₂
    replace h := h (Matrix.single a₁ a₂ 1)
    simp_rw [Matrix.trace, Matrix.diag] at h
    simp only [Matrix.traceLeft, choi_matrix, Matrix.of_apply, h]
    simp only [Matrix.single, Matrix.of_apply, Finset.sum_boole, Matrix.one_apply]
    have : (fun x => a₁ = x ∧ a₂ = x) = (fun x => a₁ = a₂ ∧ a₂ = x) := by
      funext x
      rw [eq_iff_iff, and_congr_left_iff]
      rintro rfl
      trivial
    split_ifs with h
    <;> simp [this, h, Finset.filter_eq]
  · intro h X
    replace h := fun (a₁ a₂ : A) ↦ congrFun₂ h a₁ a₂
    simp [Matrix.traceLeft, Matrix.trace] at h ⊢
    rw [← M.choi_map_inv, of_choi_matrix]
    dsimp
    rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle]
    simp_rw [← Finset.mul_sum, h, Matrix.one_apply]
    simp

namespace IsTracePreserving

/-- Simp lemma: the trace of the image of a IsTracePreserving map is the same as the original
trace. -/
@[simp]
theorem apply_trace (h : M.IsTracePreserving) (ρ : Matrix A A R)
    : (M ρ).trace = ρ.trace :=
  h ρ

/-- The trace of a Choi matrix of a TP map is the cardinality of the input space. -/
theorem trace_choi [DecidableEq A] (h : M.IsTracePreserving) :
    M.choi_matrix.trace = (Finset.univ (α := A)).card := by
  rw [← Matrix.traceLeft_trace, (IsTracePreserving_iff_trace_choi M).mp h,
    Matrix.trace_one, Finset.card_univ]

/-- The composition of IsTracePreserving maps is also trace preserving. -/
theorem comp (h₁ : M.IsTracePreserving) (h₂ : M₂.IsTracePreserving) :
    IsTracePreserving (M₂ ∘ₗ M) := by
  intro x
  simp [h₂ _, h₁ _]

/-- The identity MatrixMap IsTracePreserving. -/
@[simp]
theorem id : (id A R).IsTracePreserving := by
  simp [IsTracePreserving, MatrixMap.id]

variable {R : Type*} [CommSemiring R] in
/-- Unit linear combinations of IsTracePreserving maps are IsTracePreserving. -/
theorem unit_linear {M₁ M₂ : MatrixMap A B R} {x y : R}
    (h₁ : M₁.IsTracePreserving) (h₂ : M₂.IsTracePreserving) (hxy : x + y = 1) :
    (x • M₁ + y • M₂).IsTracePreserving := by
  rw [IsTracePreserving] at h₁ h₂ ⊢
  simp [h₁, h₂, ← add_mul, hxy]

variable {R : Type*} [CommSemiring R] [DecidableEq C] [DecidableEq A] in
/-- The kronecker product of IsTracePreserving maps is also trace preserving. -/
theorem kron {M₁ : MatrixMap A B R} {M₂ : MatrixMap C D R} (h₁ : M₁.IsTracePreserving) (h₂ : M₂.IsTracePreserving) :
    (M₁ ⊗ₖₘ M₂).IsTracePreserving := by
  intro x
  simp_rw [Matrix.trace, Matrix.diag]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [kron_def]
  have h_simp : ∑ x_1, ∑ x_2, ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂,
    M₁ (Matrix.single a₁ a₂ 1) x_1 x_1 * M₂ (Matrix.single c₁ c₂ 1) x_2 x_2 * x (a₁, c₁) (a₂, c₂) =
      ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂, (if a₁ = a₂ then 1 else 0) * (if c₁ = c₂ then 1 else 0) * x (a₁, c₁) (a₂, c₂) := by
    --Sort the sum into AACCBD order
    simp only [@Finset.sum_comm A _ D, @Finset.sum_comm A _ B, @Finset.sum_comm C _ B, @Finset.sum_comm C _ D]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    congr! 8 with a₁ _ a₂ _ c₁ _ c₂ _
    · refine (h₁ _).trans ?_
      split_ifs with h
      · subst h
        exact Matrix.trace_single_eq_same _ _
      · exact Matrix.trace_single_eq_of_ne _ _ _ h
    · refine (h₂ _).trans ?_
      split_ifs with h
      · subst h
        exact Matrix.trace_single_eq_same _ _
      · exact Matrix.trace_single_eq_of_ne _ _ _ h
  simp [h_simp]

variable {S : Type*} [CommSemiring S] [Star S] [DecidableEq A] in
/-- The channel X ↦ ∑ k : κ, (M k) * X * (N k)ᴴ formed by Kraus operators M, N : κ → Matrix B A R
is trace-preserving if ∑ k : κ, (N k)ᴴ * (M k) = 1 -/
theorem of_kraus_isTracePreserving
  (M N : κ → Matrix B A S)
  (hTP : (∑ k, (N k).conjTranspose * (M k)) = 1) :
  (MatrixMap.of_kraus M N).IsTracePreserving := by
  intro x
  simp only [of_kraus, LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.trace_sum]
  conv =>
    enter [1,2,i]
    rw [Matrix.trace_mul_cycle (M i) x (N i).conjTranspose]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hTP, one_mul]

/-- `MatrixMap.submatrix` is trace-preserving when the function is an equivalence. -/
theorem submatrix (e : A ≃ B) : (MatrixMap.submatrix R e).IsTracePreserving := by
  intro; simp

section piProd

variable {R : Type*} [CommSemiring R]
variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable {dI : ι → Type v} [∀i, Fintype (dI i)] [∀i, DecidableEq (dI i)]
variable {dO : ι → Type w} [∀i, Fintype (dO i)] [∀i, DecidableEq (dO i)]

omit [(i : ι) → DecidableEq (dO i)] in
/-- The `MatrixMap.piProd` product of trace-preserving maps is trace preserving. -/
theorem piProd {Λi : ∀ i, MatrixMap (dI i) (dO i) R} (h : ∀ i, (Λi i).IsTracePreserving) :
    (MatrixMap.piProd Λi).IsTracePreserving := by
  intro x
  conv_lhs => rw [Matrix.matrix_eq_sum_single x]
  conv_rhs => rw [Matrix.matrix_eq_sum_single x]
  simp only [map_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [show Matrix.single a b (x a b) = x a b • Matrix.single a b (1 : R) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  rw [map_smul, Matrix.trace_smul, Matrix.trace_smul]
  congr 1
  rw [MatrixMap.piProd_single, Matrix.trace_piProd, ← Matrix.piProd_single a b,
    Matrix.trace_piProd]
  exact Finset.prod_congr rfl fun i _ ↦ h i _

end piProd

end IsTracePreserving
end tp


section unital

variable [DecidableEq A] [DecidableEq B] [Semiring R]

/-- A linear matrix map is *unital* if it preserves the identity. -/
def Unital (M : MatrixMap A B R) : Prop :=
  M 1 = 1

namespace Unital

variable {M : MatrixMap A B R}

omit [Fintype A] [Fintype B]

@[simp]
theorem map_1 (h : M.Unital) : M 1 = 1 :=
  h

/-- The identity `MatrixMap` is `Unital`. -/
@[simp]
theorem id : (id A R).Unital := by
  simp [Unital, MatrixMap.id]

--TODO: Closed under composition, kronecker products, it's iff M.choi_matrix.traceLeft = 1...

end Unital
end unital

variable {A B C R : Type*}

open Kronecker
open TensorProduct

open ComplexOrder
variable [RCLike R]

/-- A linear matrix map is *Hermitian preserving* if it maps `IsHermitian` matrices to `IsHermitian`.-/
def IsHermitianPreserving (M : MatrixMap A B R) : Prop :=
  ∀⦃x⦄, x.IsHermitian → (M x).IsHermitian

/-- A linear matrix map is *positive* if it maps `PosSemidef` matrices to `PosSemidef`.-/
def IsPositive [Fintype A] [Fintype B] (M : MatrixMap A B R) : Prop :=
  ∀⦃x⦄, x.PosSemidef → (M x).PosSemidef

/-- A linear matrix map is *completely positive* if, for any integer n, the tensor product
with `I(n)` is positive. -/
def IsCompletelyPositive [Fintype A] [Fintype B] [DecidableEq A] (M : MatrixMap A B R) : Prop :=
  ∀ (n : ℕ), (M ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n) (Fin n) R)).IsPositive

namespace IsHermitianPreserving

variable {A : Type*} [Fintype A] in
/-- The identity MatrixMap IsHermitianPreserving. -/
theorem id : (id A R).IsPositive :=
  fun _ h ↦ h

/-- The composition of IsHermitianPreserving maps is also Hermitian preserving. -/
theorem comp {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R}
    (h₁ : M₁.IsHermitianPreserving) (h₂ : M₂.IsHermitianPreserving) : IsHermitianPreserving (M₂ ∘ₗ M₁) :=
  fun _ h ↦ h₂ (h₁ h)

end IsHermitianPreserving

namespace IsPositive
variable [Fintype A] [Fintype B] [Fintype C]

/- Every `MatrixMap` that `IsPositive` is also `IsHermitianPreserving`. -/
theorem IsHermitianPreserving {M : MatrixMap A B R}
    (hM : IsPositive M) : IsHermitianPreserving M := by
  intro x hx
  let xH : HermitianMat _ _ := ⟨x, hx⟩
  classical --because PosPart requires DecidableEq
  have hMPos := hM (HermitianMat.zero_le_iff.mp xH.posPart_nonneg)
  have hMNeg := hM (HermitianMat.zero_le_iff.mp xH.negPart_nonneg)
  have hSub := hMPos.isHermitian.sub hMNeg.isHermitian
  rw [← map_sub] at hSub
  convert ← hSub
  exact HermitianMat.ext_iff.1 (HermitianMat.posPart_add_negPart xH)

/-- The composition of IsPositive maps is also positive. -/
theorem comp {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R} (h₁ : M₁.IsPositive)
    (h₂ : M₂.IsPositive) : IsPositive (M₂ ∘ₗ M₁) :=
  fun _ h ↦ h₂ (h₁ h)

variable {A : Type*} [Fintype A] in
/-- The identity MatrixMap IsPositive. -/
@[simp]
theorem id : (id A R).IsPositive :=
  fun _ h ↦ h

/-- Sums of IsPositive maps are IsPositive. -/
theorem add {M₁ M₂ : MatrixMap A B R} (h₁ : M₁.IsPositive) (h₂ : M₂.IsPositive) :
    (M₁ + M₂).IsPositive :=
  fun _ h ↦ Matrix.PosSemidef.add (h₁ h) (h₂ h)

/-- Nonnegative scalings of IsPositive maps are IsPositive. -/
theorem smul {M : MatrixMap A B R} (hM : M.IsPositive) {x : R} (hx : 0 ≤ x) :
    (x • M).IsPositive :=
  fun _ h ↦ (hM h).smul hx

section Contraction

variable {M : MatrixMap A B ℂ}

/-- A positive map, viewed as a map on Hermitian matrices. -/
noncomputable def herm (hM : M.IsPositive) (X : HermitianMat A ℂ) : HermitianMat B ℂ :=
  ⟨M X.mat, hM.IsHermitianPreserving X.H⟩

@[simp]
theorem mat_herm (hM : M.IsPositive) (X : HermitianMat A ℂ) : (hM.herm X).mat = M X.mat :=
  rfl

/-- A positive map is monotone for the Loewner order. -/
theorem herm_mono (hM : M.IsPositive) {X Y : HermitianMat A ℂ} (h : X ≤ Y) :
    hM.herm X ≤ hM.herm Y := by
  rw [HermitianMat.le_iff] at h ⊢
  have hsub : (hM.herm Y - hM.herm X).mat = M ((Y - X).mat) := by
    rw [HermitianMat.mat_sub, HermitianMat.mat_sub, map_sub, mat_herm, mat_herm]
  rw [hsub]
  exact hM h

/-- On positive semidefinite inputs, a trace-preserving positive map preserves the trace norm,
because the trace norm of a positive semidefinite matrix is its trace. -/
theorem traceNorm_map_eq_trace (hM : M.IsPositive) (hTP : M.IsTracePreserving)
    {X : HermitianMat A ℂ} (hX : 0 ≤ X) : (M X.mat).traceNorm = X.trace := by
  have hpsd : (M X.mat).PosSemidef := hM (HermitianMat.zero_le_iff.mp hX)
  have h := hpsd.traceNorm_eq_trace
  rw [hTP X.mat, ← HermitianMat.trace_eq_trace_rc] at h
  exact_mod_cast h

variable [DecidableEq A]

/-- A positive trace-preserving map is a contraction in the trace norm, on Hermitian inputs.

The Jordan decomposition `X = X⁺ - X⁻` reduces this to the positive semidefinite case, where the
trace norm is the trace and so is exactly preserved. -/
theorem traceNorm_le (hM : M.IsPositive) (hTP : M.IsTracePreserving) (X : HermitianMat A ℂ) :
    (M X.mat).traceNorm ≤ X.mat.traceNorm :=
  calc (M X.mat).traceNorm = (M (X⁺).mat - M (X⁻).mat).traceNorm := by
        rw [← map_sub, ← HermitianMat.mat_sub, HermitianMat.posPart_add_negPart]
    _ ≤ (M (X⁺).mat).traceNorm + (M (X⁻).mat).traceNorm := Matrix.traceNorm_sub_le _ _
    _ = (X⁺).trace + (X⁻).trace := by
        rw [hM.traceNorm_map_eq_trace hTP X.posPart_nonneg,
          hM.traceNorm_map_eq_trace hTP X.negPart_nonneg]
    _ = X.mat.traceNorm := (HermitianMat.traceNorm_eq_trace_posPart_add_negPart X).symm

variable [DecidableEq B]

theorem herm_smul_one (hM : M.IsPositive) (hu : M.Unital) (c : ℝ) :
    hM.herm (c • 1) = c • 1 := by
  apply HermitianMat.ext
  rw [mat_herm, HermitianMat.mat_smul, HermitianMat.mat_one, HermitianMat.mat_smul,
    HermitianMat.mat_one, LinearMap.map_smul_of_tower, hu.map_1]

/-- A positive unital map is a contraction in the operator norm, on Hermitian inputs: it maps the
Loewner order interval `[-c, c]` into itself. -/
theorem mem_Icc_smul_one_of_unital (hM : M.IsPositive) (hu : M.Unital) {X : HermitianMat A ℂ}
    {c : ℝ} (h₁ : -(c • 1) ≤ X) (h₂ : X ≤ c • 1) :
    -(c • 1) ≤ hM.herm X ∧ hM.herm X ≤ c • 1 := by
  have hneg : hM.herm ((-c) • 1) = -(c • 1) := by
    rw [hM.herm_smul_one hu, neg_smul]
  refine ⟨hneg ▸ hM.herm_mono ?_, hM.herm_smul_one hu c ▸ hM.herm_mono h₂⟩
  rw [neg_smul]
  exact h₁

end Contraction

end IsPositive

namespace IsCompletelyPositive
variable [Fintype A] [Fintype B] [Fintype C] [DecidableEq A]

/-- Definition of a CP map, but with `Fintype T` in the definition instead of a `Fin n`. -/
theorem of_Fintype  {M : MatrixMap A B R} (h : IsCompletelyPositive M)
    (T : Type*) [Fintype T] [DecidableEq T] :
    (M.kron (LinearMap.id : MatrixMap T T R)).IsPositive := by
  obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty (T ≃ Fin n) :=
    Finite.exists_equiv_fin T
  convert h n using 1
  have h_submatrix : (M ⊗ₖₘ (LinearMap.id : MatrixMap T T R)) = (MatrixMap.submatrix R (fun p : B × T => (p.1, e p.2)) ∘ₗ (M ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n) (Fin n) R)) ∘ₗ MatrixMap.submatrix R (fun p : A × Fin n => (p.1, e.symm p.2))) := by
    ext
    simp only [submatrix, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Matrix.submatrix_apply]
    rw [MatrixMap.kron_def, MatrixMap.kron_def]
    simp only [Matrix.single, LinearMap.id_coe, id_eq, Matrix.of_apply, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Matrix.submatrix];
    congr! 4
    rw [← Equiv.sum_comp e]
    congr! 2
    rw [← Equiv.sum_comp e]
    simp only [EmbeddingLike.apply_eq_iff_eq, Equiv.symm_apply_apply]
  constructor
  · intro h₂
    simp [MatrixMap.IsPositive]
    exact h n
  · intro h x hx
    specialize h (hx.submatrix (fun p : A × Fin n => (p.1, e.symm p.2)))
    rw [h_submatrix]
    simp only [LinearMap.coe_comp, Function.comp_apply, submatrix_apply]
    exact h.submatrix _

/- Every `MatrixMap` that `IsCompletelyPositive` also `IsPositiveMap`. -/
theorem IsPositive {M : MatrixMap A B R}
    (hM : IsCompletelyPositive M) : IsPositive M := by
  intro x hx
  let x' : Matrix (A × Fin 1) (A × Fin 1) R := x ⊗ₖ 1
  let eqA : (A × Fin 1) ≃ A :=
    (Equiv.prodCongrRight (fun _ ↦ finOneEquiv)).trans (Equiv.prodPUnit A)
  let eqB : (B × Fin 1) ≃ B :=
    (Equiv.prodCongrRight (fun _ ↦ finOneEquiv)).trans (Equiv.prodPUnit B)
  specialize @hM 1 (x.submatrix eqA eqA) (Matrix.PosSemidef.submatrix hx _)
  convert Matrix.PosSemidef.submatrix hM eqB.symm; clear hM
  --TODO Cleanup
  ext i j
  simp only [Matrix.submatrix, Matrix.of_apply]
  rw [MatrixMap.kron_def]
  suffices h : M x = ∑ a₁, ∑ a₂, x a₁ a₂ • M (Matrix.single a₁ a₂ 1) by
    simp [h, Matrix.sum_apply, Matrix.single, eqA, eqB]
    ac_rfl
  simp only [← M.map_smul, ← map_sum]
  congr
  ext k l
  simp [Matrix.sum_apply, Matrix.single]
  rw [Finset.sum_eq_single k]
  · simp
  · simp +contextual
  · simp +contextual

/-- The composition of IsCompletelyPositive maps is also completely positive. -/
theorem comp [DecidableEq B] {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R} (h₁ : M₁.IsCompletelyPositive)
    (h₂ : M₂.IsCompletelyPositive) : IsCompletelyPositive (M₂ ∘ₗ M₁) := by
  --sketch: (M₂ ∘ₗ M₁) ⊗ₖₘ id[n] = (M₂ ⊗ₖₘ id[n]) ∘ₗ (M₁ ⊗ₖₘ id[n]), which is a composition of positive maps.
  intro n x hx
  specialize h₁ n hx
  specialize h₂ n h₁
  conv in LinearMap.id =>
    change LinearMap.id ∘ₗ LinearMap.id
  rw [kron_comp_distrib]
  simpa using h₂

/-- The identity MatrixMap IsCompletelyPositive. -/
@[simp]
theorem id : (id A R).IsCompletelyPositive := by
  intro n ρ h
  rwa [show LinearMap.id = MatrixMap.id (Fin n) R from rfl, kron_id_id]

/-- Sums of IsCompletelyPositive maps are IsCompletelyPositive. -/
theorem add {M₁ M₂ : MatrixMap A B R} (h₁ : M₁.IsCompletelyPositive) (h₂ : M₂.IsCompletelyPositive) :
    (M₁ + M₂).IsCompletelyPositive :=
  fun n _ h ↦ by
  simp only [add_kron, LinearMap.add_apply]
  exact Matrix.PosSemidef.add (h₁ n h) (h₂ n h)

/-- Nonnegative scalings of `IsCompletelyPositive` maps are `IsCompletelyPositive`. -/
theorem smul {M : MatrixMap A B R} (hM : M.IsCompletelyPositive) {x : R} (hx : 0 ≤ x) :
    (x • M).IsCompletelyPositive :=
  fun n ρ h ↦ by
    rw [MatrixMap.smul_kron]
    exact (hM n h).smul hx

variable (A B) in
/-- The zero map `IsCompletelyPositive`. -/
theorem zero : (0 : MatrixMap A B R).IsCompletelyPositive :=
  fun _ _ _ ↦ by simpa using Matrix.PosSemidef.zero

/-- A finite sum of completely positive maps is completely positive. -/
theorem finset_sum {ι : Type*} [Fintype ι] {m : ι → MatrixMap A B R} (hm : ∀ i, (m i).IsCompletelyPositive) :
    (∑ i, m i).IsCompletelyPositive :=
  Finset.sum_induction m _ (fun _ _ ↦ add) (.zero A B) (by simpa)

end IsCompletelyPositive

variable [Fintype A] [Fintype B] [Fintype C] [DecidableEq A]
variable {d : Type*} [Fintype d]

open MatrixOrder

/-- The map that takes M and returns M ⊗ₖ C, where C is positive semidefinite, is a completely
  positive map. -/
theorem kron_kronecker_const {C : Matrix d d R} (h : C.PosSemidef) {h₁ h₂ : _} : IsCompletelyPositive
    (⟨⟨fun M => M ⊗ₖ C, h₁⟩, h₂⟩ : MatrixMap A (A × d) R) := by
  intros n x hx
  have h_kronecker_pos : (x ⊗ₖ C).PosSemidef := by
    -- Since $x$ and $C$ are positive semidefinite, there exist matrices $U$ and $V$ such that
    -- $x = U^*U$ and $C = V^*V$.
    obtain ⟨U, hU⟩ : ∃ U : Matrix (A × Fin n) (A × Fin n) R, x = star U * U := by
      classical
      apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
      exact Matrix.nonneg_iff_posSemidef.mpr hx
    obtain ⟨V, hV⟩ : ∃ V : Matrix d d R, C = star V * V := by
      classical
      apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
      exact Matrix.nonneg_iff_posSemidef.mpr h
    -- $W = (U \otimes V)^* (U \otimes V)$ is positive semidefinite.
    have hW_pos : (U ⊗ₖ V).conjTranspose * (U ⊗ₖ V) = x ⊗ₖ C := by
      rw [Matrix.kroneckerMap_conjTranspose, ← Matrix.mul_kronecker_mul]
      rw [hU, hV, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
    rw [ ← hW_pos ]
    exact Matrix.posSemidef_conjTranspose_mul_self (U ⊗ₖ V)
  --TODO clean up this mess (but, thanks Aristotle)
  convert h_kronecker_pos.submatrix (fun (⟨ ⟨ a, d' ⟩, n' ⟩ : (A × d) × Fin n) => ⟨ ⟨ a, n' ⟩, d' ⟩) using 1;
  ext ⟨⟨a, d⟩, n⟩ ⟨⟨a', d'⟩, n'⟩
  simp [Matrix.kroneckerMap_apply, Matrix.submatrix_apply]
  erw [MatrixMap.kron_def]
  simp [Matrix.single, Matrix.kroneckerMap_apply]
  simp [Finset.sum_ite, Finset.filter_eq', Finset.filter_and]
  rw [ Finset.sum_eq_single a ]
  · simp_all only [RingHom.id_apply, ↓reduceIte, Finset.mem_univ, Finset.inter_singleton_of_mem, Finset.sum_singleton]
    rw [ Finset.sum_eq_single n ]
    · simp_all only [↓reduceIte, Finset.mem_univ, Finset.inter_singleton_of_mem, Finset.sum_singleton]
      ring
    · intro b a_1 a_2
      simp_all only [Finset.mem_univ, ne_eq, ↓reduceIte, Finset.notMem_empty, not_false_eq_true,
        Finset.inter_singleton_of_notMem, Finset.sum_empty]
    · intro a_1
      simp_all only [Finset.mem_univ, not_true_eq_false]
  · intro b a_1 a_2
    simp_all only [RingHom.id_apply, Finset.mem_univ, ne_eq, ↓reduceIte, Finset.notMem_empty, not_false_eq_true,
      Finset.inter_singleton_of_notMem, Finset.sum_empty]
  · intro a_1
    simp_all only [RingHom.id_apply, Finset.mem_univ, not_true_eq_false]

omit [Fintype B] in
theorem choi_of_kraus (K : κ → Matrix B A 𝕜) :
    (MatrixMap.of_kraus K K).choi_matrix = ∑ k, Matrix.vecMulVec (fun (x : B × A) => K k x.1 x.2) (fun (x : B × A) => star (K k x.1 x.2)) := by
  -- By definition of Choi matrix, we can expand the left-hand side using the linearity of the map and the properties of the Choi matrix.
  ext ⟨b₁, a₁⟩ ⟨b₂, a₂⟩
  simp [MatrixMap.choi_matrix, MatrixMap.of_kraus];
  -- By definition of the sum, the entry (b₁, b₂) of the sum of the Choi matrices of each Kraus operator is the sum of the entries (b₁, b₂) of each individual Choi matrix.
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.single];
  -- Since the inner sum over `x_2` will only contribute when `x_2 = a₁` and `x_1 = a₂`, we can simplify the expression.
  have h_inner : ∀ x : κ, ∑ x_1 : A, (∑ x_2 : A, if a₁ = x_2 ∧ a₂ = x_1 then K x b₁ x_2 else 0) * (starRingEnd 𝕜) (K x b₂ x_1) = (K x b₁ a₁) * (starRingEnd 𝕜) (K x b₂ a₂) := by
    simp [ Finset.sum_ite, Finset.filter_eq, Finset.filter_and ];
    intro x; rw [ Finset.sum_eq_single a₂ ] <;> aesop;
  exact Finset.sum_congr rfl fun _ _ => h_inner _

/-- The linear map of conjugating a matrix by another, `x → y * x * yᴴ`. -/
@[simps]
def _root_.MatrixMap.conj (y : Matrix B A R) : MatrixMap A B R where
  toFun x := y * x * y.conjTranspose
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq A] in
theorem conj_isPositive (M : Matrix B A 𝕜) : (conj M).IsPositive := by
  exact fun X hX => hX.mul_mul_conjTranspose_same M

omit [DecidableEq A] in
theorem IsPositive_sum {ι : Type*} [Fintype ι] (f : ι → MatrixMap A B ℂ) (h : ∀ i, (f i).IsPositive) :
    (∑ i, f i).IsPositive := by
  intro X hX;
  replace hX : ∀ i, ((f i) X).PosSemidef := fun i => h i hX;
  simp [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian] at hX ⊢
  simp [Matrix.conjTranspose_sum, Matrix.mulVec, dotProduct] at hX ⊢
  simp [Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul] at hX ⊢
  constructor
  · simp [hX]
  field_simp
  simp_rw [mul_assoc, mul_comm ((f _) X _ _), ← mul_assoc]
  intro x
  rw [Finset.sum_comm_cycle]
  exact Finset.sum_nonneg fun i _ => by simpa [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] using hX i |>.2 x;

omit [DecidableEq A] in
theorem of_kraus_isPositive (K : κ → Matrix B A ℂ) :
    (of_kraus K K).IsPositive := by
  rw [of_kraus]
  apply IsPositive_sum
  intro k
  exact conj_isPositive (K k)

theorem conj_kron (M : Matrix B A 𝕜) (N : Matrix D C 𝕜) [DecidableEq C] :
    conj M ⊗ₖₘ conj N = conj (M ⊗ₖ N) := by
  apply LinearMap.ext
  intro x
  have h_eq : ∀ (X : Matrix A A 𝕜) (Y : Matrix C C 𝕜), (conj M ⊗ₖₘ conj N) (X ⊗ₖ Y) = (conj (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) M N)) (X ⊗ₖ Y) := by
    intro X Y;
    convert MatrixMap.kron_map_of_kron_state _ _ X Y using 1;
    ext ⟨ b₁, d₁ ⟩ ⟨ b₂, d₂ ⟩
    simp only [Matrix.kroneckerMap]
    ring_nf
    simp only [conj, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply, star_mul', RCLike.star_def]
    simp only [mul_left_comm, mul_comm, Finset.mul_sum, mul_assoc]
    simp only [← Finset.univ_product_univ, ← Finset.sum_product'];
    apply Finset.sum_bij (fun x _ ↦ (x.1.2, x.2.2, x.1.1, x.2.1)) <;> simp
  -- By linearity, it suffices to show that the maps agree on a basis.
  have h_basis : ∀ (x : Matrix (A × C) (A × C) 𝕜), x ∈ Submodule.span 𝕜 (Set.range (fun (p : Matrix A A 𝕜 × Matrix C C 𝕜) => p.1 ⊗ₖ p.2)) → (conj M ⊗ₖₘ conj N) x = (conj (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) M N)) x := by
    intro x hx;
    induction hx using Submodule.span_induction;
    · rename_i h
      simp only [Set.mem_range, Prod.exists] at h
      obtain ⟨w, ⟨w', rfl⟩⟩ := h
      apply h_eq
    · simp [conj];
    · simp_all only [map_add]
    · simp_all only [map_smul]
  convert h_basis x _;
  -- By definition of matrix multiplication and the properties of the Kronecker product, we can express any matrix as a sum of Kronecker products of basis matrices.
  have h_decomp : ∀ (x : Matrix (A × C) (A × C) 𝕜), ∃ (coeffs : A → C → A → C → 𝕜), x = ∑ a₁, ∑ c₁, ∑ a₂, ∑ c₂, coeffs a₁ c₁ a₂ c₂ • Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (Matrix.single a₁ a₂ 1) (Matrix.single c₁ c₂ 1) := by
    intro x
    use fun a₁ c₁ a₂ c₂ => x (a₁, c₁) (a₂, c₂);
    ext ⟨ a₁, c₁ ⟩ ⟨ a₂, c₂ ⟩
    simp only [Matrix.single]
    simp only [Matrix.sum_apply, Matrix.kroneckerMap]
    rw [ Finset.sum_eq_single a₁ ] <;> simp [Finset.sum_ite]
    · rw [ Finset.sum_eq_single c₁ ] <;> simp +contextual
      rw [ Finset.sum_eq_single c₂ ] <;> simp +contextual;
    · simp +contextual [Finset.filter_eq', Finset.filter_and ];
  obtain ⟨ coeffs, rfl ⟩ := h_decomp x;
  exact Submodule.sum_mem _ fun a₁ _ => Submodule.sum_mem _ fun c₁ _ => Submodule.sum_mem _ fun a₂ _ => Submodule.sum_mem _ fun c₂ _ => Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ ( Matrix.single a₁ a₂ 1, Matrix.single c₁ c₂ 1 ), rfl ⟩ )

theorem congruence_one_eq_id : conj (1 : Matrix A A ℂ) = MatrixMap.id A ℂ := by
  ext x
  simp [conj]

theorem congruence_CP {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (M : Matrix B A 𝕜) : (conj M).IsCompletelyPositive := by
  intro n;
  -- The tensor product of congruence maps is a congruence map.
  have h_tensor_congruence : conj M ⊗ₖₘ LinearMap.id = conj (M ⊗ₖ (1 : Matrix (Fin n) (Fin n) 𝕜)) := by
    convert conj_kron M ( 1 : Matrix ( Fin n ) ( Fin n ) 𝕜 );
    ext M
    simp
  convert conj_isPositive ( M ⊗ₖ ( 1 : Matrix ( Fin n ) ( Fin n ) 𝕜 ) ) using 1

theorem IsCompletelyPositive_sum {ι : Type*} [Fintype ι] (f : ι → MatrixMap A B ℂ) (h : ∀ i, (f i).IsCompletelyPositive) :
    (∑ i, f i).IsCompletelyPositive := by
      convert IsCompletelyPositive.finset_sum h using 1

omit [Fintype B] [DecidableEq A] in
theorem of_kraus_eq_sum_conj (K : κ → Matrix B A 𝕜) :
    of_kraus K K = ∑ k, conj (K k) := by
  ext
  simp [MatrixMap.of_kraus, conj]

theorem of_kraus_CP (K : κ → Matrix B A 𝕜) : (of_kraus K K).IsCompletelyPositive := by
  -- By definition of `MatrixMap.of_kraus`, we know that it is a sum of congruence maps.
  have h_sum_congruence : MatrixMap.of_kraus K K = ∑ k, conj (K k) := by
    -- By definition of `MatrixMap.of_kraus`, we know that it is equal to the sum of the congruence maps of each Kraus operator.
    apply of_kraus_eq_sum_conj
  have h_congruence_CP : ∀ k, (conj (K k)).IsCompletelyPositive := by
    intro k; exact (by
    convert congruence_CP ( K k ) using 1;
    -- Since B is a finite type, we can use the fact that finite types have decidable equality.
    apply Classical.decEq);
  exact h_sum_congruence.symm ▸ IsCompletelyPositive.finset_sum h_congruence_CP

set_option backward.isDefEq.respectTransparency false in
theorem exists_kraus_of_choi_PSD
    (C : Matrix (B × A) (B × A) 𝕜) (hC : C.PosSemidef) :
    ∃ (K : (B × A) → Matrix B A 𝕜), C = (MatrixMap.of_kraus K K).choi_matrix := by
  classical
  use fun k i j => ( hC.1.eigenvectorUnitary.val : Matrix _ _ 𝕜 ) (i, j) k * ( hC.1.eigenvalues k |> RCLike.ofReal |> Real.sqrt)
  convert Matrix.IsHermitian.spectral_theorem hC.1 using 1;
  ext i j
  simp [choi_of_kraus, Matrix.mul_apply, Matrix.vecMulVec ]
  ring_nf
  simp [ Matrix.sum_apply, Matrix.diagonal ];
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [ ← RCLike.ofReal_pow, Real.sq_sqrt ( hC.eigenvalues_nonneg _ ) ]

/-
The Choi matrix of M is the image of the unnormalized maximally entangled state projector under M ⊗ id.
-/
theorem choi_matrix_eq_map_proj (M : MatrixMap A B R) :
    M.choi_matrix = (M ⊗ₖₘ MatrixMap.id A R) (Matrix.vecMulVec (fun (x : A × A) => if x.1 = x.2 then 1 else 0) (fun (x : A × A) => star (if x.1 = x.2 then 1 else 0))) := by
  have h_choi : ∀ (M : MatrixMap A B R), MatrixMap.kron M (MatrixMap.id A R) (Matrix.vecMulVec (fun (x : A × A) => if x.1 = x.2 then 1 else 0) (fun (x : A × A) => star (if x.1 = x.2 then 1 else 0))) = MatrixMap.choi_matrix M := by
    intro M
    ext ⟨b₁, d₁⟩ ⟨b₂, d₂⟩
    simp [MatrixMap.kron_def, MatrixMap.choi_matrix];
    simp +decide [ Matrix.single, Matrix.vecMulVec ];
    rw [ Finset.sum_eq_single d₁ ] <;> aesop;
  convert h_choi M |> Eq.symm

/-- Choi's theorem on completely positive maps: A map `IsCompletelyPositive` iff its Choi Matrix is PSD. -/
theorem choi_PSD_iff_CP_map (M : MatrixMap A B R) :
    M.IsCompletelyPositive ↔ M.choi_matrix.PosSemidef := by
  constructor
  · intro hcp
    have := MatrixMap.IsCompletelyPositive.of_Fintype hcp A
    rw [ MatrixMap.choi_matrix_eq_map_proj ] at *;
    exact this ( Matrix.PosSemidef.outer_self_conj _ )
  · intro h_psd
    obtain ⟨K, hK⟩ := exists_kraus_of_choi_PSD M.choi_matrix h_psd
    rw [choi_matrix_inj hK]
    exact of_kraus_CP K

omit [Fintype B] [DecidableEq A] in
theorem conj_eq_mulRightLinearMap_comp_mulRightLinearMap (y : Matrix B A R) :
    conj y = mulRightLinearMap B R y.conjTranspose ∘ₗ mulLeftLinearMap A R y := by
  ext1; simp

set_option backward.isDefEq.respectTransparency false in
/-- The act of conjugating (not necessarily by a unitary, just by any matrix at all) is completely positive. -/
theorem conj_isCompletelyPositive (M : Matrix B A R) : (conj M).IsCompletelyPositive := by
  --TODO: This is identical to congruence_CP
  intro n m h
  classical
  open ComplexOrder in
  open Kronecker in
  suffices ((M ⊗ₖ 1 : Matrix (B × Fin n) (A × Fin n) R) * m * (M.conjTranspose ⊗ₖ 1)).PosSemidef by
    convert this
    --TODO cleanup. Thanks Aristotle
    ext ⟨ b₁, c₁ ⟩ ⟨ b₂, c₂ ⟩
    rw [ MatrixMap.kron_def ];
    simp [Matrix.mul_apply, Matrix.single];
    have h_split : ∑ x, ∑ x_1, ∑ x_2, ∑ x_3, (if x_2 = c₁ ∧ x_3 = c₂ then (∑ x_4, (∑ x_5, if x = x_5 ∧ x_1 = x_4 then M b₁ x_5 else 0) * (starRingEnd R) (M b₂ x_4)) * m (x, x_2) (x_1, x_3) else 0) = ∑ x, ∑ x_1, (∑ x_4, (∑ x_5, if x = x_5 ∧ x_1 = x_4 then M b₁ x_5 else 0) * (starRingEnd R) (M b₂ x_4)) * m (x, c₁) (x_1, c₂) := by
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      rw [ Finset.sum_eq_single c₁ ]
      · simp_all only [Finset.mem_univ, true_and, Finset.sum_ite_eq', ↓reduceIte]
      · intro b a a_1
        simp_all only [Finset.mem_univ, ne_eq, false_and, ↓reduceIte, Finset.sum_const_zero]
      · intro a
        simp_all only [Finset.mem_univ, not_true_eq_false]
    convert h_split using 1;
    rw [ Matrix.mul_assoc ];
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
      RCLike.star_def, Finset.mul_sum _ _ _, Finset.sum_mul, ite_mul, zero_mul];
    simp [ Matrix.one_apply, Finset.sum_ite, Finset.filter_eq, Finset.filter_and ];
    have h_reindex : ∑ x ∈ {x | c₁ = x.2}, ∑ x_1 ∈ {x | x.2 = c₂}, M b₁ x.1 * (m x x_1 * (starRingEnd R) (M b₂ x_1.1)) = ∑ x ∈ Finset.univ, ∑ x_1 ∈ Finset.univ, M b₁ x * (m (x, c₁) (x_1, c₂) * (starRingEnd R) (M b₂ x_1)) := by
      rw [ show ( Finset.univ.filter fun x : A × Fin n => c₁ = x.2 ) = Finset.image ( fun x : A => ( x, c₁ ) ) Finset.univ from ?_, show ( Finset.univ.filter fun x : A × Fin n => x.2 = c₂ ) = Finset.image ( fun x : A => ( x, c₂ ) ) Finset.univ from ?_ ];
      · simp [Finset.sum_image, Set.InjOn]
      · ext ⟨ x, y ⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq,
          exists_eq_left]
        exact eq_comm;
      · ext ⟨ x, y ⟩
        simp [ eq_comm ];
    have h_inner : ∀ x x_1, ∑ x_2, ∑ x_3 ∈ {x} ∩ if x_1 = x_2 then Finset.univ else ∅, M b₁ x_3 * (starRingEnd R) (M b₂ x_2) * m (x, c₁) (x_1, c₂) = M b₁ x * (starRingEnd R) (M b₂ x_1) * m (x, c₁) (x_1, c₂) := by
      intro x x_1
      rw [ Finset.sum_eq_single x_1 ] <;> simp +contextual;
      simp +contextual [ eq_comm ];
    simp only [ h_inner ];
    simpa only [ mul_assoc, mul_comm, mul_left_comm ] using h_reindex
  obtain ⟨m', rfl⟩ : ∃ B, m = B.conjTranspose * B := by
    classical
    apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    exact Matrix.nonneg_iff_posSemidef.mpr h
  convert Matrix.posSemidef_conjTranspose_mul_self (m' * (M ⊗ₖ 1 : Matrix (B × Fin n) (A × Fin n) R).conjTranspose) using 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  congr
  ext
  simp +contextual only [Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    Matrix.one_apply, apply_ite, mul_one, mul_zero, star_zero, ↓reduceIte, ite_eq_right_iff,
    map_eq_zero, if_true_left]
  tauto

/-- `MatrixMap.submatrix` is completely positive -/
theorem IsCompletelyPositive.submatrix (f : B → A) : (MatrixMap.submatrix R f).IsCompletelyPositive := by
  convert conj_isCompletelyPositive (Matrix.submatrix (α := R) 1 f _root_.id : Matrix B A R)
  ext1 m
  simp [m.submatrix_eq_mul_mul]

/-- The channel X ↦ ∑ k : κ, (M k) * X * (M k)ᴴ formed by Kraus operators M : κ → Matrix B A R
is completely positive -/
theorem of_kraus_isCompletelyPositive (M : κ → Matrix B A R) :
    (of_kraus M M).IsCompletelyPositive := by
  rw [of_kraus]
  exact IsCompletelyPositive.finset_sum (fun i ↦ conj_isCompletelyPositive (M i))

omit [Fintype B] [DecidableEq A] in
/--
The Choi matrix of a map in symmetric Kraus form is a sum of rank-1 projectors.
-/
theorem choi_of_kraus_R [DecidableEq A] (K : κ → Matrix B A 𝕜) :
    (of_kraus K K).choi_matrix = ∑ k, Matrix.vecMulVec (fun (x : B × A) => K k x.1 x.2) (fun (x : B × A) => star (K k x.1 x.2)) := by
  unfold of_kraus choi_matrix
  ext i j : 2
  simp only [LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    Matrix.vecMulVec, Matrix.of_apply]
  simp only [Matrix.single, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  simp +contextual only [Finset.sum_ite, Finset.filter_and, Finset.filter_const, not_and,
    Finset.sum_const_zero, add_zero];
  congr! with k
  simp_all only [Finset.mem_univ, Finset.filter_eq, ↓reduceIte]
  rw [Finset.sum_eq_single j.2]
  · simp
  · aesop
  · simp

/-
The Choi matrix of M is the result of applying M \otimes I to the unnormalized maximally entangled state (Choi matrix of identity).
-/
variable {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [RCLike R]

theorem choi_eq_kron_id_apply_choi_id (M : MatrixMap A B R) :
    M.choi_matrix = (M ⊗ₖₘ MatrixMap.id A R) ((MatrixMap.id A R).choi_matrix) := by
  ext ⟨j₁, a₁⟩ ⟨j₂, a₂⟩ : 2
  rw [ MatrixMap.kron_def ]
  simp only [choi_matrix, Matrix.single, LinearMap.id_coe, id_eq, Matrix.of_apply, mul_ite, mul_one,
    mul_zero]
  simp only [← Finset.sum_filter, Finset.filter_and, Finset.filter_const, Finset.filter_eq',
    Finset.mem_univ, ↓reduceIte, Finset.mem_inter, Finset.mem_singleton, Finset.sum_const,
    nsmul_eq_mul]
  rw [ Finset.sum_eq_single a₁ ]
  · simp +contextual only [↓reduceIte, Finset.inter_singleton_of_mem]
    rw [ Finset.sum_eq_single a₂, Finset.sum_eq_single a₁ ]
    · simp
    · simp +contextual
    · intro h
      simp at h
    · intro b _ hb
      rw [Finset.sum_eq_zero]
      aesop
    · simp
  · simp +contextual only
    intro b a
    split_ifs with h <;> simp [h]
  · simp +contextual

/-
The Choi matrix of the identity map is positive semidefinite.
-/
theorem choi_id_is_PSD {A R : Type*} [Fintype A] [DecidableEq A] [RCLike R] :
    (MatrixMap.id A R).choi_matrix.PosSemidef := by
  -- Let $v$ be the vector with $v_{(a,b)} = \delta_{ab}$.
  set v : A × A → R := fun p => if p.1 = p.2 then 1 else 0;
  -- By definition of $C$, we know that $C = v v^*$.
  have hC : (MatrixMap.id A R).choi_matrix = Matrix.of (fun (i j : A × A) => v i * star (v j)) := by
    ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp [ MatrixMap.choi_matrix, Matrix.single ] ; aesop;
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine' ⟨ _, fun x => _ ⟩;
  · ext i j; aesop;
  · -- By definition of $v$, we know that $star x ⬝ᵥ v v^* x = |star x ⬝ᵥ v|^2$.
    have h_inner : star x ⬝ᵥ (MatrixMap.id A R).choi_matrix.mulVec x = star (star x ⬝ᵥ v) * (star x ⬝ᵥ v) := by
      simp [ hC, Matrix.mulVec, dotProduct ];
      simp [ Finset.mul_sum, mul_comm, v]
      exact Finset.sum_congr rfl fun i hi => by split_ifs <;> simp [ * ] ;
    rw [ h_inner, mul_comm ];
    exact mul_star_self_nonneg (star x ⬝ᵥ v)

/-
If a map is completely positive, its Choi matrix is positive semidefinite.
-/
theorem is_CP_implies_choi_PSD {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [RCLike R] (M : MatrixMap A B R) (hCP : M.IsCompletelyPositive) :
    M.choi_matrix.PosSemidef := by
  rw [choi_eq_kron_id_apply_choi_id]
  exact MatrixMap.IsCompletelyPositive.of_Fintype hCP A choi_id_is_PSD

theorem IsCompletelyPositive.exists_kraus (Φ : MatrixMap A B R) (hCP : Φ.IsCompletelyPositive) :
    ∃ (M : (B × A) → Matrix B A R), Φ = of_kraus M M := by
  rw [choi_PSD_iff_CP_map] at hCP
  convert exists_kraus_of_choi_PSD Φ.choi_matrix hCP using 1;
  funext
  rw [eq_iff_iff, iff_comm]
  exact MatrixMap.choi_matrix_inj.eq_iff

open scoped MatrixOrder in
/-- Kadison-Schwarz for completely positive subunital matrix maps. -/
theorem cp_subunital_kadison_schwarz {M : MatrixMap A B ℂ} [DecidableEq B]
    (hM : M.IsCompletelyPositive) (hM1 : M 1 ≤ (1 : Matrix B B ℂ))
    (X : Matrix A A ℂ) :
    (M X)ᴴ * M X ≤ M (Xᴴ * X) := by
  have hblock :
      (Matrix.fromBlocks (M 1) (M X) ((M X)ᴴ) (M (Xᴴ * X))).PosSemidef := by
    classical
    obtain ⟨K, rfl⟩ := MatrixMap.IsCompletelyPositive.exists_kraus _ hM
    rw [MatrixMap.of_kraus_eq_sum_conj]
    convert Matrix.posSemidef_sum Finset.univ (fun k _ => by
      simpa [MatrixMap.conj, Matrix.mul_assoc] using
        Matrix.fromBlocks_gram_posSemidef (X * (K k)ᴴ) (K k)ᴴ) using 1
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.conjTranspose_sum,
        Matrix.mul_assoc]
  have hgap_block :
      (Matrix.fromBlocks (1 - M 1) 0 0 (0 : Matrix B B ℂ)).PosSemidef := by
    have hnonneg : (0 : Matrix B B ℂ) ≤ 1 - M 1 := by simpa [sub_nonneg] using hM1
    rw [← show (CFC.sqrt (1 - M 1))ᴴ * CFC.sqrt (1 - M 1) = 1 - M 1 from by
      rw [show (CFC.sqrt (1 - M 1))ᴴ = CFC.sqrt (1 - M 1) from by
        simpa using (CFC.sqrt_nonneg (1 - M 1)).1.eq]
      exact CFC.sqrt_mul_sqrt_self (1 - M 1) hnonneg]
    simpa using Matrix.fromBlocks_gram_posSemidef
      (0 : Matrix B B ℂ) (CFC.sqrt (1 - M 1))
  have hsum :
      (Matrix.fromBlocks (1 : Matrix B B ℂ) (M X) ((M X)ᴴ) (M (Xᴴ * X))).PosSemidef := by
    convert hblock.add hgap_block using 1
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.fromBlocks, sub_eq_add_neg, add_left_comm, add_comm]
  let : Invertible (1 : Matrix B B ℂ) := invertibleOne
  have h1 :=
    (Matrix.PosDef.fromBlocks₁₁ (B := M X) (D := M (Xᴴ * X))
      (hA := (Matrix.PosDef.one : (1 : Matrix B B ℂ).PosDef))).mp hsum
  simp_all only [inv_one, mul_one, ge_iff_le]
  exact h1

open scoped MatrixOrder in
/-- A positive subunital matrix map is contractive on positive inputs. -/
theorem positive_subunital_norm_apply_le {M : MatrixMap A B ℂ} [DecidableEq B]
    (hM : M.IsPositive) (hM1 : M 1 ≤ (1 : Matrix B B ℂ))
    {X : Matrix A A ℂ} (hX : 0 ≤ X) :
    ‖M X‖ ≤ ‖X‖ := by
  let eA := Matrix.toEuclideanCLM (n := A) (𝕜 := ℂ)
  let eB := Matrix.toEuclideanCLM (n := B) (𝕜 := ℂ)
  have hXle : X ≤ ‖X‖ • (1 : Matrix A A ℂ) := by
    refine (map_le_map_iff eA).mp ?_
    have h := IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg (map_nonneg eA hX))
    have hs : algebraMap ℝ (EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) ‖eA X‖ =
        eA (‖X‖ • (1 : Matrix A A ℂ)) := by
      rw [Algebra.algebraMap_eq_smul_one]
      ext x i
      change (((‖X‖ : ℂ) • x).ofLp i) =
        (((‖X‖ : ℂ) • (1 : Matrix A A ℂ)) *ᵥ x.ofLp) i
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, WithLp.ofLp_smul]
    exact h.trans_eq hs
  have hMX_le : M X ≤ ‖X‖ • (1 : Matrix B B ℂ) :=
    (show M X ≤ ‖X‖ • M 1 by
      simpa [sub_nonneg, map_sub, map_smul] using
        (hM (by exact hXle :
          (‖X‖ • (1 : Matrix A A ℂ) - X).PosSemidef)).nonneg).trans
      (smul_le_smul_of_nonneg_left hM1 (norm_nonneg X))
  have hMX_nn : 0 ≤ M X := (hM (by simpa [Matrix.nonneg_iff_posSemidef] using hX)).nonneg
  have hone : ‖(1 : Matrix B B ℂ)‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial (Matrix B B ℂ) with h | h
    · simp [Subsingleton.elim (1 : Matrix B B ℂ) 0]
    · exact CStarRing.norm_one.le
  refine (CStarAlgebra.norm_le_norm_of_nonneg_of_le (map_nonneg eB hMX_nn)
    ((map_le_map_iff eB).mpr hMX_le)).trans ?_
  change ‖‖X‖ • (1 : Matrix B B ℂ)‖ ≤ ‖X‖
  rw [show (‖X‖ • (1 : Matrix B B ℂ)) = ((‖X‖ : ℂ) • (1 : Matrix B B ℂ)) by ext; simp, norm_smul]
  simpa using mul_le_mul_of_nonneg_left hone (norm_nonneg X)

open scoped MatrixOrder in
/-- A completely positive subunital matrix map is contractive in operator norm. -/
theorem cp_subunital_opNorm_le_one {M : MatrixMap A B ℂ} [DecidableEq B]
    (hM : M.IsCompletelyPositive) (hM1 : M 1 ≤ (1 : Matrix B B ℂ))
    (X : Matrix A A ℂ) :
    ‖M X‖ ≤ ‖X‖ := by
  refine (sq_le_sq₀ (norm_nonneg (M X)) (norm_nonneg X)).mp ?_
  simp only [sq, ← CStarRing.norm_star_mul_self, Matrix.star_eq_conjTranspose]
  let e := Matrix.toEuclideanCLM (n := B) (𝕜 := ℂ)
  exact (CStarAlgebra.norm_le_norm_of_nonneg_of_le
      (map_nonneg e (star_mul_self_nonneg (M X)))
      ((map_le_map_iff e).mpr (cp_subunital_kadison_schwarz hM hM1 X))).trans
    (positive_subunital_norm_apply_le hM.IsPositive hM1 (star_mul_self_nonneg X))

/--
The Kronecker product of two Kraus maps is the Kraus map of the Kronecker products of the operators.
-/
theorem kron_of_kraus {A B C D R : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq C] [CommSemiring R] [StarRing R] [SMulCommClass R R R]
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (M : κ → Matrix B A R) (N : ι → Matrix D C R) :
    of_kraus M M ⊗ₖₘ of_kraus N N =
    of_kraus (fun (k : κ × ι) => M k.1 ⊗ₖ N k.2) (fun k => M k.1 ⊗ₖ N k.2) := by
  open Classical
  in convert MatrixMap.choi_map_inv _ using 1;
  rotate_left
  · infer_instance
  · infer_instance
  rw [choi_map_inv]
  apply MatrixMap.choi_matrix_inj
  ext ⟨ b, a ⟩ ⟨ d, c ⟩
  simp only [of_kraus] ;
  simp only [choi_matrix, LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
  rw [ MatrixMap.kron_def ]
  simp only [LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    star_mul'] ;
  simp only [Matrix.single, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite, not_and,
    Finset.sum_const_zero, add_zero, ne_eq];
  simp only [Finset.sum_sigma', Finset.univ_sigma_univ];
  simp only [mul_comm, Finset.mul_sum, Finset.sum_sigma', mul_left_comm, mul_assoc];
  refine Finset.sum_bij ( fun x _ => ⟨ ⟨ ⟨ x.snd.snd.fst.fst, x.snd.fst.fst.fst ⟩, x.snd.snd.fst.snd, x.snd.fst.fst.snd ⟩, x.snd.snd.snd, x.snd.fst.snd ⟩ ) ?_ ?_ ?_ ?_
  · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, and_imp]
    grind
  · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, Sigma.mk.injEq,
      Prod.mk.injEq, heq_eq_eq, and_imp]
    grind
  · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, exists_prop,
      Sigma.exists, existsAndEq, and_true, exists_and_left, and_imp]
    grind
  · simp

namespace IsCompletelyPositive

/-- The Kronecker product of IsCompletelyPositive maps is also completely positive. -/
theorem kron {D : Type*} [DecidableEq C] [Fintype D] {M₁ : MatrixMap A B R} {M₂ : MatrixMap C D R}
    (h₁ : M₁.IsCompletelyPositive) (h₂ : M₂.IsCompletelyPositive) : IsCompletelyPositive (M₁ ⊗ₖₘ M₂) := by
  obtain ⟨K₁, rfl⟩ := exists_kraus M₁ h₁
  obtain ⟨K₂, rfl⟩ := exists_kraus M₂ h₂
  rw [kron_of_kraus K₁ K₂]
  apply of_kraus_isCompletelyPositive

section piProd

variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀i, Fintype (dI i)] [∀i, DecidableEq (dI i)]
variable {dO : ι → Type w} [∀i, Fintype (dO i)] [∀i, DecidableEq (dO i)]

/-- The `MatrixMap.piProd` product of IsCompletelyPositive maps is also completely positive. -/
theorem piProd {Λi : ∀ i, MatrixMap (dI i) (dO i) R} (h₁ : ∀ i, (Λi i).IsCompletelyPositive) :
    IsCompletelyPositive (MatrixMap.piProd Λi) := by
  rw [choi_PSD_iff_CP_map, MatrixMap.choi_matrix_piProd]
  convert! Matrix.PosSemidef.submatrix
    (Matrix.PosSemidef.piProd (fun i => (choi_PSD_iff_CP_map (Λi i)).1 (h₁ i)))
    (Equiv.arrowProdEquivProdArrow ι dO dI).symm using 1

end piProd

end IsCompletelyPositive

end MatrixMap
