/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Operators.Unitary

/-! # Completely Positive Trace Preserving maps

A `CPTPMap` is a `ℂ`-linear map between matrices (`MatrixMap` is an alias), bundled with the facts that it
`IsCompletelyPositive` and `IsTracePreserving`. CPTP maps are typically regarded as the "most general
quantum operation", as they map density matrices (`MState`s) to density matrices. The type `PTPMap`,
for maps that are positive (but not necessarily completely positive) is also declared.

A large portion of the theory is in terms of the Choi matrix (`MatrixMap.choi_matrix`), as the
positive-definiteness of this matrix corresponds to being a CP map. This is
[Choi's theorem on CP maps](https://en.wikipedia.org/wiki/Choi%27s_theorem_on_completely_positive_maps).

This file also defines several important examples of, classes of, and operations on, CPTPMaps:
 * `compose`: Composition of maps
 * `id`: The identity map
 * `replacement`: The replacement channel that always outputs the same state
 * `prod`: Tensor product of two CPTP maps, with notation M₁ ⊗ M₂
 * `piProd`: Tensor product of finitely many CPTP maps (Pi-type product)
 * `of_unitary`: The CPTP map corresponding to a unitary operation `U`
 * `IsUnitary`: Predicate whether the map corresponds to any unitary
 * `purify`: Purifying a channel into a unitary on a larger Hilbert space
 * `complementary`: The complementary channel to its purification
 * `IsEntanglementBreaking`, `IsDegradable`, `IsAntidegradable`: Entanglement breaking, degradable
    and antidegradable channels.
 * `SWAP`, `assoc`, `assoc'`, `traceLeft`, `traceRight`: The CPTP maps corresponding to important
    operations on states. These correspond directly to `MState.SWAP`, `MState.assoc`, `MState.assoc'`,
    `MState.traceLeft`, and `MState.traceRight`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

variable {dIn dOut dOut₂ : Type*} [Fintype dIn] [Fintype dOut] [Fintype dOut₂]
variable [DecidableEq dIn] [DecidableEq dOut] [DecidableEq dOut₂]

namespace CPTPOp
noncomputable section
open scoped Matrix ComplexOrder

variable {dM : Type*} [Fintype dM] [DecidableEq dM]
variable {dM₂ : Type*} [Fintype dM₂] [DecidableEq dM₂]
variable (Λ : CPTPMap dIn dOut)

/-- The Choi matrix of a CPTPOp. -/
@[reducible]
def choi := Λ.map.choi_matrix

/-- Two CPTPMaps are equal if their Choi matrices are equal. -/
theorem choi_ext {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : Λ₁.choi = Λ₂.choi) : Λ₁ = Λ₂ :=
  ext_map (MatrixMap.choi_equiv.injective h)

/-- The Choi matrix of a channel is PSD. -/
theorem choi_PSD_of_CPTP : Λ.map.choi_matrix.PosSemidef :=
  Λ.map.choi_PSD_iff_CP_map.1 Λ.map_cp

/-- The trace of a Choi matrix of a CPTP map is the cardinality of the input space. -/
@[simp]
theorem Tr_of_choi_of_CPTP : Λ.choi.trace =
    (Finset.univ (α := dIn)).card :=
  Λ.map_TP.trace_choi

/-- Construct a CPTP map from a PSD Choi matrix with correct partial trace. -/
def CPTP_of_choi_PSD_Tr {M : Matrix (dOut × dIn) (dOut × dIn) ℂ} (h₁ : M.PosSemidef)
    (h₂ : M.traceLeft = 1) : CPTPMap dIn dOut :=
  ofMat (MatrixMap.of_choi_matrix M)
    ((MatrixMap.choi_PSD_iff_CP_map (MatrixMap.of_choi_matrix M)).2
      ((MatrixMap.map_choi_inv M).symm ▸ h₁))
    ((MatrixMap.of_choi_matrix M).IsTracePreserving_iff_trace_choi.2
      ((MatrixMap.map_choi_inv M).symm ▸ h₂))

@[simp]
theorem map_CPTP_of_choi_PSD_Tr {M : Matrix (dOut × dIn) (dOut × dIn) ℂ} {h₁} {h₂} :
    (CPTP_of_choi_PSD_Tr (M := M) h₁ h₂).map = MatrixMap.of_choi_matrix M :=
  map_ofMat _ _ _

@[simp]
theorem choi_of_CPTP_of_choi (M : Matrix (dOut × dIn) (dOut × dIn) ℂ) {h₁} {h₂} :
    (CPTP_of_choi_PSD_Tr (M := M) h₁ h₂).choi = M := by
  simp only [choi, map_CPTP_of_choi_PSD_Tr]
  rw [MatrixMap.map_choi_inv]

theorem mat_coe_eq_apply_mat (ρ : MState dIn) : (Λ ρ).m = Λ.map ρ.m :=
  congrArg HermitianMat.mat (PTPOp.M_apply_MState Λ.toPTPOp ρ)

omit [DecidableEq dIn] [DecidableEq dOut] in
@[ext]
theorem funext {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : ∀ ρ, Λ₁ ρ = Λ₂ ρ) : Λ₁ = Λ₂ :=
  DFunLike.ext _ _ h

/-- The composition of CPTPMaps, as a CPTPOp. -/
def compose (Λ₂ : CPTPMap dM dOut) (Λ₁ : CPTPMap dIn dM) : CPTPMap dIn dOut where
  toLinearMap := Λ₂.toLinearMap ∘ₗ Λ₁.toLinearMap
  cp := Λ₁.cp.comp Λ₂.cp
  TP := Λ₁.TP.comp Λ₂.TP

infixl:75 "∘ₘ" => CPTPOp.compose

/-- **Matrix analogue of composition**: the matrix of a composition is the composition of the
matrices. -/
@[simp]
theorem compose_map (Λ₂ : CPTPMap dM dOut) (Λ₁ : CPTPMap dIn dM) :
    (Λ₂ ∘ₘ Λ₁).map = Λ₂.map ∘ₗ Λ₁.map :=
  OpMap.toMat_comp _ _

/-- Composition of CPTPMaps by `CPTPOp.compose` is compatible with the `instFunLike` action. -/
@[simp]
theorem compose_eq {Λ₁ : CPTPMap dIn dM} {Λ₂ : CPTPMap dM dOut} :
    ∀ ρ, (Λ₂ ∘ₘ Λ₁) ρ = Λ₂ (Λ₁ ρ) := fun ρ ↦ by
  apply DensityOp.ext_m
  rw [mat_coe_eq_apply_mat, mat_coe_eq_apply_mat, mat_coe_eq_apply_mat, compose_map]
  rfl

/-- Composition of CPTPMaps is associative. -/
theorem compose_assoc (Λ₃ : CPTPMap dM₂ dOut) (Λ₂ : CPTPMap dM dM₂)
    (Λ₁ : CPTPMap dIn dM) : (Λ₃ ∘ₘ Λ₂) ∘ₘ Λ₁ = Λ₃ ∘ₘ (Λ₂ ∘ₘ Λ₁) := by
  ext1 ρ
  simp

/-- CPTPMaps have a convex structure from their Choi matrices. -/
instance instMixable : Mixable (Matrix (dOut × dIn) (dOut × dIn) ℂ) (CPTPMap dIn dOut) where
  to_U := CPTPOp.choi
  to_U_inj := choi_ext
  mkT {u} h := ⟨CPTP_of_choi_PSD_Tr (M := u)
    (Exists.recOn h fun t ht => ht ▸ t.choi_PSD_of_CPTP)
    (Exists.recOn h fun t ht => (by
      rw [← ht, ← MatrixMap.IsTracePreserving_iff_trace_choi]
      exact t.map_TP)),
    by apply choi_of_CPTP_of_choi⟩
  convex := by
    have h_convex : ∀ (M₁ M₂ : Matrix (dOut × dIn) (dOut × dIn) ℂ), M₁.PosSemidef → M₂.PosSemidef → ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → (t • M₁ + (1 - t) • M₂).PosSemidef := by
      intro M₁ M₂ h₁ h₂ t ht₁ ht₂;
      convert Matrix.PosSemidef.add ( h₁.smul ht₁ ) ( h₂.smul ( sub_nonneg.mpr ht₂ ) ) using 1;
    intro M hM N hN a b ha hb hab;
    obtain ⟨Λ₁, hΛ₁⟩ := hM
    obtain ⟨Λ₂, hΛ₂⟩ := hN;
    obtain ⟨Λ, hΛ⟩ : ∃ Λ : MatrixMap dIn dOut ℂ, (a • M + b • N).traceLeft = 1 ∧ (a • M + b • N).PosSemidef ∧ Λ = MatrixMap.of_choi_matrix (a • M + b • N) := by
      refine ⟨_, ?_, ?_, rfl⟩
      · have h_trace_M : M.traceLeft = 1 := by
          convert Λ₁.map_TP using 1;
          rw [ ← hΛ₁, MatrixMap.IsTracePreserving_iff_trace_choi ]
        have h_trace_N : N.traceLeft = 1 := by
          convert Λ₂.map_TP using 1;
          rw [ ← hΛ₂, MatrixMap.IsTracePreserving_iff_trace_choi ]
        convert congr_arg₂ ( fun x y : Matrix dIn dIn ℂ => a • x + b • y ) h_trace_M h_trace_N using 1;
        · ext i j
          simp [ Matrix.traceLeft ]
          simp only [Finset.sum_add_distrib, Finset.mul_sum _ _ _];
        · rw [ ← add_smul, hab, one_smul ];
      · convert h_convex M N ( by simpa [ ← hΛ₁ ] using Λ₁.choi_PSD_of_CPTP ) ( by simpa [ ← hΛ₂ ] using Λ₂.choi_PSD_of_CPTP ) a ha ( by linarith ) using 1 ; rw [ ← hab ]
        ring_nf
    use CPTP_of_choi_PSD_Tr hΛ.2.1 hΛ.1;
    exact choi_of_CPTP_of_choi (a • M + b • N)

/-- The identity channel, which leaves the input unchanged. -/
def id : CPTPMap dIn dIn where
  toLinearMap := LinearMap.id
  cp := OpMap.isCompletelyPositive_id
  TP := OpMap.isTracePreserving_id

/-- The map `CPTPOp.id` leaves any matrix unchanged. -/
@[simp]
theorem id_map : (id (dIn := dIn)).map = LinearMap.id :=
  OpMap.toMat_id

/-- The map `CPTPOp.id` leaves the input state unchanged. -/
@[simp]
theorem id_MState (ρ : MState dIn) : CPTPOp.id (dIn := dIn) ρ = ρ := by
  apply DensityOp.ext_m
  rw [mat_coe_eq_apply_mat]
  simp

/-- The map `CPTPOp.id` composed with any map is the same map. -/
@[simp]
theorem id_compose (Λ : CPTPMap dIn dOut) : id ∘ₘ Λ = Λ := by
  apply funext
  simp

/-- Any map composed with `CPTPOp.id` is the same map. -/
@[simp]
theorem compose_id (Λ : CPTPMap dIn dOut) : Λ ∘ₘ id = Λ := by
  classical ext1
  simp

section equiv

/-- Given a equivalence (a bijection) between the types d₁ and d₂, that is, if they're
 the same dimension, then there's a CPTP channel for this. This is what we need for
 defining e.g. the SWAP channel, which is 'unitary' but takes heterogeneous input
 and outputs types (d₁ × d₂) and (d₂ × d₁). -/
def ofEquiv (σ : dIn ≃ dOut) : CPTPMap dIn dOut :=
  ofMat (MatrixMap.submatrix ℂ σ.symm) (.submatrix σ.symm)
    (fun x ↦ by rw [MatrixMap.IsTracePreserving.submatrix])

@[simp]
theorem ofEquiv_map (σ : dIn ≃ dOut) :
    (ofEquiv σ).map = MatrixMap.submatrix ℂ σ.symm :=
  map_ofMat _ _ _

@[simp]
theorem ofEquiv_apply (σ : dIn ≃ dOut) (ρ : MState dIn) :
    ofEquiv σ ρ = ρ.relabel σ.symm := by
  apply DensityOp.ext_m
  rw [mat_coe_eq_apply_mat, ofEquiv_map, MState.relabel_m]
  rfl

@[simp]
theorem equiv_inverse (σ : dIn ≃ dOut)  : (ofEquiv σ) ∘ (ofEquiv σ.symm) = id (dIn := dOut) := by
  ext1; simp

variable {d₁ d₂ d₃ : Type*} [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]

--TODO: of_equiv (id) = id
--(of_equiv σ).compose (of_equiv τ) = of_equiv (σ ∘ τ)

/-- The SWAP operation, as a channel. -/
def SWAP : CPTPMap (d₁ × d₂) (d₂ × d₁) :=
  ofEquiv (Equiv.prodComm d₁ d₂)

/-- The associator, as a channel. -/
def assoc : CPTPMap ((d₁ × d₂) × d₃) (d₁ × d₂ × d₃) :=
  ofEquiv (Equiv.prodAssoc d₁ d₂ d₃)

/-- The inverse associator, as a channel. -/
def assoc' : CPTPMap (d₁ × d₂ × d₃) ((d₁ × d₂) × d₃) :=
  ofEquiv (Equiv.prodAssoc d₁ d₂ d₃).symm

@[simp]
theorem SWAP_eq_MState_SWAP (ρ : MState (d₁ × d₂)) : SWAP (d₁ := d₁) (d₂ := d₂) ρ = ρ.SWAP :=
  ofEquiv_apply _ _

@[simp]
theorem assoc_eq_MState_assoc (ρ : MState ((d₁ × d₂) × d₃)) : assoc (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) ρ = ρ.assoc :=
  ofEquiv_apply _ _

@[simp]
theorem assoc'_eq_MState_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    assoc' (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) ρ = ρ.assoc' := by
  apply DensityOp.ext_m
  rw [assoc', ofEquiv_apply]
  ext i j
  simp [MState.assoc', MState.assoc, MState.SWAP]

@[simp]
theorem assoc_assoc' : (assoc (d₁ := d₁) (d₂ := d₂) (d₃ := d₃)) ∘ₘ assoc' = id := by
  ext1 ρ
  simp

end equiv

section trace
variable {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]

--TODO: make Matrix.traceLeft a linear map, a `MatrixMap`.
/-- Partial tracing out the left, as a `MatrixMap`. -/
def traceLeftₘ (d : Type*) [Fintype d] [DecidableEq d] :
    Matrix (d₁ × d) (d₁ × d) ℂ →ₗ[ℂ] Matrix d d ℂ where
  toFun x := Matrix.traceLeft x
  map_add' := by
    intros; ext
    simp [Matrix.traceLeft, Finset.sum_add_distrib]
  map_smul' := by
    intros; ext
    simp [Matrix.traceLeft, Finset.mul_sum]

theorem traceLeftₘ_cp :
    MatrixMap.IsCompletelyPositive (traceLeftₘ (d₁ := d₁) d₂) := by
  --(traceLeft ⊗ₖₘ I) = traceLeft ∘ₘ (ofEquiv prod_assoc)
  --Both go (A × B) × C → B × C
  --So then it suffices to show both are positive, and we have PosSemidef.traceLeft already.
  intro n
  classical
  suffices MatrixMap.IsPositive
      (traceLeftₘ (d₁ := d₁) (d₂ × Fin n) ∘ₗ
        (MatrixMap.submatrix ℂ (Equiv.prodAssoc d₁ d₂ (Fin n)).symm)) by
    convert this
    ext
    rw [MatrixMap.kron_def]
    simp [traceLeftₘ, Matrix.submatrix, Matrix.single, ite_and, Matrix.traceLeft,
      Fintype.sum_prod_type]
  apply MatrixMap.IsPositive.comp
  · exact (MatrixMap.IsCompletelyPositive.submatrix _).IsPositive
  · intro x h
    exact h.traceLeft

/-- Partial tracing out the left, as a CPTP map. -/
def traceLeft : CPTPMap (d₁ × d₂) d₂ :=
  ofMat (traceLeftₘ d₂) traceLeftₘ_cp (by intro; simp [traceLeftₘ])

@[simp]
theorem traceLeft_map : (traceLeft (d₁ := d₁) (d₂ := d₂)).map = traceLeftₘ d₂ :=
  map_ofMat _ _ _

/-- Partial tracing out the right, as a CPTP map. -/
def traceRight : CPTPMap (d₁ × d₂) d₁ :=
  traceLeft ∘ₘ SWAP

@[simp]
theorem traceLeft_eq_MState_traceLeft (ρ : MState (d₁ × d₂)) :
    traceLeft (d₁ := d₁) (d₂ := d₂) ρ = ρ.traceLeft := by
  apply DensityOp.ext_m
  rw [mat_coe_eq_apply_mat, traceLeft_map, MState.traceLeft_m]
  rfl

@[simp]
theorem traceRight_eq_MState_traceRight (ρ : MState (d₁ × d₂)) :
    traceRight (d₁ := d₁) (d₂ := d₂) ρ = ρ.traceRight := by
  rw [traceRight, compose_eq, SWAP_eq_MState_SWAP, traceLeft_eq_MState_traceLeft,
    MState.traceLeft_SWAP]

end trace

/-- The matrix map that appends a fixed state `ρ` on the right. -/
def appendₘ (ρ : MState dOut) : MatrixMap dIn (dIn × dOut) ℂ where
  toFun M := Matrix.kroneckerMap (fun x1 x2 => x1 * x2) M ρ.m
  map_add' := by simp [Matrix.add_kronecker]
  map_smul' := by simp [Matrix.smul_kronecker]

/--The replacement channel that maps all inputs to a given state. -/
def replacement [Nonempty dIn] (ρ : MState dOut) : CPTPMap dIn dOut :=
  traceLeft ∘ₘ ofMat (appendₘ ρ) (MatrixMap.kron_kronecker_const ρ.psd)
    (by intro; simp [appendₘ, Matrix.trace_kronecker])

/-- **Matrix analogue of the replacement channel**: it sends `M` to `M.trace • ρ`. -/
@[simp]
theorem replacement_map [Nonempty dIn] (ρ : MState dOut) (M : Matrix dIn dIn ℂ) :
    (replacement ρ).map M = M.trace • ρ.m := by
  simp only [replacement, compose_map, LinearMap.comp_apply, traceLeft_map, map_ofMat,
    traceLeftₘ, appendₘ, LinearMap.coe_mk, AddHom.coe_mk]
  ext i j
  simp [Matrix.traceLeft, Matrix.kroneckerMap, Matrix.trace, ← Finset.sum_mul]

/-- The output of `replacement ρ` is always that `ρ`. -/
@[simp]
theorem replacement_apply [Nonempty dIn] (ρ : MState dOut) (ρ₀ : MState dIn) :
    replacement (dIn := dIn) ρ ρ₀ = ρ := by
  apply DensityOp.ext_m
  rw [mat_coe_eq_apply_mat, replacement_map, ρ₀.tr', one_smul]

--In principle we can relax the `Nonempty dIn`: for the case where `IsEmpty dIn`, we just take the
-- 0 map, and it's CPTP.
instance [Nonempty dIn] [Nonempty dOut] : Inhabited (CPTPMap dIn dOut) :=
  ⟨replacement default⟩

instance [Nonempty dIn] [Nonempty dOut] : Nonempty (CPTPMap dIn dOut) := by
  classical infer_instance

/-- There is a CPTP map that takes a system of any (nonzero) dimension and outputs the
trivial Hilbert space, 1-dimensional, indexed by any `Unique` type. We can think of this
as "destroying" the whole system; tracing out everything. -/
def destroy [Nonempty dIn] [Unique dOut] : CPTPMap dIn dOut :=
  replacement default

omit [DecidableEq dIn] in
/-- Two CPTP maps into the same one-dimensional output space must be equal -/
theorem eq_if_output_unique [Unique dOut] (Λ₁ Λ₂ : CPTPMap dIn dOut) : Λ₁ = Λ₂ :=
  funext fun _ ↦ (Unique.eq_default _).trans (Unique.eq_default _).symm

/-- There is exactly one CPTPMap to a 1-dimensional space. -/
instance instUnique [Nonempty dIn] [Unique dOut] : Unique (CPTPMap dIn dOut) where
  default := destroy
  uniq := fun _ ↦ eq_if_output_unique _ _

@[simp]
theorem destroy_comp {dOut₂ : Type*} [Unique dOut₂] [DecidableEq dOut₂] [Nonempty dIn] [Nonempty dOut]
  (Λ : CPTPMap dIn dOut) :
    destroy (dOut := dOut₂) ∘ₘ Λ = destroy :=
  Unique.eq_default _

section prod
open Kronecker

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂] [Fintype dO₁] [Fintype dO₂]
variable [DecidableEq dI₁] [DecidableEq dI₂] [DecidableEq dO₁] [DecidableEq dO₂]

set_option maxRecDepth 1000 in -- ??? what the heck is recursing
/-- The tensor product of two CPTPMaps. -/
def prod (Λ₁ : CPTPMap dI₁ dO₁) (Λ₂ : CPTPMap dI₂ dO₂) : CPTPMap (dI₁ × dI₂) (dO₁ × dO₂) :=
  ofMat (Λ₁.map.kron Λ₂.map) (Λ₁.map_cp.kron Λ₂.map_cp) (Λ₁.map_TP.kron Λ₂.map_TP)

infixl:70 "⊗ᶜᵖ" => CPTPOp.prod

/-- **Matrix analogue of the tensor product**: the matrix of a product is the Kronecker product
of the matrices. -/
@[simp]
theorem prod_map (Λ₁ : CPTPMap dI₁ dO₁) (Λ₂ : CPTPMap dI₂ dO₂) :
    (Λ₁ ⊗ᶜᵖ Λ₂).map = Λ₁.map.kron Λ₂.map :=
  map_ofMat _ _ _

/-- Tensor products commute with channel application:
`(Λ₁ ⊗ᶜᵖ Λ₂) (ρ₁ ⊗ᴹ ρ₂) = Λ₁ ρ₁ ⊗ᴹ Λ₂ ρ₂`. -/
@[simp]
theorem prod_apply_prod (Λ₁ : CPTPMap dI₁ dO₁) (Λ₂ : CPTPMap dI₂ dO₂)
    (ρ₁ : MState dI₁) (ρ₂ : MState dI₂) :
    (Λ₁ ⊗ᶜᵖ Λ₂) (ρ₁ ⊗ᴹ ρ₂) = (Λ₁ ρ₁) ⊗ᴹ (Λ₂ ρ₂) := by
  apply DensityOp.ext_m
  rw [mat_coe_eq_apply_mat, prod_map, MState.prod_m, MState.prod_m, mat_coe_eq_apply_mat,
    mat_coe_eq_apply_mat]
  exact MatrixMap.kron_map_of_kron_state Λ₁.map Λ₂.map ρ₁.m ρ₂.m

end prod

section finprod

variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀(i :ι), Fintype (dI i)] [∀(i :ι), DecidableEq (dI i)]
variable {dO : ι → Type w} [∀(i :ι), Fintype (dO i)] [∀(i :ι), DecidableEq (dO i)]

/-- Finitely-indexed tensor products of CPTPMaps.  -/
def piProd (Λi : (i:ι) → CPTPMap (dI i) (dO i)) : CPTPMap ((i:ι) → dI i) ((i:ι) → dO i) :=
  ofMat (MatrixMap.piProd (fun i ↦ (Λi i).map))
    (MatrixMap.IsCompletelyPositive.piProd (fun i ↦ (Λi i).map_cp))
    (MatrixMap.IsTracePreserving.piProd (fun i ↦ (Λi i).map_TP))

@[simp]
theorem piProd_map (Λi : (i:ι) → CPTPMap (dI i) (dO i)) :
    (piProd Λi).map = MatrixMap.piProd (fun i ↦ (Λi i).map) :=
  map_ofMat _ _ _

/-- A tensor product over a singleton index type is just the single factor, up to the relabelling
that identifies a singleton-indexed Pi type with its unique component. -/
theorem piProd_unique [Unique ι] (Λi : (i : ι) → CPTPMap (dI i) (dO i)) :
    piProd Λi = CPTPOp.ofEquiv (Equiv.piUnique dO).symm ∘ₘ
      (Λi default ∘ₘ CPTPOp.ofEquiv (Equiv.piUnique dI)) := by
  apply CPTPOp.ext_map
  refine (Matrix.stdBasis ℂ ((i : ι) → dI i) ((i : ι) → dI i)).ext fun p ↦ ?_
  obtain ⟨a, b⟩ := p
  have hsub : MatrixMap.submatrix ℂ (Equiv.piUnique dI).symm (Matrix.single a b 1)
      = Matrix.single (a default) (b default) 1 := by
    ext j k
    rw [MatrixMap.submatrix]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply, Matrix.single_apply]
    refine if_congr (and_congr ?_ ?_) rfl rfl <;>
      exact Equiv.eq_symm_apply (Equiv.piUnique dI)
  simp only [Matrix.stdBasis_eq_single, piProd_map, compose_map, LinearMap.comp_apply,
    ofEquiv_map, Equiv.symm_symm, hsub, MatrixMap.piProd_single]
  ext j k
  rw [MatrixMap.submatrix]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply, Matrix.piProd_apply,
    Fintype.prod_unique]
  rfl

/--
The tensor product of composed maps is the composition of the tensor products.
-/
theorem piProd_comp
  {d₁ d₂ d₃ : ι → Type*}
  [∀ i, Fintype (d₁ i)] [∀ i, DecidableEq (d₁ i)]
  [∀ i, Fintype (d₂ i)] [∀ i, DecidableEq (d₂ i)]
  [∀ i, Fintype (d₃ i)] [∀ i, DecidableEq (d₃ i)]
  (Λ₁ : ∀ i, CPTPMap (d₁ i) (d₂ i)) (Λ₂ : ∀ i, CPTPMap (d₂ i) (d₃ i)) :
  piProd (fun i => (Λ₂ i) ∘ₘ (Λ₁ i)) = (piProd Λ₂) ∘ₘ (piProd Λ₁) := by
    apply CPTPOp.ext_map
    simp only [piProd_map, compose_map]
    convert MatrixMap.piProd_comp _ _;
    infer_instance

/-- The tensor product of identity channels is the identity channel. -/
@[simp]
theorem piProd_id :
    piProd (fun i ↦ (CPTPOp.id : CPTPMap (dI i) (dI i))) = CPTPOp.id := by
  apply CPTPOp.ext_map
  simp only [piProd_map, id_map]
  exact MatrixMap.piProd_id

end finprod

section unitary

/-- Conjugating density matrices by a unitary as a channel. This is standard unitary evolution. -/
def ofUnitary (U : 𝐔[dIn]) : CPTPMap dIn dIn :=
  ofMat (MatrixMap.conj (U : Matrix dIn dIn ℂ))
    (MatrixMap.conj_isCompletelyPositive (U : Matrix dIn dIn ℂ))
    (by
      intro
      simp [Matrix.trace_mul_cycle (U : Matrix dIn dIn ℂ), ← Matrix.star_eq_conjTranspose])

/-- **Matrix analogue of a unitary channel**: its matrix is conjugation by `U`. -/
@[simp]
theorem ofUnitary_map (U : 𝐔[dIn]) :
    (ofUnitary U).map = MatrixMap.conj (U : Matrix dIn dIn ℂ) :=
  map_ofMat _ _ _

/-- The unitary channel U conjugated by U. -/
theorem ofUnitary_eq_conj (U : 𝐔[dIn]) (ρ : MState dIn) :
    (ofUnitary U) ρ = ρ.uConj U := by
  apply DensityOp.ext_m
  rw [mat_coe_eq_apply_mat, ofUnitary_map, MState.uConj_m]
  rfl

/-- A channel is unitary iff it is `ofUnitary U`. -/
def IsUnitary (Λ : CPTPMap dIn dIn) : Prop :=
  ∃ U, Λ = ofUnitary U

/-- A channel is unitary iff it can be written as conjugation by a unitary. -/
theorem IsUnitary_iff_uConj (Λ : CPTPMap dIn dIn) :
    IsUnitary Λ ↔ ∃ U, ∀ ρ : MState dIn, Λ ρ = ρ.uConj U := by
  constructor
  · rintro ⟨U, rfl⟩
    exact ⟨U, ofUnitary_eq_conj U⟩
  · rintro ⟨U, hU⟩
    exact ⟨U, CPTPOp.funext fun ρ ↦ (hU ρ).trans (ofUnitary_eq_conj U ρ).symm⟩

theorem IsUnitary_equiv (σ : dIn ≃ dIn) : IsUnitary (ofEquiv σ) := by
  have h_unitary : ∃ U : Matrix dIn dIn ℂ, U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 ∧ ∀ x : dIn, (∀ y : dIn, (U y x = 1) ↔ (y = σ x)) ∧ ∀ y : dIn, (U y x = 0) ↔ (y ≠ σ x) := by
    simp only [Matrix.conjTranspose, RCLike.star_def];
    refine' ⟨ fun y x => if y = σ x then 1 else 0, ?_, ?_, by simp⟩
    · ext y x
      simp [Matrix.mul_apply, Matrix.transpose_apply];
      rw [Finset.sum_eq_single ( σ.symm x )] <;> aesop
    · ext y x
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply];
      simp [Matrix.one_apply, eq_comm]
  obtain ⟨U, hU_unitary, hU_eq⟩ := h_unitary;
  use ⟨U, Matrix.mem_unitaryGroup_iff.mpr hU_unitary⟩
  have h_mul : ∀ ρ : Matrix dIn dIn ℂ, U * ρ * Uᴴ = Matrix.submatrix ρ σ.symm σ.symm := by
    intro ρ
    ext i j
    have hU_i_x : ∀ x : dIn, U i x = if x = σ.symm i then 1 else 0 := by grind
    have hU_j_x : ∀ x : dIn, U j x = if x = σ.symm j then 1 else 0 := by grind
    simp [Matrix.mul_apply, Matrix.submatrix, hU_i_x, hU_j_x]
  apply CPTPOp.funext
  intro ρ
  apply DensityOp.ext_m
  rw [ofUnitary_eq_conj, MState.uConj_m, ofEquiv_apply, MState.relabel_m]
  exact (h_mul ρ.m).symm

end unitary

-- /-- A channel is *entanglement breaking* iff its product with the identity channel
--   only outputs separable states. -/
-- def IsEntanglementBreaking (Λ : CPTPMap dIn dOut) : Prop :=
--   ∀ (dR : Type u_1) [Fintype dR] [DecidableEq dR],
--   ∀ (ρ : MState (dR × dIn)), ((CPTPOp.id (dIn := dR) ⊗ₖ Λ) ρ).IsSeparable

--TODO:
--Theorem: entanglement breaking iff it holds for all channels, not just id.
--Theorem: entanglement break iff it breaks a Bell pair (Wilde Exercise 4.6.2)
--Theorem: entanglement break if c-q or q-c, e.g. measurements
--Theorem: eb iff Kraus operators can be written as all unit rank (Wilde Theorem 4.6.1)

section purify
variable [Inhabited dOut]

--PULLOUT
omit [DecidableEq dOut] [Inhabited dOut] in
/-
PROBLEM
If a MatrixMap of_kraus K K is trace-preserving, then Σ_k K_k† K_k = 1.

PROVIDED SOLUTION
The TP condition says for all X, trace((of_kraus K K) X) = trace(X).
Unfolding of_kraus: trace(Σ_k K_k X K_k†) = Σ_k trace(K_k† K_k X) (by cycle) = trace((Σ_k K_k† K_k) X).
So trace(A X) = trace(X) for all X where A = Σ_k K_k† K_k, which means A = 1.
Use `Matrix.eq_of_trace_mul_eq` or the fact that trace is a faithful pairing on matrices
to conclude A = 1. The TP condition `Λ.TP` gives us `∀ x, (Λ.map x).trace = x.trace`, and
since `Λ.map = of_kraus K K`, we substitute and simplify.
-/
private lemma kraus_sum_eq_one_of_TP
    {κ : Type*} [Fintype κ]
    {K₁ K₂ : κ → Matrix dOut dIn ℂ}
    (hTP : (MatrixMap.of_kraus K₁ K₂).IsTracePreserving) :
    ∑ k, (K₂ k).conjTranspose * (K₁ k) = 1 := by
  ext1 i j
  have := hTP (Matrix.of fun x y ↦ if x = j then if y = i then 1 else 0 else 0)
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] at this
  convert this using 1
  · simp [MatrixMap.of_kraus, Matrix.sum_apply, Matrix.mul_apply]
    rw [Finset.sum_comm]
    congr! 2
    ring
  · simp [Matrix.one_apply, eq_comm]

/-
PROBLEM
Given an m × n matrix V over ℂ with V†V = 1, and an injection emb : n ↪ m,
there exists a unitary matrix U ∈ unitaryGroup m ℂ such that for all i and j,
U i (emb j) = V i j.

PROVIDED SOLUTION
The columns of V form an orthonormal set in ℂ^m (this follows from V†V = 1).
Using the embedding emb, assign each column V_j to position emb(j) in the larger matrix.
The remaining columns can be filled by extending to an orthonormal basis of ℂ^m.
This extension exists by `Orthonormal.exists_orthonormalBasis_extension` in Mathlib.
The resulting matrix has orthonormal columns spanning ℂ^m, hence it is unitary.

Concretely, define the column vectors of V as an orthonormal family in EuclideanSpace ℂ m,
indexed by the range of emb. Then use `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
to extend this to a full OrthonormalBasis. The matrix of this basis is unitary.

Alternatively, use V to define a linear isometry on the subspace spanned by the image
of emb, then use `LinearIsometry.extend` to extend to the full space. Since in finite
dimensions a linear isometry from a space to itself is surjective, this gives a
LinearIsometryEquiv, hence a unitary matrix.
-/
private lemma exists_unitary_extending_isometry
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : V.conjTranspose * V = 1)
    (emb : n ↪ m) :
    ∃ U : 𝐔[m], ∀ i j, U.val i (emb j) = V i j := by
  -- Let $u_i$ be the $i$-th column of $V$.
  set u : n → EuclideanSpace ℂ m := fun j => WithLp.toLp 2 (fun i => V i j)
  -- Since $u$ is an orthonormal set, we can extend it to an orthonormal basis of $\mathbb{C}^m$.
  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis m ℂ (EuclideanSpace ℂ m), ∀ j, b (emb j) = u j := by
    have h_orthonormal : Orthonormal ℂ (fun j => u j) := by
      rw [ orthonormal_iff_ite ];
      intro i j
      replace hV := congr_fun (congr_fun hV i) j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hV
      simp only [u, EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply]
      simpa only [mul_comm] using hV
    have := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ) (E := EuclideanSpace ℂ m) (ι := m)
    simp only [finrank_euclideanSpace, forall_const] at this
    contrapose! this
    · refine ⟨fun i => if hi : i ∈ Set.range emb then u (Classical.choose hi) else 0, Set.range emb, ?_, ?_ ⟩
      · simp +contextual only [Orthonormal, h_orthonormal.1, implies_true, true_and,
          Set.mem_range, Set.domRestrict_apply, Subtype.forall, ↓reduceDIte]
        intro i j hij
        split_ifs with h₁ h₂
        · apply h_orthonormal.2
          have := Classical.choose_spec ‹∃ y, emb y = ↑i›
          have := Classical.choose_spec ‹∃ y, emb y = ↑j›
          grind
        · simp
        · simp
        · simp
      · simp_all only [Orthonormal, ne_eq, Set.mem_range, exists_exists_eq_and,
          EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceDIte, Classical.choose_eq, implies_true];
  refine ⟨⟨Matrix.of (fun i j ↦ b j i), ?_⟩, ?_⟩
  · simp only [Matrix.mem_unitaryGroup_iff]
    ext1 i j
    simpa [inner, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using
      b.sum_inner_mul_inner (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  · simp [hb, u]

omit [DecidableEq dOut] [Inhabited dOut] in
/--
Given Kraus operators K indexed by (dOut × dIn), define the isometry matrix
V : Matrix (dIn × dOut × dOut) dIn ℂ by V_{(a, b, d), a'} = (K (b, a))_{d, a'}.
Then V†V = 1.
-/
private lemma purify_isometry_condition
    {K : (dOut × dIn) → Matrix dOut dIn ℂ}
    (hTP : ∑ k, (K k).conjTranspose * (K k) = 1) :
    let V : Matrix (dIn × dOut × dOut) dIn ℂ :=
      fun ⟨a, b, d⟩ a' => (K (b, a)) d a'
    V.conjTranspose * V = 1 := by
  rw [← hTP]
  ext1 i j
  simp only [Matrix.mul_apply, Fintype.sum_prod_type];
  rw [Finset.sum_comm]
  simp [Matrix.sum_apply, Matrix.mul_apply]

private lemma purify_MState_pure_basis_default_entry (i j : dOut × dOut) :
    (MState.pure (Ket.basis (default : dOut × dOut))).m i j =
    if i = default ∧ j = default then 1 else 0 := by
  rw [MState.pure_apply, Ket.apply, Ket.apply, Ket.basis]
  by_cases hi : i = default <;> by_cases hj : j = default <;>
    simp [hi, hj, eq_comm]

omit [Inhabited dOut] in
private lemma purify_replacement_single_eq (ρ₀ : MState (dOut × dOut)) (b₁ b₂ : dOut × dOut) :
    ((replacement ρ₀).map (Matrix.single () () 1)) b₁ b₂ = ρ₀.m b₁ b₂ := by
  rw [replacement_map]
  simp

omit [Inhabited dOut] in
/-- **Matrix analogue of preparation**: appending a `Unit` factor and then preparing `ρ₀` on it
is just taking the Kronecker product with `ρ₀`. -/
private lemma purify_prep_append_map (X : Matrix dIn dIn ℂ) (ρ₀ : MState (dOut × dOut)) :
    (id ⊗ᶜᵖ (replacement ρ₀ : CPTPMap Unit (dOut × dOut))).map
      ((CPTPOp.ofEquiv (Equiv.prodPUnit dIn).symm).map X) =
      Matrix.kroneckerMap (· * ·) X ρ₀.m := by
  have happ : (CPTPOp.ofEquiv (Equiv.prodPUnit dIn).symm).map X =
      Matrix.kroneckerMap (· * ·) X (Matrix.single () () 1 : Matrix Unit Unit ℂ) := by
    ext ⟨a, u⟩ ⟨b, v⟩
    simp [MatrixMap.submatrix, Matrix.kroneckerMap]
  rw [happ, prod_map, MatrixMap.kron_map_of_kron_state, id_map, LinearMap.id_coe, _root_.id_eq]
  congr 1
  ext b₁ b₂
  exact purify_replacement_single_eq ρ₀ b₁ b₂

private lemma purify_pure_basis_default_m :
    (MState.pure (Ket.basis (default : dOut × dOut))).m =
      Matrix.single default default 1 := by
  ext a b
  rw [purify_MState_pure_basis_default_entry, Matrix.single_apply]
  by_cases ha : a = default <;> by_cases hb : b = default <;> simp [ha, hb, eq_comm]

/-- Append two fresh copies of `dOut`, each prepared in the default basis state `∣0⟩`, to the
input system. -/
def prepDefault : CPTPMap dIn (dIn × dOut × dOut) :=
  (id ⊗ᶜᵖ (replacement (MState.pure (Ket.basis (default : dOut × dOut))) :
      CPTPMap Unit (dOut × dOut))) ∘ₘ CPTPOp.ofEquiv (Equiv.prodPUnit dIn).symm

/-- **Matrix analogue of `CPTPOp.prepDefault`**: it takes the Kronecker product with `∣0⟩⟨0∣`. -/
@[simp]
theorem prepDefault_map (X : Matrix dIn dIn ℂ) :
    (prepDefault (dIn := dIn) (dOut := dOut)).map X =
      Matrix.kroneckerMap (· * ·) X (Matrix.single default default 1) := by
  rw [prepDefault, compose_map, LinearMap.comp_apply, purify_prep_append_map,
    purify_pure_basis_default_m]

/-- The Stinespring preparation `prep ∘ₘ append` acts on a matrix entry by the Kronecker product
with the fixed pure state `∣0⟩⟨0∣` on `dOut × dOut`. -/
theorem prep_append_map_entry (X : Matrix dIn dIn ℂ)
    (a₁ : dIn) (b₁c₁ : dOut × dOut) (a₂ : dIn) (b₂c₂ : dOut × dOut) :
    let τ := MState.pure (Ket.basis (default : dOut × dOut))
    let zero_prep : CPTPMap Unit (dOut × dOut) := replacement τ
    let prep := (id ⊗ᶜᵖ zero_prep)
    let append : CPTPMap dIn (dIn × Unit) := CPTPOp.ofEquiv (Equiv.prodPUnit dIn).symm
    (prep ∘ₘ append).map X (a₁, b₁c₁) (a₂, b₂c₂) =
    X a₁ a₂ * τ.m b₁c₁ b₂c₂ := by
  show (prepDefault (dIn := dIn) (dOut := dOut)).map X (a₁, b₁c₁) (a₂, b₂c₂) = _
  rw [prepDefault_map, purify_pure_basis_default_m]
  rfl

private lemma purify_conj_entry (X : Matrix dIn dIn ℂ) (U : 𝐔[dIn × dOut × dOut])
      (i j : dIn × dOut × dOut) :
    (ofUnitary U).map (prepDefault.map X) i j =
    ∑ α₁ : dIn, ∑ α₂ : dIn,
      U.val i (α₁, default, default) * X α₁ α₂ *
      starRingEnd ℂ (U.val j (α₂, default, default)) := by
  have hd : (default : dOut × dOut) = (default, default) := rfl
  simp only [prepDefault_map, ofUnitary_map, MatrixMap.conj_apply]
  have key : ∀ l : dIn × dOut × dOut,
      (U.val * Matrix.kroneckerMap (· * ·) X
          (Matrix.single (default : dOut × dOut) default 1) :
        Matrix (dIn × dOut × dOut) (dIn × dOut × dOut) ℂ) i l
        = if l.2 = default then ∑ α : dIn, U.val i (α, default, default) * X α l.1 else 0 := by
    intro l
    rw [Matrix.mul_apply]
    split_ifs with hl
    · simp only [Matrix.kroneckerMap_apply, Matrix.single_apply, hl, and_true, hd,
        mul_ite, mul_one, mul_zero, Fintype.sum_prod_type, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    · simp only [Matrix.kroneckerMap_apply, Matrix.single_apply, Ne.symm hl, and_false,
        if_false, mul_zero, Finset.sum_const_zero]
  rw [Matrix.mul_apply]
  simp only [key]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, hd, Fintype.sum_prod_type,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  exact Finset.sum_comm

private lemma purify_rhs_entry (X : Matrix dIn dIn ℂ) (d₁ d₂ : dOut)
    (U : 𝐔[dIn × dOut × dOut]) :
    (traceLeft ∘ₘ traceLeft ∘ₘ (ofUnitary U) ∘ₘ prepDefault).map X d₁ d₂ =
    ∑ a : dIn, ∑ b : dOut, ∑ α₁ : dIn, ∑ α₂ : dIn,
      U.val (a, b, d₁) (α₁, default, default) * X α₁ α₂ *
      starRingEnd ℂ (U.val (a, b, d₂) (α₂, default, default)) := by
  simp only [compose_map, LinearMap.comp_apply, traceLeft_map, traceLeftₘ, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.traceLeft, Matrix.of_apply, purify_conj_entry]
  exact Finset.sum_comm

omit [DecidableEq dIn] [DecidableEq dOut] [Inhabited dOut] in
private lemma purify_of_kraus_entry (K : (dOut × dIn) → Matrix dOut dIn ℂ) (X : Matrix dIn dIn ℂ) (d₁ d₂ : dOut) :
    (MatrixMap.of_kraus K K) X d₁ d₂ =
    ∑ k : dOut × dIn, ∑ α₁ : dIn, ∑ α₂ : dIn,
      (K k) d₁ α₁ * X α₁ α₂ * starRingEnd ℂ ((K k) d₂ α₂) := by
  have h_lhs : (MatrixMap.of_kraus K K) X = ∑ k, K k * X * (K k).conjTranspose := by
    simp [MatrixMap.of_kraus]
  simp only [h_lhs, Matrix.sum_apply, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ ↦ ?_
  rw [Finset.sum_comm]

theorem exists_purify (Λ : CPTPMap dIn dOut) :
    ∃ (Λ' : CPTPMap (dIn × dOut × dOut) (dIn × dOut × dOut)),
      Λ'.IsUnitary ∧
      Λ = CPTPOp.traceLeft ∘ₘ CPTPOp.traceLeft ∘ₘ Λ' ∘ₘ prepDefault := by
  obtain ⟨K, hK⟩ := Λ.map_cp.exists_kraus _
  have hTP_kraus : ∑ k, (K k).conjTranspose * (K k) = 1 :=
    kraus_sum_eq_one_of_TP (hK ▸ Λ.map_TP)
  let V : Matrix (dIn × dOut × dOut) dIn ℂ :=
    fun ⟨a, b, d⟩ a' => (K (b, a)) d a'
  have hV : V.conjTranspose * V = 1 :=
    purify_isometry_condition hTP_kraus
  let emb : dIn ↪ (dIn × dOut × dOut) :=
    ⟨fun a ↦ (a, default, default), fun a₁ a₂ h ↦ by simpa using h⟩
  obtain ⟨U, hU⟩ := exists_unitary_extending_isometry V hV emb
  use ofUnitary U, ⟨U, rfl⟩
  apply CPTPOp.ext_map
  ext X d₁ d₂ : 2
  rw [hK, purify_of_kraus_entry, purify_rhs_entry]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Function.Embedding.coeFn_mk, emb, V] at hU
  simp_rw [hU]

/-- Every channel can be written as a unitary channel on a larger system. In general, if
 the original channel was A→B, we may need to go as big as dilating the output system (the
 environment) by a factor of A*B. One way of stating this would be that it forms an
 isometry from A to (B×A×B). So that we can instead talk about the cleaner unitaries, we
 say that this is a unitary on (A×B×B). The defining properties that this is a valid
 purification comes are `purify_IsUnitary` and `purify_trace`. This means the environment
 always has type `dIn × dOut`.

 Furthermore, since we need a canonical "0" state on B in order to add with the input,
 we require a typeclass instance [Inhabited dOut]. -/
def purify (Λ : CPTPMap dIn dOut) : CPTPMap (dIn × dOut × dOut) (dIn × dOut × dOut) :=
  exists_purify Λ |>.choose

theorem purify_IsUnitary (Λ : CPTPMap dIn dOut) : Λ.purify.IsUnitary :=
  exists_purify Λ |>.choose_spec.1

/-- With a channel Λ : A → B, a valid purification (A×B×B)→(A×B×B) is such that:
 * Preparing the default ∣0⟩ state on two copies of B
 * Appending these to the input
 * Applying the purified unitary channel
 * Tracing out the two left parts of the output
is equivalent to the original channel. This theorem states that the channel output by `purify`
has this property. -/
theorem purify_trace (Λ : CPTPMap dIn dOut) :
    Λ = CPTPOp.traceLeft ∘ₘ CPTPOp.traceLeft ∘ₘ Λ.purify ∘ₘ prepDefault :=
  exists_purify Λ |>.choose_spec.2

--TODO Theorem: `purify` is unique up to unitary equivalence.

/-- The complementary channel comes from tracing out the other half (the right half) of the purified channel `purify`. -/
def complementary (Λ : CPTPMap dIn dOut) : CPTPMap dIn (dIn × dOut) :=
  CPTPOp.traceRight ∘ₘ CPTPOp.assoc' ∘ₘ Λ.purify ∘ₘ prepDefault

end purify

section degradable
variable [Inhabited dOut] [Inhabited dOut₂]

/-- A channel is *degradable to* another, if the other can be written as a composition of
  a _degrading_ channel D with the original channel. -/
def IsDegradableTo (Λ : CPTPMap dIn dOut) (Λ₂ : CPTPMap dIn dOut₂) : Prop :=
  ∃ (D : CPTPMap dOut (dOut₂)), D ∘ₘ Λ = Λ₂

/-- A channel is *antidegradable to* another, if the other `IsDegradableTo` this one. -/
@[reducible]
def IsAntidegradableTo (Λ : CPTPMap dIn dOut) (Λ₂ : CPTPMap dIn dOut₂) : Prop :=
  IsDegradableTo Λ₂ Λ

/-- A channel is *degradable* if it `IsDegradableTo` its complementary channel. -/
def IsDegradable (Λ : CPTPMap dIn dOut) : Prop :=
  IsDegradableTo Λ Λ.complementary

/-- A channel is *antidegradable* if it `IsAntidegradableTo` its complementary channel. -/
@[reducible]
def IsAntidegradable (Λ : CPTPMap dIn dOut) : Prop :=
  IsAntidegradableTo Λ Λ.complementary

--Theorem (Wilde Exercise 13.5.7): Entanglement breaking channels are antidegradable.
end degradable

/-- `CPTPMap`s inherit a topology from their choi matrices. -/
instance instTop : TopologicalSpace (CPTPMap dIn dOut) :=
  TopologicalSpace.induced (CPTPOp.choi) instTopologicalSpaceMatrix

/-- The projection from `CPTPMap` to the Choi matrix is an embedding -/
theorem choi_IsEmbedding : Topology.IsEmbedding (CPTPOp.choi (dIn := dIn) (dOut := dOut)) where
  eq_induced := rfl
  injective _ _ := choi_ext

instance instT3Space : T3Space (CPTPMap dIn dOut) :=
  Topology.IsEmbedding.t3Space choi_IsEmbedding

end
end CPTPOp
