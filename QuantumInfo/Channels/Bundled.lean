/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Channels.OpMap
public import QuantumInfo.States.Mixed.MState

public import Mathlib.Topology.Order.Hom.Basic

/-! # Classes of operator maps

The bundled `OpMap`s: `HPOp` (Hermitian preserving), `UnitalOp`, `TPOp` (trace preserving),
`POp` (positive), and `CPOp` (completely positive), together with the combinations `PTPOp`,
`PUOp`, `CPTPOp`, and `CPUOp`.

These are all maps between operators on complex Hilbert spaces, and so are independent of any
choice of basis. Given preferred orthonormal bases -- that is, `StdBasis ℂ E ι` and
`StdBasis ℂ F κ` instances -- `HPOp.map` is the corresponding `MatrixMap`, and each defining
property has a matrix analogue (`HPOp.map_HP`, `TPOp.map_TP`, and so on). The abbreviations
`HPMap dIn dOut`, ..., `CPTPMap dIn dOut` are the special case of `EuclideanSpace`s, where the
preferred bases are the computational ones.

The majority of quantum theory revolves around `CPTPOp`s, so those are explored more
thoroughly in their file CPTP.lean.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder

section Defs

variable (E F : Type*)
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Hermitian-preserving linear maps of operators. -/
structure HPOp extends OpMap E F where
  HP : OpMap.IsHermitianPreserving toLinearMap

/-- Unital linear maps of operators. -/
structure UnitalOp extends OpMap E F where
  unital : OpMap.Unital toLinearMap

/-- Trace-preserving linear maps of operators. -/
structure TPOp extends OpMap E F where
  TP : OpMap.IsTracePreserving toLinearMap

/-- Positive linear maps of operators. -/
structure POp extends HPOp E F where
  pos : OpMap.IsPositive toLinearMap
  HP := pos.isHermitianPreserving

/-- Completely positive linear maps of operators. -/
structure CPOp extends POp E F where
  cp : OpMap.IsCompletelyPositive toLinearMap
  pos := cp.isPositive

/-- Positive trace-preserving linear maps. These include all channels, but aren't
  necessarily *completely* positive, see `CPTPOp`. -/
structure PTPOp extends POp E F, TPOp E F

/-- Positive unital maps. These are important because they are the
  dual to `PTPOp`: they are the most general way to map *observables*. -/
structure PUOp extends POp E F, UnitalOp E F

/-- Completely positive trace-preserving linear maps. This is the most common
  meaning of "channel", often described as "the most general physically realizable
  quantum operation". -/
structure CPTPOp extends PTPOp E F, CPOp E F

/-- Completely positive unital maps. These are important because they are the
  dual to `CPTPOp`: they are the physically realizable ways to map *observables*. -/
structure CPUOp extends CPOp E F, PUOp E F

end Defs

section Euclidean

variable (dIn dOut : Type*) [Fintype dIn] [Fintype dOut]

/-- Hermitian-preserving maps between systems with computational bases. -/
abbrev HPMap := HPOp (EuclideanSpace ℂ dIn) (EuclideanSpace ℂ dOut)

/-- Unital maps between systems with computational bases. -/
abbrev UnitalMap := UnitalOp (EuclideanSpace ℂ dIn) (EuclideanSpace ℂ dOut)

/-- Trace-preserving maps between systems with computational bases. -/
abbrev TPMap := TPOp (EuclideanSpace ℂ dIn) (EuclideanSpace ℂ dOut)

/-- Positive maps between systems with computational bases. -/
abbrev PMap := POp (EuclideanSpace ℂ dIn) (EuclideanSpace ℂ dOut)

/-- Completely positive maps between systems with computational bases. -/
abbrev CPMap := CPOp (EuclideanSpace ℂ dIn) (EuclideanSpace ℂ dOut)

/-- Positive trace-preserving maps between systems with computational bases. -/
abbrev PTPMap := PTPOp (EuclideanSpace ℂ dIn) (EuclideanSpace ℂ dOut)

/-- Positive unital maps between systems with computational bases. -/
abbrev PUMap := PUOp (EuclideanSpace ℂ dIn) (EuclideanSpace ℂ dOut)

/-- Quantum channels between systems with computational bases. -/
abbrev CPTPMap := CPTPOp (EuclideanSpace ℂ dIn) (EuclideanSpace ℂ dOut)

/-- Completely positive unital maps between systems with computational bases. -/
abbrev CPUMap := CPUOp (EuclideanSpace ℂ dIn) (EuclideanSpace ℂ dOut)

end Euclidean

variable {E F ι κ : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

--Hermitian-preserving maps: continuous linear maps on HermitianMats.
namespace HPOp

variable {Λ₁ Λ₂ : HPOp E F}

@[ext]
theorem ext (h : Λ₁.toLinearMap = Λ₂.toLinearMap) : Λ₁ = Λ₂ := by
  rwa [HPOp.mk.injEq]

/-- A Hermitian-preserving map acting on self-adjoint operators. This is the basis-free form of
`HPOp.instFunLike`; `HPOp.toMat_opApply` is its matrix analogue. -/
def opApply (Λ : HPOp E F) (A : HermitianOp E) : HermitianOp F :=
  ⟨Λ.toLinearMap A.op, Λ.HP A.H⟩

@[simp]
theorem op_opApply (Λ : HPOp E F) (A : HermitianOp E) :
    (Λ.opApply A).op = Λ.toLinearMap A.op :=
  rfl

section StdBasis

variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ]

/-- **Matrix analogue of a Hermitian-preserving map**: its matrix in the preferred bases. -/
def map (Λ : HPOp E F) : MatrixMap ι κ ℂ :=
  OpMap.toMat Λ.toLinearMap

theorem map_eq (Λ : HPOp E F) : Λ.map (ι := ι) (κ := κ) = OpMap.toMat Λ.toLinearMap :=
  rfl

/-- Two maps with the same matrix are equal. -/
theorem ext_map (h : Λ₁.map (ι := ι) (κ := κ) = Λ₂.map) : Λ₁ = Λ₂ :=
  ext (OpMap.toMat_injective h)

@[simp]
theorem map_HP (Λ : HPOp E F) : (Λ.map (ι := ι) (κ := κ)).IsHermitianPreserving :=
  (OpMap.isHermitianPreserving_toMat_iff _).mpr Λ.HP

/-- The Hermitian-preserving map with a given Hermitian-preserving matrix. -/
def ofMat (M : MatrixMap ι κ ℂ) (hHP : M.IsHermitianPreserving) : HPOp E F where
  toLinearMap := OpMap.ofMat E F M
  HP := (OpMap.isHermitianPreserving_toMat_iff (ι := ι) (κ := κ) _).mp (by simpa using hHP)

@[simp]
theorem map_ofMat (M : MatrixMap ι κ ℂ) (hHP : M.IsHermitianPreserving) :
    (ofMat (E := E) (F := F) M hHP).map = M :=
  OpMap.toMat_ofMat M

/-- Two maps are equal if they agree on all Hermitian inputs. -/
theorem funext_hermitian (h : ∀ M : HermitianMat ι ℂ, Λ₁.map (κ := κ) M = Λ₂.map M) :
    Λ₁ = Λ₂ := by
  refine ext_map (ι := ι) (κ := κ) ?_
  ext M : 1
  have hH := h (realPart M)
  have hA := h (imaginaryPart M)
  convert congr($hH + Complex.I • $hA)
  <;> rw (occs := [1]) [← realPart_add_I_smul_imaginaryPart M, map_add, map_smul]
  <;> rfl

/-- Two maps are equal if they agree on all positive inputs. -/
theorem funext_pos (h : ∀ M : HermitianMat ι ℂ, 0 ≤ M → Λ₁.map (κ := κ) M = Λ₂.map M) :
    Λ₁ = Λ₂ := by
  classical
  open scoped HermitianMat in
  apply funext_hermitian (κ := κ)
  intro M
  rw [← M.posPart_add_negPart]
  simp [HermitianMat.posPart_nonneg, HermitianMat.negPart_nonneg, h]

/-- Two maps are equal if they agree on all positive inputs with trace one -/
theorem funext_pos_trace
    (h : ∀ M : HermitianMat ι ℂ, 0 ≤ M → M.trace = 1 → Λ₁.map (κ := κ) M = Λ₂.map M) :
    Λ₁ = Λ₂ := by
  apply funext_pos (κ := κ)
  intro M hM'
  rcases hM'.eq_or_lt with rfl | hM
  · simp
  have h_tr : 0 < M.trace := M.trace_pos hM
  have := h (M.trace⁻¹ • M) ?_ ?_
  · simp only [HermitianMat.mat_smul, LinearMap.map_smul_of_tower] at this
    convert congr(M.trace • $this)
    · rw [smul_smul]
      field_simp
      simp
    · rw [smul_smul]
      field_simp
      simp
  · apply smul_nonneg (by positivity) hM'
  · simp [field]

/-- Two maps are equal if they agree on all states. -/
theorem funext_mstate (h : ∀ ρ : DensityOp E, Λ₁.map (κ := κ) (ρ.m (ι := ι)) = Λ₂.map ρ.m) :
    Λ₁ = Λ₂ :=
  funext_pos_trace (κ := κ) fun M hM_pos hM_tr ↦ by
    simpa using h (DensityOp.ofMat M hM_pos hM_tr)

/-- Hermitian-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (HPOp E F) (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  coe Λ ρ := ⟨Λ.map ρ.1, Λ.map_HP ρ.2⟩
  coe_injective x y h := funext_hermitian fun M ↦
    by simpa using congrFun h M

/-- **Matrix analogue of applying a Hermitian-preserving map**: the underlying matrix of `Λ T` is
the image of the underlying matrix of `T`. -/
@[simp]
theorem mat_apply (Λ : HPOp E F) (T : HermitianMat ι ℂ) :
    (Λ T : HermitianMat κ ℂ).mat = Λ.map T.mat :=
  rfl

/-- **Matrix analogue of `HPOp.opApply`**: the matrix of `Λ.opApply A` is the image of the matrix
of `A`. Not a `simp` lemma: the index type of `E`'s preferred basis appears only on the
right-hand side, so `simp` cannot infer it. -/
theorem toMat_opApply (Λ : HPOp E F) (A : HermitianOp E) :
    ((Λ.opApply A).toMat : HermitianMat κ ℂ) = Λ (A.toMat : HermitianMat ι ℂ) := by
  refine HermitianMat.ext ?_
  rw [mat_apply, HermitianOp.toMat_mat, HermitianOp.toMat_mat, op_opApply, map_eq,
    OpMap.toMat_apply_toMat]

instance : ContinuousLinearMapClass
    (HPOp E F) ℝ (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.map x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp
  map_continuous f := .subtype_mk (by fun_prop) _

end StdBasis

end HPOp

--Positive-preserving maps: continuous linear order-preserving maps on HermitianMats.
namespace POp

@[ext]
theorem ext {Λ₁ Λ₂ : POp E F} (h : Λ₁.toLinearMap = Λ₂.toLinearMap) : Λ₁ = Λ₂ := by
  rw [POp.mk.injEq]
  exact HPOp.ext h

theorem injective_toHPOp : (POp.toHPOp (E := E) (F := F)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

/-- A positive map sends nonnegative operators to nonnegative operators. -/
theorem opApply_nonneg (Λ : POp E F) {A : HermitianOp E} (h : 0 ≤ A) : 0 ≤ Λ.toHPOp.opApply A :=
  Λ.pos h

section StdBasis

variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ]

/-- **Matrix analogue of positivity**: the matrix map is positive. -/
@[simp]
theorem map_pos (Λ : POp E F) : (Λ.map (ι := ι) (κ := κ)).IsPositive :=
  (OpMap.isPositive_toMat_iff _).mpr Λ.pos

/-- The positive map with a given positive matrix. -/
def ofMat (M : MatrixMap ι κ ℂ) (hpos : M.IsPositive) : POp E F where
  toLinearMap := OpMap.ofMat E F M
  pos := (OpMap.isPositive_toMat_iff (ι := ι) (κ := κ) _).mp (by simpa using hpos)

@[simp]
theorem map_ofMat (M : MatrixMap ι κ ℂ) (hpos : M.IsPositive) :
    (ofMat (E := E) (F := F) M hpos).map = M :=
  OpMap.toMat_ofMat M

/-- Positive maps are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (POp E F) (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  coe := DFunLike.coe ∘ toHPOp
  coe_injective := DFunLike.coe_injective.comp injective_toHPOp

/-- **Matrix analogue of applying a positive map**: the underlying matrix of `Λ T` is
the image of the underlying matrix of `T`. -/
@[simp]
theorem mat_apply (Λ : POp E F) (T : HermitianMat ι ℂ) :
    (Λ T : HermitianMat κ ℂ).mat = Λ.map T.mat :=
  rfl

set_option synthInstance.maxHeartbeats 40000 in
instance instLinearMapClass :
    LinearMapClass (POp E F) ℝ (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.map x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp

instance instContinuousOrderHomClass : ContinuousOrderHomClass (POp E F)
    (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toHPOp
  map_monotone f x y h := by
    rw [HermitianMat.le_iff] at h ⊢
    have hpos := f.map_pos (ι := ι) (κ := κ) h
    rwa [HermitianMat.mat_sub, mat_apply, mat_apply, ← map_sub, ← HermitianMat.mat_sub]

/-- Positive maps also preserve positivity on, specifically, Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : POp E F) {x : HermitianMat ι ℂ} (h : 0 ≤ x) :
    0 ≤ (M x : HermitianMat κ ℂ) := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end StdBasis

end POp

namespace CPOp

@[ext]
theorem ext {Λ₁ Λ₂ : CPOp E F} (h : Λ₁.toLinearMap = Λ₂.toLinearMap) : Λ₁ = Λ₂ := by
  rw [CPOp.mk.injEq]
  exact POp.ext h

section StdBasis

variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ]

/-- **Matrix analogue of complete positivity**: the matrix map is completely positive. -/
@[simp]
theorem map_cp (Λ : CPOp E F) : (Λ.map (ι := ι) (κ := κ)).IsCompletelyPositive :=
  (OpMap.isCompletelyPositive_toMat_iff _).mpr Λ.cp

/-- The completely positive map with a given completely positive matrix. -/
def ofMat (M : MatrixMap ι κ ℂ) (hcp : M.IsCompletelyPositive) : CPOp E F where
  toLinearMap := OpMap.ofMat E F M
  cp := (OpMap.isCompletelyPositive_toMat_iff (ι := ι) (κ := κ) _).mp (by simpa using hcp)

@[simp]
theorem map_ofMat (M : MatrixMap ι κ ℂ) (hcp : M.IsCompletelyPositive) :
    (ofMat (E := E) (F := F) M hcp).map = M :=
  OpMap.toMat_ofMat M

/-- The completely positive map with the given Kraus operators. -/
def of_kraus_CPMap {ν : Type*} [Fintype ν] (M : ν → Matrix κ ι ℂ) : CPOp E F :=
  ofMat (MatrixMap.of_kraus M M) (MatrixMap.of_kraus_isCompletelyPositive M)

/-- **Matrix analogue of `CPOp.of_kraus_CPMap`**: its matrix is the Kraus-operator sum. -/
@[simp]
theorem map_of_kraus_CPMap {ν : Type*} [Fintype ν] (M : ν → Matrix κ ι ℂ) :
    (of_kraus_CPMap (E := E) (F := F) M).map = MatrixMap.of_kraus M M :=
  map_ofMat _ _

end StdBasis

end CPOp

--Positive trace-preserving maps:
--  * Continuous linear order-preserving maps on HermitianMats.
--  * Continuous maps on states.
namespace PTPOp

@[ext]
theorem ext {Λ₁ Λ₂ : PTPOp E F} (h : Λ₁.toLinearMap = Λ₂.toLinearMap) : Λ₁ = Λ₂ := by
  rw [PTPOp.mk.injEq]
  exact POp.ext h

theorem injective_toPOp : (PTPOp.toPOp (E := E) (F := F)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

/-- A trace-preserving map preserves the trace of a self-adjoint operator. -/
theorem trace_opApply (Λ : PTPOp E F) (A : HermitianOp E) :
    (Λ.toHPOp.opApply A).trace = A.trace :=
  congrArg RCLike.re (Λ.TP A.op)

section StdBasis

variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ]

/-- **Matrix analogue of trace preservation**: the matrix map is trace-preserving. -/
@[simp]
theorem map_TP (Λ : PTPOp E F) : (Λ.map (ι := ι) (κ := κ)).IsTracePreserving :=
  (OpMap.isTracePreserving_toMat_iff _).mpr Λ.TP

/-- The positive trace-preserving map with a given positive, trace-preserving matrix. -/
def ofMat (M : MatrixMap ι κ ℂ) (hpos : M.IsPositive) (hTP : M.IsTracePreserving) : PTPOp E F where
  toLinearMap := OpMap.ofMat E F M
  pos := (OpMap.isPositive_toMat_iff (ι := ι) (κ := κ) _).mp (by simpa using hpos)
  TP := (OpMap.isTracePreserving_toMat_iff (ι := ι) (κ := κ) _).mp (by simpa using hTP)

@[simp]
theorem map_ofMat (M : MatrixMap ι κ ℂ) (hpos : M.IsPositive) (hTP : M.IsTracePreserving) :
    (ofMat (E := E) (F := F) M hpos hTP).map = M :=
  OpMap.toMat_ofMat M

/-- Positive trace-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (PTPOp E F) (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  coe := DFunLike.coe ∘ toPOp
  coe_injective := DFunLike.coe_injective.comp injective_toPOp

/-- **Matrix analogue of applying a positive trace-preserving map**: the underlying matrix of `Λ T` is
the image of the underlying matrix of `T`. -/
@[simp]
theorem mat_apply (Λ : PTPOp E F) (T : HermitianMat ι ℂ) :
    (Λ T : HermitianMat κ ℂ).mat = Λ.map T.mat :=
  rfl

instance instLinearMapClass :
    LinearMapClass (PTPOp E F) ℝ (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.map x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (PTPOp E F)
    (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPOp
  map_monotone f x y h := by
    rw [HermitianMat.le_iff] at h ⊢
    have hpos := f.map_pos (ι := ι) (κ := κ) h
    rwa [HermitianMat.mat_sub, mat_apply, mat_apply, ← map_sub, ← HermitianMat.mat_sub]

/-- PTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PTPOp E F) {x : HermitianMat ι ℂ} (h : 0 ≤ x) :
    0 ≤ (M x : HermitianMat κ ℂ) := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end StdBasis

/-- The action of a positive trace-preserving map on states: it carries a positive unit-trace
operator to another one, with no choice of basis anywhere. `PTPOp.instMFunLike` installs this as
the `FunLike` coercion, so it is normally written `Λ ρ`. -/
def applyState (Λ : PTPOp E F) (ρ : DensityOp E) : DensityOp F where
  op := Λ.toHPOp.opApply ρ.op
  op_nonneg := POp.opApply_nonneg Λ.toPOp ρ.op_nonneg
  op_trace := (Λ.trace_opApply ρ.op).trans ρ.op_trace

@[simp]
theorem op_applyState (Λ : PTPOp E F) (ρ : DensityOp E) :
    (Λ.applyState ρ).op = Λ.toHPOp.opApply ρ.op :=
  rfl

/-- **Matrix analogue of `PTPOp.applyState`**: the density matrix of `Λ.applyState ρ` is the image
of the density matrix of `ρ`. Not a `simp` lemma, for the same reason as
`HPOp.toMat_opApply`. -/
theorem M_applyState [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [Fintype κ] [DecidableEq κ]
    [StdBasis ℂ F κ] (Λ : PTPOp E F) (ρ : DensityOp E) :
    ((Λ.applyState ρ).M : HermitianMat κ ℂ) = instFunLike.coe Λ (ρ.M : HermitianMat ι ℂ) :=
  HPOp.toMat_opApply Λ.toHPOp ρ.op

/-- `PTPOp`s are functions from states to states, through `PTPOp.applyState`. -/
instance (priority := 1100) instMFunLike : FunLike (PTPOp E F) (DensityOp E) (DensityOp F) where
  coe := applyState
  coe_injective x y h := by
    let := StdBasis.some ℂ E
    let := StdBasis.some ℂ F
    refine injective_toPOp (POp.injective_toHPOp (HPOp.funext_mstate fun ρ ↦ ?_))
    have h₂ := congrArg (fun σ : DensityOp F ↦ σ.M) (congr($h ρ))
    rw [M_applyState, M_applyState] at h₂
    simpa using congrArg HermitianMat.mat h₂

@[simp]
theorem op_apply_MState (Λ : PTPOp E F) (ρ : DensityOp E) :
    (Λ ρ : DensityOp F).op = Λ.toHPOp.opApply ρ.op :=
  rfl

/-- Two positive trace-preserving maps are equal exactly when they agree on every state. -/
theorem funext_iff {Λ₁ Λ₂ : PTPOp E F} : Λ₁ = Λ₂ ↔ ∀ ρ : DensityOp E, Λ₁ ρ = Λ₂ ρ :=
  DFunLike.ext_iff

/-- **Matrix analogue of applying a positive trace-preserving map to a state**: the density matrix
of `Λ ρ` is the image of the density matrix of `ρ`. Not a `simp` lemma, for the same reason as
`HPOp.toMat_opApply`. -/
theorem M_apply_MState [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [Fintype κ] [DecidableEq κ]
    [StdBasis ℂ F κ] (Λ : PTPOp E F) (ρ : DensityOp E) :
    ((Λ ρ : DensityOp F).M : HermitianMat κ ℂ) =
      instFunLike.coe Λ (ρ.M : HermitianMat ι ℂ) :=
  M_applyState Λ ρ

--If we have a PTPMap, the input and output dimensions are always both nonempty (otherwise
--we can't preserve trace) - or they're both empty. So `[Nonempty dIn]` will always suffice.
-- This would be nice as an `instance` but that would leave `dIn` as a metavariable.
theorem nonemptyOut {dIn dOut : Type*} [Fintype dIn] [DecidableEq dIn] [Fintype dOut]
    [DecidableEq dOut] (Λ : PTPMap dIn dOut) [hIn : Nonempty dIn] : Nonempty dOut := by
  by_contra h
  simp only [not_nonempty_iff] at h
  let M := (1 : Matrix dIn dIn ℂ)
  have := calc (Finset.univ.card (α := dIn) : ℂ)
    _ = M.trace := by simp [Matrix.trace, M]
    _ = (Λ.map M).trace := (Λ.map_TP M).symm
    _ = 0 := by simp only [Matrix.trace_eq_zero_of_isEmpty]
  norm_num [Finset.univ_eq_empty_iff] at this

end PTPOp

namespace CPTPOp

/-- Two `CPTPOp`s are equal if their `OpMap`s are equal. -/
@[ext]
theorem ext {Λ₁ Λ₂ : CPTPOp E F} (h : Λ₁.toLinearMap = Λ₂.toLinearMap) : Λ₁ = Λ₂ := by
  rw [CPTPOp.mk.injEq]
  exact PTPOp.ext h

theorem injective_toPTPOp : (CPTPOp.toPTPOp (E := E) (F := F)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

/-- `CPTPOp`s are functions from states to states. -/
instance (priority := 1100) instMFunLike :
    FunLike (CPTPOp E F) (DensityOp E) (DensityOp F) where
  coe := DFunLike.coe ∘ toPTPOp
  coe_injective := DFunLike.coe_injective.comp injective_toPTPOp

theorem apply_eq_toPTPOp (Λ : CPTPOp E F) (ρ : DensityOp E) :
    (Λ ρ : DensityOp F) = Λ.toPTPOp ρ :=
  rfl

section StdBasis

variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ]

/-- Two maps with the same matrix are equal. -/
theorem ext_map {Λ₁ Λ₂ : CPTPOp E F} (h : Λ₁.map (ι := ι) (κ := κ) = Λ₂.map) : Λ₁ = Λ₂ :=
  ext (OpMap.toMat_injective h)

/-- Two channels are equal exactly when they agree on every state. -/
theorem funext_iff {Λ₁ Λ₂ : CPTPOp E F} : Λ₁ = Λ₂ ↔ ∀ ρ : DensityOp E, Λ₁ ρ = Λ₂ ρ :=
  DFunLike.ext_iff

@[simp]
theorem IsTracePreserving (Λ : CPTPOp E F) : (Λ.map (ι := ι) (κ := κ)).IsTracePreserving :=
  Λ.map_TP

/-- The channel with a given completely positive, trace-preserving matrix. -/
def ofMat (M : MatrixMap ι κ ℂ) (hcp : M.IsCompletelyPositive) (hTP : M.IsTracePreserving) :
    CPTPOp E F where
  toLinearMap := OpMap.ofMat E F M
  cp := (OpMap.isCompletelyPositive_toMat_iff (ι := ι) (κ := κ) _).mp (by simpa using hcp)
  TP := (OpMap.isTracePreserving_toMat_iff (ι := ι) (κ := κ) _).mp (by simpa using hTP)

@[simp]
theorem map_ofMat (M : MatrixMap ι κ ℂ) (hcp : M.IsCompletelyPositive)
    (hTP : M.IsTracePreserving) : (ofMat (E := E) (F := F) M hcp hTP).map = M :=
  OpMap.toMat_ofMat M

variable (ι κ) in
/-- Read a channel between `E` and `F` as a channel between the Euclidean spaces indexed by their
preferred bases. The matrix of the channel is unchanged (`map_transport`), and it acts on
transported states in the transported way (`transport_apply`). -/
def transport (Λ : CPTPOp E F) : CPTPMap ι κ :=
  ofMat Λ.map ((OpMap.isCompletelyPositive_toMat_iff _).mpr Λ.cp) Λ.map_TP

/-- **Matrix analogue of `CPTPOp.transport`**: the matrix of the channel is unchanged. -/
@[simp]
theorem map_transport (Λ : CPTPOp E F) : (Λ.transport ι κ).map = Λ.map (ι := ι) (κ := κ) :=
  map_ofMat _ _ _

/-- Transporting a channel to the Euclidean spaces of its preferred bases commutes with
transporting the states it acts on. -/
@[simp]
theorem transport_apply (Λ : CPTPOp E F) (ρ : MState ι) :
    Λ.transport ι κ ρ = (Λ (ρ.transport E)).transport (EuclideanSpace ℂ κ) := by
  refine DensityOp.ext (ι := κ) ?_
  rw [DensityOp.M_transport, apply_eq_toPTPOp, apply_eq_toPTPOp, PTPOp.M_apply_MState,
    PTPOp.M_apply_MState, DensityOp.M_transport]
  refine HermitianMat.ext ?_
  rw [PTPOp.mat_apply, PTPOp.mat_apply, map_transport]

/-- The channel with the given Kraus operators. -/
def of_kraus_CPTPMap {ν : Type*} [Fintype ν] (M : ν → Matrix κ ι ℂ)
    (hTP : (∑ k, (M k).conjTranspose * (M k)) = 1) : CPTPOp E F :=
  ofMat (MatrixMap.of_kraus M M) (MatrixMap.of_kraus_isCompletelyPositive M)
    (MatrixMap.IsTracePreserving.of_kraus_isTracePreserving M M hTP)

/-- **Matrix analogue of `CPTPOp.of_kraus_CPTPMap`**: its matrix is the Kraus-operator sum. -/
@[simp]
theorem map_of_kraus_CPTPMap {ν : Type*} [Fintype ν] (M : ν → Matrix κ ι ℂ)
    (hTP : (∑ k, (M k).conjTranspose * (M k)) = 1) :
    (of_kraus_CPTPMap (E := E) (F := F) M hTP).map = MatrixMap.of_kraus M M :=
  map_ofMat _ _ _

end StdBasis

end CPTPOp

namespace PUOp

@[ext]
theorem ext {Λ₁ Λ₂ : PUOp E F} (h : Λ₁.toLinearMap = Λ₂.toLinearMap) : Λ₁ = Λ₂ := by
  rw [PUOp.mk.injEq]
  exact POp.ext h

theorem injective_toPOp : (PUOp.toPOp (E := E) (F := F)).Injective := by
  intro _ _ _
  rwa [PUOp.mk.injEq]

section StdBasis

variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ]

/-- **Matrix analogue of unitality**: the matrix map is unital. -/
@[simp]
theorem map_unital (Λ : PUOp E F) : (Λ.map (ι := ι) (κ := κ)).Unital :=
  (OpMap.unital_toMat_iff _).mpr Λ.unital

/-- The positive unital map with a given positive, unital matrix. -/
def ofMat (M : MatrixMap ι κ ℂ) (hpos : M.IsPositive) (hu : M.Unital) : PUOp E F where
  toLinearMap := OpMap.ofMat E F M
  pos := (OpMap.isPositive_toMat_iff (ι := ι) (κ := κ) _).mp (by simpa using hpos)
  unital := (OpMap.unital_toMat_iff (ι := ι) (κ := κ) _).mp (by simpa using hu)

@[simp]
theorem map_ofMat (M : MatrixMap ι κ ℂ) (hpos : M.IsPositive) (hu : M.Unital) :
    (ofMat (E := E) (F := F) M hpos hu).map = M :=
  OpMap.toMat_ofMat M

/-- `PUOp`s are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (PUOp E F) (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  coe Λ := Λ.toPOp
  coe_injective := (DFunLike.coe_injective (F := POp E F)).comp injective_toPOp

/-- **Matrix analogue of applying a positive unital map**: the underlying matrix of `Λ T` is
the image of the underlying matrix of `T`. -/
@[simp]
theorem mat_apply (Λ : PUOp E F) (T : HermitianMat ι ℂ) :
    (Λ T : HermitianMat κ ℂ).mat = Λ.map T.mat :=
  rfl

instance instLinearMapClass :
    LinearMapClass (PUOp E F) ℝ (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.map x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (PUOp E F)
    (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPOp
  map_monotone f x y h := by
    rw [HermitianMat.le_iff] at h ⊢
    have hpos := f.map_pos (ι := ι) (κ := κ) h
    rwa [HermitianMat.mat_sub, mat_apply, mat_apply, ← map_sub, ← HermitianMat.mat_sub]

instance instOneHomClass : OneHomClass (PUOp E F)
    (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  map_one f := HermitianMat.ext (f.map_unital (ι := ι) (κ := κ))

/-- Positive unital maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PUOp E F) {x : HermitianMat ι ℂ} (h : 0 ≤ x) :
    0 ≤ (M x : HermitianMat κ ℂ) := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end StdBasis

end PUOp

namespace CPUOp

@[ext]
theorem ext {Λ₁ Λ₂ : CPUOp E F} (h : Λ₁.toLinearMap = Λ₂.toLinearMap) : Λ₁ = Λ₂ := by
  rw [CPUOp.mk.injEq, CPOp.mk.injEq]
  exact POp.ext h

theorem injective_toPOp : (CPOp.toPOp ∘ CPUOp.toCPOp (E := E) (F := F)).Injective := by
  intro _ _ _
  rwa [CPUOp.mk.injEq, CPOp.mk.injEq]

section StdBasis

variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ]

/-- **Matrix analogue of unitality**: the matrix map is unital. -/
@[simp]
theorem map_unital (Λ : CPUOp E F) : (Λ.map (ι := ι) (κ := κ)).Unital :=
  (OpMap.unital_toMat_iff _).mpr Λ.unital

/-- The completely positive unital map with a given completely positive, unital matrix. -/
def ofMat (M : MatrixMap ι κ ℂ) (hcp : M.IsCompletelyPositive) (hu : M.Unital) : CPUOp E F where
  toLinearMap := OpMap.ofMat E F M
  cp := (OpMap.isCompletelyPositive_toMat_iff (ι := ι) (κ := κ) _).mp (by simpa using hcp)
  unital := (OpMap.unital_toMat_iff (ι := ι) (κ := κ) _).mp (by simpa using hu)

@[simp]
theorem map_ofMat (M : MatrixMap ι κ ℂ) (hcp : M.IsCompletelyPositive) (hu : M.Unital) :
    (ofMat (E := E) (F := F) M hcp hu).map = M :=
  OpMap.toMat_ofMat M

/-- `CPUOp`s are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (CPUOp E F) (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  coe Λ := Λ.toPOp
  coe_injective := (DFunLike.coe_injective (F := POp E F)).comp injective_toPOp

/-- **Matrix analogue of applying a completely positive unital map**: the underlying matrix of `Λ T` is
the image of the underlying matrix of `T`. -/
@[simp]
theorem mat_apply (Λ : CPUOp E F) (T : HermitianMat ι ℂ) :
    (Λ T : HermitianMat κ ℂ).mat = Λ.map T.mat :=
  rfl

instance instLinearMapClass :
    LinearMapClass (CPUOp E F) ℝ (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.map x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (CPUOp E F)
    (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPOp
  map_monotone f x y h := by
    rw [HermitianMat.le_iff] at h ⊢
    have hpos := f.map_pos (ι := ι) (κ := κ) h
    rwa [HermitianMat.mat_sub, mat_apply, mat_apply, ← map_sub, ← HermitianMat.mat_sub]

instance instOneHomClass : OneHomClass (CPUOp E F)
    (HermitianMat ι ℂ) (HermitianMat κ ℂ) where
  map_one f := HermitianMat.ext (f.map_unital (ι := ι) (κ := κ))

/-- Completely positive unital maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : CPUOp E F) {x : HermitianMat ι ℂ} (h : 0 ≤ x) :
    0 ≤ (M x : HermitianMat κ ℂ) := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end StdBasis

end CPUOp

--Tests to make sure that our `simp`s and classes are all working like we want them too

section test

variable {dIn dOut : Type*} [Fintype dIn] [DecidableEq dIn] [Fintype dOut] [DecidableEq dOut]

#guard_msgs in
example (M : HPMap dIn dOut) : (M (Real.pi • 1)) = Real.pi • M 1 := by simp

#guard_msgs in
example (M : PTPMap dIn dOut) : (M.toHPOp (Real.pi • 1)) = Real.pi • M.toHPOp 1 := by simp

#guard_msgs in
example (M : CPTPMap dIn dOut) (ρ : Matrix dIn dIn ℂ) : (M.map ρ).trace = ρ.trace := by simp

#guard_msgs in
example (M : CPUMap dIn dOut) (T : HermitianMat dIn ℂ) : M (1 + 2 • T) = 1 + 2 • M T := by simp

end test
