/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.Adjoint
public import Physlib.Relativity.Tensors.Equivariant
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.Flat.Basic
/-!
# The complex tensor species of `SU(N)`

## i. Overview

The complex tensors of `SU(N)` carry three kinds of index, in analogy with the complex Lorentz
tensors `complexLorentzTensor`: a fundamental index, an anti-fundamental index and an adjoint
index. `suTensor N` is the tensor species with these three colors. The fundamental color is
`Fin N → ℂ` moved by `g`, the anti-fundamental color is `Fin N → ℂ` moved by `(g⁻¹)ᵀ` (for a unitary
`g` the complex conjugate), and the adjoint color is the complexification
`SUAlgebraComplexified N = ℂ ⊗[ℝ] su(N)` of the Lie algebra `SUAlgebra N` of traceless hermitian
matrices, moved by the adjoint representation `adjRep` with the generalized Gell-Mann matrices as
basis, as set up in `LocalGaugeData.SU.Adjoint`. The type of tensors with colors `c₁, …, cₙ` is
written `SuT[N, c₁, …, cₙ]`.

The fundamental and anti-fundamental colors are dual to each other and contract by the dot
product, with unit `∑ eᵢ ⊗ eᵢ`. The adjoint color is dual to itself and contracts by the trace
form `tr (A B)` (`adjContr`), with unit `∑ λ_a ⊗ λᵃ` for the Gell-Mann matrices `λ_a` and their
trace-dual basis `λᵃ = λ_a / 2`. In these bases the matrix of `g⁻¹` on each color is the conjugate transpose
of that of `g`, so the colors are closed under adjoints (F) and the general results on equivariant
maps out of the tensors of a species apply. The
species has no metric (`TensorSpecies.WithMetric`): for `N ≥ 3` the fundamental of `SU(N)` is not
self-dual, so there is no invariant in `ℂᴺ ⊗ ℂᴺ` to raise and lower its indices with.

## ii. Key results

- `suTensor.Color` : the fundamental, anti-fundamental and adjoint colors.
- `suTensor.fundRep`, `suTensor.antiFundRep` : the fundamental and anti-fundamental
  representations.
- `suTensor` : the complex tensor species of `SU(N)`, with the notation `SuT[N, c₁, …, cₙ]`.
- `suTensor.isAdjointClosed` : the colors are closed under adjoints, so the general results on
  equivariant maps (`TensorSpecies.IsEquivariant`) apply.

## iii. Table of contents

- A. The colors and the carriers
- B. The representations
- C. The contractions
- D. The units
- E. The tensor species
- F. The colors are closed under adjoints

-/

@[expose] public section

open Matrix MatrixGroups Module TensorProduct

namespace suTensor

/-!

## A. The colors and the carriers

-/

/-- The colors of the complex tensors of `SU(N)`. -/
inductive Color
  /-- The fundamental color. -/
  | fund : Color
  /-- The anti-fundamental color. -/
  | antiFund : Color
  /-- The adjoint color. -/
  | adj : Color
  deriving DecidableEq

variable (N : ℕ)

/-- The carriers of the three colors. -/
abbrev modules : Color → Type
  | .fund => Fin N → ℂ
  | .antiFund => Fin N → ℂ
  | .adj => SUAlgebraComplexified N

noncomputable instance modulesAddCommGroup : ∀ c, AddCommGroup (modules N c)
  | .fund => inferInstance
  | .antiFund => inferInstance
  | .adj => inferInstance

noncomputable instance modulesModule : ∀ c, Module ℂ (modules N c)
  | .fund => inferInstance
  | .antiFund => inferInstance
  | .adj => inferInstance

/-- The labels of the basis vectors: `Fin N` for the fundamental and anti-fundamental colors,
  and the labels of the generalized Gell-Mann matrices for the adjoint. -/
abbrev basisIdx : Color → Type
  | .fund => Fin N
  | .antiFund => Fin N
  | .adj => GellMann.Index N

instance basisIdxFintype : ∀ c, Fintype (basisIdx N c)
  | .fund => inferInstance
  | .antiFund => inferInstance
  | .adj => inferInstance

instance basisIdxDecidableEq : ∀ c, DecidableEq (basisIdx N c)
  | .fund => inferInstance
  | .antiFund => inferInstance
  | .adj => inferInstance

/-- The bases of the carriers: the standard basis for the fundamental and anti-fundamental colors,
  and the generalized Gell-Mann matrices for the adjoint. -/
noncomputable abbrev basis : (c : Color) → Basis (basisIdx N c) ℂ (modules N c)
  | .fund => Pi.basisFun ℂ (Fin N)
  | .antiFund => Pi.basisFun ℂ (Fin N)
  | .adj => adjBasis N

/-!

## B. The representations

-/

/-- The fundamental representation, `v ↦ g v`. -/
noncomputable def fundRep : Representation ℂ (SU N) (Fin N → ℂ) where
  toFun g := g.1.mulVecLin
  map_one' := by
    simp only [OneMemClass.coe_one, Matrix.mulVecLin_one]
    rfl
  map_mul' g h := by
    simp only [Submonoid.coe_mul, Matrix.mulVecLin_mul]
    rfl

/-- The anti-fundamental representation, `v ↦ (g⁻¹)ᵀ v`, the dual of the fundamental one. For
  unitary `g`, `(g⁻¹)ᵀ` is the complex conjugate of `g`. -/
noncomputable def antiFundRep : Representation ℂ (SU N) (Fin N → ℂ) where
  toFun g := (g⁻¹).1ᵀ.mulVecLin
  map_one' := by
    simp only [inv_one, OneMemClass.coe_one, transpose_one, Matrix.mulVecLin_one]
    rfl
  map_mul' g h := by
    rw [_root_.mul_inv_rev, Submonoid.coe_mul, transpose_mul, Matrix.mulVecLin_mul]
    rfl

/-- The representations of the three colors. -/
noncomputable abbrev rep : (c : Color) → Representation ℂ (SU N) (modules N c)
  | .fund => fundRep N
  | .antiFund => antiFundRep N
  | .adj => adjRep N

/-!

## C. The contractions

-/

/-- The contraction of a fundamental against an anti-fundamental index, the dot product
  `v ⊗ w ↦ ∑ vᵢ wᵢ`. -/
noncomputable def fundContr : ((fundRep N).tprod (antiFundRep N)).IntertwiningMap
    (Representation.trivial ℂ (SU N) ℂ) where
  toLinearMap := TensorProduct.lift (dotProductBilin ℂ ℂ)
  isIntertwining' g := TensorProduct.ext' fun v w => by
    change (g.1 *ᵥ v) ⬝ᵥ ((g⁻¹).1ᵀ *ᵥ w) = v ⬝ᵥ w
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, val_inv_mul_val, one_mulVec]

/-- The contraction of an anti-fundamental against a fundamental index, the dot product
  `w ⊗ v ↦ ∑ wᵢ vᵢ`. -/
noncomputable def antiFundContr : ((antiFundRep N).tprod (fundRep N)).IntertwiningMap
    (Representation.trivial ℂ (SU N) ℂ) where
  toLinearMap := TensorProduct.lift (dotProductBilin ℂ ℂ)
  isIntertwining' g := TensorProduct.ext' fun w v => by
    change ((g⁻¹).1ᵀ *ᵥ w) ⬝ᵥ (g.1 *ᵥ v) = w ⬝ᵥ v
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, val_inv_mul_val,
      one_mulVec, dotProduct_comm]

/-!

## D. The units

The unit of a color is determined by its contraction. For a contraction `V ⊗ W → ℂ`, an element
`U ∈ W ⊗ V` is sent to the endomorphism `x ↦ ∑ contr (x ⊗ wᵢ) vᵢ` of `V` (`coevalMap`), and `U` is
a unit exactly when this is the identity. When the contraction separates `W` the map is
injective, so a unit is unique, and it is invariant, its transform being sent to
`g ∘ id ∘ g⁻¹ = id`.

-/

section Coevaluation

variable {N} {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (SU N) V}
  {σ : Representation ℂ (SU N) W}

/-- The endomorphism `x ↦ ∑ contr (x ⊗ wᵢ) vᵢ` of `V` attached to `∑ wᵢ ⊗ vᵢ ∈ W ⊗ V`. -/
noncomputable def coevalMap (contr : (ρ.tprod σ).IntertwiningMap
    (Representation.trivial ℂ (SU N) ℂ)) : W ⊗[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V :=
  dualTensorHom ℂ V V ∘ₗ TensorProduct.map (TensorProduct.curry contr.toLinearMap).flip
    LinearMap.id

variable (contr : (ρ.tprod σ).IntertwiningMap (Representation.trivial ℂ (SU N) ℂ))

@[simp]
lemma coevalMap_tmul (w : W) (v x : V) :
    coevalMap contr (w ⊗ₜ v) x = contr (x ⊗ₜ w) • v := rfl

/-- The contraction of `x` against the first factor of `U` is `coevalMap contr U x`. -/
lemma lid_rTensor_assoc_symm_eq_coevalMap (x : V) (U : W ⊗[ℂ] V) :
    TensorProduct.lid ℂ V (contr.toLinearMap.rTensor V
      ((TensorProduct.assoc ℂ V W V).symm (x ⊗ₜ[ℂ] U))) = coevalMap contr U x := by
  induction U with
  | tmul w v => simp
  | add U U' hU hU' => simp only [tmul_add, map_add, hU, hU', LinearMap.add_apply]

/-- `coevalMap` is injective when the contraction separates `W`. -/
lemma coevalMap_injective [FiniteDimensional ℂ V]
    (h : Function.Injective (TensorProduct.curry contr.toLinearMap).flip) :
    Function.Injective (coevalMap contr) := by
  rw [coevalMap, LinearMap.coe_comp]
  exact (dualTensorHomEquiv ℂ V V).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap (M := V) _ h)

/-- Transforming both factors of `U` conjugates `coevalMap contr U`, by the invariance of the
  contraction. -/
lemma coevalMap_map (g : SU N) (U : W ⊗[ℂ] V) :
    coevalMap contr (TensorProduct.map (σ g) (ρ g) U)
      = ρ g ∘ₗ coevalMap contr U ∘ₗ ρ g⁻¹ := by
  induction U with
  | tmul w v =>
    refine LinearMap.ext fun x => ?_
    have h := LinearMap.congr_fun (contr.isIntertwining' g) (ρ g⁻¹ x ⊗ₜ[ℂ] w)
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.self_inv_apply, Representation.trivial_apply] at h
    simp only [TensorProduct.map_tmul, coevalMap_tmul, LinearMap.comp_apply, map_smul]
    exact congrArg (· • (ρ g) v) h
  | add U U' hU hU' => simp only [map_add, hU, hU', LinearMap.add_comp, LinearMap.comp_add]

/-- An element whose `coevalMap` is the identity is invariant, when the contraction separates
  `W`. -/
lemma map_eq_self_of_coevalMap_eq_id [FiniteDimensional ℂ V]
    (h : Function.Injective (TensorProduct.curry contr.toLinearMap).flip) {U : W ⊗[ℂ] V}
    (hU : coevalMap contr U = LinearMap.id) (g : SU N) :
    TensorProduct.map (σ g) (ρ g) U = U := by
  refine coevalMap_injective contr h ?_
  rw [coevalMap_map, hU]
  exact LinearMap.ext fun x => by simp

variable {contr} in
/-- The unit intertwining map `a ↦ a • U` of an invariant element `U ∈ W ⊗ V`. -/
noncomputable def unitOf {U : W ⊗[ℂ] V} (hU : ∀ g : SU N, TensorProduct.map (σ g) (ρ g) U = U) :
    (Representation.trivial ℂ (SU N) ℂ).IntertwiningMap (σ.tprod ρ) where
  toFun a := a • U
  map_add' a b := add_smul a b U
  map_smul' a b := smul_assoc a b U
  isIntertwining' g := LinearMap.ext fun a => by
    simp [Representation.tprod_apply, hU g]

@[simp]
lemma unitOf_apply {U : W ⊗[ℂ] V} (hU : ∀ g : SU N, TensorProduct.map (σ g) (ρ g) U = U)
    (a : ℂ) : unitOf hU a = a • U := rfl

end Coevaluation

/-- The element `∑ eᵢ ⊗ eᵢ` of `ℂᴺ ⊗ ℂᴺ`, the unit of the fundamental and of the anti-fundamental
  color. -/
noncomputable def pairUnitVal : (Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ) :=
  ∑ i, Pi.single i 1 ⊗ₜ Pi.single i 1

lemma comm_pairUnitVal : TensorProduct.comm ℂ _ _ (pairUnitVal N) = pairUnitVal N := by
  simp [pairUnitVal]

/-- The dot product separates vectors. -/
lemma dotProduct_flip_injective : Function.Injective
    (TensorProduct.curry (TensorProduct.lift (dotProductBilin ℂ ℂ) :
      (Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ) →ₗ[ℂ] ℂ)).flip := fun w w' h => funext fun i => by
  simpa [dotProductBilin] using LinearMap.congr_fun h (Pi.single i 1)

/-- Contracting against `∑ eᵢ ⊗ eᵢ` by the dot product is the identity. -/
lemma coevalMap_pairUnitVal {ρ σ : Representation ℂ (SU N) (Fin N → ℂ)}
    (contr : (ρ.tprod σ).IntertwiningMap (Representation.trivial ℂ (SU N) ℂ))
    (h : contr.toLinearMap = TensorProduct.lift (dotProductBilin ℂ ℂ)) :
    coevalMap contr (pairUnitVal N) = LinearMap.id := by
  have hc : ∀ v w : Fin N → ℂ, contr (v ⊗ₜ w) = v ⬝ᵥ w := fun v w => by
    rw [show contr (v ⊗ₜ w) = contr.toLinearMap (v ⊗ₜ w) from rfl, h]
    rfl
  refine LinearMap.ext fun x => funext fun j => ?_
  simp [pairUnitVal, map_sum, hc, Finset.sum_apply, Pi.single_apply]

/-- The unit of the fundamental color, `∑ eᵢ ⊗ eᵢ` in anti-fundamental ⊗ fundamental. -/
noncomputable def fundUnit : (Representation.trivial ℂ (SU N) ℂ).IntertwiningMap
    ((antiFundRep N).tprod (fundRep N)) :=
  unitOf (map_eq_self_of_coevalMap_eq_id (fundContr N) (dotProduct_flip_injective N)
    (coevalMap_pairUnitVal N (fundContr N) rfl))

/-- The unit of the anti-fundamental color, `∑ eᵢ ⊗ eᵢ` in fundamental ⊗ anti-fundamental. -/
noncomputable def antiFundUnit : (Representation.trivial ℂ (SU N) ℂ).IntertwiningMap
    ((fundRep N).tprod (antiFundRep N)) :=
  unitOf (map_eq_self_of_coevalMap_eq_id (antiFundContr N) (dotProduct_flip_injective N)
    (coevalMap_pairUnitVal N (antiFundContr N) rfl))

/-- The element `∑ b_a ⊗ bᵃ` of `su(N)_ℂ ⊗ su(N)_ℂ`, for the Gell-Mann basis `b` and its dual basis
  `bᵃ` under the trace form: the unit of the adjoint color. -/
noncomputable def adjUnitVal : (SUAlgebraComplexified N) ⊗[ℂ] (SUAlgebraComplexified N) :=
  ∑ a, adjBasis N a ⊗ₜ (traceForm N).dualBasis (traceForm_nondegenerate N) (adjBasis N) a

lemma coevalMap_adjUnitVal : coevalMap (adjContr N) (adjUnitVal N) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.id_apply]
  conv_rhs => rw [← ((traceForm N).dualBasis (traceForm_nondegenerate N)
    (adjBasis N)).sum_repr x]
  rw [adjUnitVal, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coevalMap_tmul, LinearMap.BilinForm.dualBasis_repr_apply]
  rfl

lemma coevalMap_comm_adjUnitVal :
    coevalMap (adjContr N) (TensorProduct.comm ℂ _ _ (adjUnitVal N)) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  have hb := LinearMap.BilinForm.dualBasis_dualBasis (traceForm_nondegenerate N)
    (traceForm_isSymm N) (adjBasis N)
  rw [LinearMap.id_apply]
  conv_rhs => rw [← ((traceForm N).dualBasis (traceForm_nondegenerate N)
    ((traceForm N).dualBasis (traceForm_nondegenerate N)
      (adjBasis N))).sum_repr x]
  simp_rw [LinearMap.BilinForm.dualBasis_repr_apply]
  rw [hb, adjUnitVal, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [TensorProduct.comm_tmul, coevalMap_tmul]
  rfl

/-- The unit of the adjoint color is symmetric. -/
lemma comm_adjUnitVal : TensorProduct.comm ℂ _ _ (adjUnitVal N) = adjUnitVal N :=
  coevalMap_injective (adjContr N) (adjContr_flip_injective N)
    ((coevalMap_comm_adjUnitVal N).trans (coevalMap_adjUnitVal N).symm)

/-- The unit of the adjoint color, `∑ b_a ⊗ bᵃ`. -/
noncomputable def adjUnit : (Representation.trivial ℂ (SU N) ℂ).IntertwiningMap
    ((adjRep N).tprod (adjRep N)) :=
  unitOf (map_eq_self_of_coevalMap_eq_id (adjContr N) (adjContr_flip_injective N)
    (coevalMap_adjUnitVal N))

end suTensor

/-!

## E. The tensor species

-/

open suTensor in
/-- The complex tensor species of `SU(N)`, with fundamental, anti-fundamental and adjoint
  indices. The fundamental and anti-fundamental colors are dual to each other, the adjoint
  color dual to itself. -/
noncomputable def suTensor (N : ℕ) : TensorSpecies ℂ suTensor.Color (SU N)
    (suTensor.modules N) (suTensor.basisIdx N) (suTensor.rep N)
    (suTensor.basis N) where
  τ
    | .fund => .antiFund
    | .antiFund => .fund
    | .adj => .adj
  τ_involution c := by cases c <;> rfl
  contr
    | .fund => fundContr N
    | .antiFund => antiFundContr N
    | .adj => adjContr N
  unit
    | .fund => fundUnit N
    | .antiFund => antiFundUnit N
    | .adj => adjUnit N
  contr_tmul_symm
    | .fund, x, y => dotProduct_comm x y
    | .antiFund, x, y => dotProduct_comm x y
    | .adj, x, y => trace_mul_comm (adjMat N x) (adjMat N y)
  -- Each unit is fixed by swapping its factors, and the cast along `τ (τ c) = c` is the identity.
  unit_symm c := by
    cases c <;>
    · dsimp only
      simp only [fundUnit, antiFundUnit, adjUnit, unitOf_apply, one_smul, comm_pairUnitVal,
        comm_adjUnitVal]
      exact (LinearMap.congr_fun (LinearMap.lTensor_id _ _) _).symm
  contr_unit
    | .fund, x => by
      dsimp only
      rw [lid_rTensor_assoc_symm_eq_coevalMap (fundContr N), fundUnit, unitOf_apply,
        one_smul, coevalMap_pairUnitVal N (fundContr N) rfl, LinearMap.id_apply]
    | .antiFund, x => by
      dsimp only
      rw [lid_rTensor_assoc_symm_eq_coevalMap (antiFundContr N), antiFundUnit, unitOf_apply,
        one_smul, coevalMap_pairUnitVal N (antiFundContr N) rfl, LinearMap.id_apply]
    | .adj, x => by
      dsimp only
      rw [lid_rTensor_assoc_symm_eq_coevalMap (adjContr N), adjUnit, unitOf_apply, one_smul,
        coevalMap_adjUnitVal, LinearMap.id_apply]

namespace suTensor

/-- Notation for the complex tensors of `SU(N)`: `SuT[N, c₁, …, cₙ]` is the type
  `(suTensor N).Tensor ![c₁, …, cₙ]` of tensors with index colors `c₁, …, cₙ`, for example
  `SuT[3, .fund, .antiFund, .adj]`. -/
syntax (name := suTensorSyntax) "SuT[" term,* "]" : term

macro_rules
  | `(SuT[$N:term, $term:term, $terms:term,*]) =>
    `((suTensor $N).Tensor (vecCons $term ![$terms,*]))
  | `(SuT[$N:term, $term:term]) => `((suTensor $N).Tensor (vecCons $term ![]))
  | `(SuT[$N:term]) => `((suTensor $N).Tensor vecEmpty)

end suTensor

/-!

## F. The colors are closed under adjoints

For unitary `g`, the matrix of `g⁻¹` on each color is the conjugate transpose of that of `g`: on
the fundamental color `g⁻¹ = g†`, on the anti-fundamental color `gᵀ = ((g⁻¹)ᵀ)†`, and on the
adjoint color, in the hermitian and orthogonal Gell-Mann basis, the matrix entries are
`tr (λ_a g λ_b g⁻¹) / 2`. So every list of colors is closed under adjoints, and the general results
on equivariant maps (`Physlib.Relativity.Tensors.Equivariant`) apply to the tensors of `SU(N)`:
the invariants in the range of an equivariant map out of `(suTensor N).Tensor c` come from invariant
tensors.

-/

namespace suTensor

variable {N}

lemma toMatrix_fundRep (g : SU N) :
    LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N)) (fundRep N g) = g.1 := by
  rw [LinearMap.toMatrix_eq_toMatrix', ← LinearMap.toMatrix'_toLin' g.1, Matrix.toLin'_apply']
  rfl

lemma toMatrix_antiFundRep (g : SU N) :
    LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N)) (antiFundRep N g)
      = (g⁻¹).1ᵀ := by
  rw [LinearMap.toMatrix_eq_toMatrix', ← LinearMap.toMatrix'_toLin' (g⁻¹).1ᵀ,
    Matrix.toLin'_apply']
  rfl

variable (N) in
/-- On every color, the matrix of `g⁻¹` is the conjugate transpose of the matrix of `g`. -/
lemma toMatrix_rep_inv (k : Color) (g : SU N) :
    LinearMap.toMatrix (basis N k) (basis N k) (rep N k g⁻¹)
      = (LinearMap.toMatrix (basis N k) (basis N k) (rep N k g))ᴴ := by
  cases k
  · change LinearMap.toMatrix _ _ (fundRep N g⁻¹) = (LinearMap.toMatrix _ _ (fundRep N g))ᴴ
    rw [toMatrix_fundRep, toMatrix_fundRep, val_inv]
    rfl
  · change LinearMap.toMatrix _ _ (antiFundRep N g⁻¹)
      = (LinearMap.toMatrix _ _ (antiFundRep N g))ᴴ
    rw [toMatrix_antiFundRep, toMatrix_antiFundRep, inv_inv, val_inv]
    ext i j
    simp
  · change adjMatrix g⁻¹ = (adjMatrix g)ᴴ
    ext a b
    rw [adjMatrix_inv, transpose_apply, conjTranspose_apply, star_adjMatrix_apply]

variable (N) in
/-- Every list of colors of the `SU(N)` tensors is closed under adjoints, with `g' = g⁻¹`. -/
lemma isAdjointClosed {n : ℕ} (c : Fin n → Color) : (suTensor N).IsAdjointClosed c :=
  fun g => ⟨g⁻¹, fun i => toMatrix_rep_inv N (c i) g⟩

end suTensor
