/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.Bispinors.BispinorMatrix
public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.CentreEigenspace
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Exponential
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Vector.InvariantCoeff
/-!
# The complexified Lorentz group acting on Weyl tensors

The complex Lorentz tensors with Weyl colours carry an action of `SL(2, ℂ) × SL(2, ℂ)` with the
same invariant tensors as `SL(2, ℂ)`.

## i. Overview

The complexified Lorentz group `SL(2, ℂ) × SL(2, ℂ)` acts on the complex Lorentz tensors with Weyl
colours, `(M, N)` acting on each undotted index by `M`, on each dotted index by `N`, and on their
duals by the inverse transposes (`complexifiedAction`, A.1). Restricted along the complexification
`M ↦ (M, M̄)` it is the action of `SL(2, ℂ)` (A.2).

On undotted indices followed by dotted ones, each factor acts on its own indices only. The
Reynolds elements of the two factors, applied one after the other, fix an invariant and send every
product of tensors to a product of invariant tensors, so the invariants of the complexified action
are spanned by the products of an invariant tensor of the undotted indices and one of the dotted
indices (B).

The invariant tensors of the two actions are the same (C). One direction is the restriction. For
the other, take a real square-zero `G`, such as `E` or `F`, and the line `1 + z G` in `SL(2, ℂ)`
(C.1). Along `t ↦ 1 + c₀ t G`, for real `t`, the matrices of the undotted colours are holomorphic
in `c₀ t` and those of the dotted colours antiholomorphic (C.2). So the derivative of the
components of an invariant tensor is `c₀` times the action of `G` on its undotted indices plus `c̄₀`
times that on its dotted ones, and it vanishes. Taking `c₀ = 1` and `c₀ = i` shows that `G` kills
the invariant tensor on its undotted indices alone. The components along `s ↦ (1 + s z G, 1)` then
have derivative zero at the identity, hence everywhere by the group law, so the invariant tensor is
fixed by `(1 + z G, 1)` (C.3). These elements generate `SL(2, ℂ) × 1`, and
`(1, N) = (N̄, N) (N̄⁻¹, 1)` (C.4). With B, the invariant tensors with undotted indices followed by
dotted ones are spanned by products of invariant tensors of each chirality,
`invariants_append_eq_map₂_prodT`.

Two consequences follow here. A left- and a right-handed Weyl index carry no invariant tensor, the
element `-1` negating a single Weyl index, and with them neither do the ranges of equivariant maps
out of such tensors (D). The Pauli matrices change `n` four-vector indices into `n` left- and `n`
right-handed Weyl indices, `pauliTensorMap`, injectively and equivariantly. For odd `n` the
invariants on the Weyl side are products of invariants of `n` left-handed indices, of which there
are none, so an odd number of four-vector indices carries no invariant tensor (E). The bispinor
classifications of `PhyslibAlpha.Relativity.Bispinors.MetricPairing` and the classification of
four four-vector indices in `PhyslibAlpha.Relativity.Tensors.ComplexTensor.Vector.ContractionTensor`
build on the same results.

## ii. Key results

- `complexLorentzTensor.complexifiedAction` : the action of `SL(2, ℂ) × SL(2, ℂ)` on the complex
  Lorentz tensors with Weyl colours.
- `Lorentz.SL2C.toComplexified` : the complexification `M ↦ (M, M̄)`.
- `complexLorentzTensor.complexifiedAction_comp_toComplexified` : restricted along it, the
  complexified action is the action of `SL(2, ℂ)`.
- `complexLorentzTensor.invariants_complexifiedAction_append` : on undotted indices followed by
  dotted ones, the complexified invariants are spanned by products of invariants.
- `complexLorentzTensor.invariants_complexifiedAction` : the two actions have the same invariant
  tensors.
- `complexLorentzTensor.invariants_append_eq_map₂_prodT` : the invariant tensors with undotted
  indices followed by dotted ones are spanned by products of invariants.
- `complexLorentzTensor.invariants_upL_upR_eq_bot` : a left- and a right-handed Weyl index carry
  no invariant tensor.
- `Lorentz.reducesInvariantsTo_bot_leftRight` : nor does the range of an equivariant map out of
  them or out of their duals.
- `complexLorentzTensor.pauliTensorMap` : the Pauli change of indices on tensors.
- `complexLorentzTensor.invariants_up_pow_eq_bot_of_odd` : an odd number of four-vector indices
  carries no invariant tensor.
- `Lorentz.ComplexVector.reducesInvariantsTo_bot_of_odd` : nor does the range of an equivariant
  map out of them.

## iii. Table of contents

- A. The complexified action
  - A.1. The action of `SL(2, ℂ) × SL(2, ℂ)`
  - A.2. The restriction to `SL(2, ℂ)`
- B. Undotted indices followed by dotted ones
- C. The invariants of the two actions agree
  - C.1. The unipotent lines
  - C.2. The derivatives of the colours
  - C.3. The derivative argument
  - C.4. The invariants
- D. A left- and a right-handed Weyl index
  - D.1. The invariant tensors
  - D.2. The reduction to zero
  - D.3. Peeling the pair spans off a Lorentz-stable submodule
- E. Four-vector indices through the Pauli matrices
  - E.1. The Pauli change of indices on tensors
  - E.2. An odd number of four-vector indices

## iv. References

* R. F. Streater and A. S. Wightman, *PCT, Spin and Statistics, and All That*.

-/

@[expose] public section

open Matrix MatrixGroups

namespace complexLorentzTensor

open TensorSpecies Tensor Lorentz.SL2C TensorProduct

/-!

## A. The complexified action

### A.1. The action of `SL(2, ℂ) × SL(2, ℂ)`

-/

/-- The factor of the complexified Lorentz group `SL(2, ℂ) × SL(2, ℂ)` under which a colour
  transforms. The undotted colours `upL` and `downL` transform under the first factor `M`. The
  dotted colours `upR` and `downR`, whose representations are conjugate, transform under the
  conjugate of the second factor `N`, so that a dotted index transforms under `N` itself. The
  vector colours, which carry an index of each kind, are not part of the construction, and are put
  under the first factor only so that every colour has one. -/
def complexifiedFactor : Color → SL(2,ℂ) × SL(2,ℂ) →* SL(2,ℂ)
  | .upR => (SpecialLinearGroup.map (starRingEnd ℂ)).comp (MonoidHom.snd _ _)
  | .downR => (SpecialLinearGroup.map (starRingEnd ℂ)).comp (MonoidHom.snd _ _)
  | _ => MonoidHom.fst _ _

/-- A colour and its dual transform under the same factor. -/
lemma complexifiedFactor_τ (k : Color) :
    complexifiedFactor (complexLorentzTensor.τ k) = complexifiedFactor k := by
  cases k <;> rfl

/-- The complexified Lorentz group `SL(2, ℂ) × SL(2, ℂ)` acting on the complex Lorentz tensors
  with Weyl colours: `(M, N)` acts on an undotted index by `M`, on a dotted index by `N`, and on
  their duals by the inverse transposes. -/
noncomputable def complexifiedAction {n : ℕ} (c : Fin n → Color) :
    Representation ℂ (SL(2,ℂ) × SL(2,ℂ)) ℂT(c) :=
  (complexLorentzTensor.restrict complexifiedFactor complexifiedFactor_τ).tensorRep c

variable {n : ℕ} {c : Fin n → Color}

/-- An element of `SL(2, ℂ) × SL(2, ℂ)` acts on the index `i` through the factor of its colour. -/
lemma complexifiedAction_apply (g : SL(2,ℂ) × SL(2,ℂ)) :
    complexifiedAction c g =
      PiTensorProduct.map fun i => complexLorentzTensor.rep (c i) (complexifiedFactor (c i) g) :=
  rfl

/-- The components of `g • t` under the complexified action. -/
lemma basis_repr_complexifiedAction (g : SL(2,ℂ) × SL(2,ℂ)) (t : ℂT(c))
    (φ : ComponentIdx (S := complexLorentzTensor) c) :
    (Tensor.basis c).repr (complexifiedAction c g t) φ = ∑ ψ, (∏ i, LinearMap.toMatrix
      (complexLorentzTensor.basis (c i)) (complexLorentzTensor.basis (c i))
      (complexLorentzTensor.rep (c i) (complexifiedFactor (c i) g)) (φ i) (ψ i)) *
      (Tensor.basis c).repr t ψ :=
  basis_repr_smul (S := complexLorentzTensor.restrict complexifiedFactor complexifiedFactor_τ)
    c g t φ

/-- The complexified action acts on a product of tensors factor by factor. -/
lemma complexifiedAction_prodT {m : ℕ} {c1 : Fin m → Color} (g : SL(2,ℂ) × SL(2,ℂ)) (t : ℂT(c))
    (t1 : ℂT(c1)) :
    complexifiedAction (Fin.append c c1) g (prodT t t1) =
      prodT (complexifiedAction c g t) (complexifiedAction c1 g t1) :=
  (prodT_equivariant (S := complexLorentzTensor.restrict complexifiedFactor complexifiedFactor_τ)
    g t t1).symm

end complexLorentzTensor

/-!

### A.2. The restriction to `SL(2, ℂ)`

-/

namespace Lorentz.SL2C

/-- The complexification `M ↦ (M, M̄)` of `SL(2, ℂ)` into the complexified Lorentz group
  `SL(2, ℂ) × SL(2, ℂ)`, with `M̄` the entrywise conjugate of `M`. -/
def toComplexified : SL(2,ℂ) →* SL(2,ℂ) × SL(2,ℂ) :=
  (MonoidHom.id _).prod (SpecialLinearGroup.map (starRingEnd ℂ))

/-- The complexification of `M` is `(M, M̄)`. -/
lemma toComplexified_apply (M : SL(2,ℂ)) :
    toComplexified M = (M, SpecialLinearGroup.map (starRingEnd ℂ) M) := rfl

/-- Conjugating an element of `SL(2, ℂ)` twice gives it back. -/
lemma map_starRingEnd_map_starRingEnd (M : SL(2,ℂ)) :
    SpecialLinearGroup.map (starRingEnd ℂ) (SpecialLinearGroup.map (starRingEnd ℂ) M) = M := by
  ext i j
  simp

end Lorentz.SL2C

namespace complexLorentzTensor

open TensorSpecies Tensor Lorentz.SL2C TensorProduct

variable {n : ℕ} {c : Fin n → Color}

/-- Each colour transforms under `M` when restricted along `M ↦ (M, M̄)`. -/
lemma complexifiedFactor_toComplexified (k : Color) (M : SL(2,ℂ)) :
    complexifiedFactor k (toComplexified M) = M := by
  cases k <;> simp [complexifiedFactor, toComplexified_apply, map_starRingEnd_map_starRingEnd]

/-- Restricted along `M ↦ (M, M̄)`, the complexified action is the action of `SL(2, ℂ)`. -/
lemma complexifiedAction_toComplexified (M : SL(2,ℂ)) :
    complexifiedAction c (toComplexified M) = complexLorentzTensor.tensorRep c M := by
  rw [complexifiedAction_apply]
  simp only [complexifiedFactor_toComplexified]
  rfl

/-- Restricted along `M ↦ (M, M̄)`, the complexified action is the action of `SL(2, ℂ)`. -/
lemma complexifiedAction_comp_toComplexified :
    (complexifiedAction c).comp toComplexified = complexLorentzTensor.tensorRep c :=
  MonoidHom.ext complexifiedAction_toComplexified

/-!

## B. Undotted indices followed by dotted ones

-/

variable {m : ℕ} {cL : Fin n → Color} {cR : Fin m → Color}

/-- On undotted colours the complexified action of `(M, N)` is the action of `M`. -/
lemma complexifiedAction_eq_tensorRep_fst (hL : ∀ i, cL i = .upL ∨ cL i = .downL)
    (g : SL(2,ℂ) × SL(2,ℂ)) :
    complexifiedAction cL g = complexLorentzTensor.tensorRep cL g.1 := by
  rw [complexifiedAction_apply]
  refine congrArg PiTensorProduct.map (funext fun i => ?_)
  rcases hL i with h | h <;> rw [h] <;> rfl

/-- On dotted colours the complexified action of `(M, N)` is the action of `N̄`, under which a
  dotted index transforms by `N`. -/
lemma complexifiedAction_eq_tensorRep_snd (hR : ∀ i, cR i = .upR ∨ cR i = .downR)
    (g : SL(2,ℂ) × SL(2,ℂ)) :
    complexifiedAction cR g =
      complexLorentzTensor.tensorRep cR (SpecialLinearGroup.map (starRingEnd ℂ) g.2) := by
  rw [complexifiedAction_apply]
  refine congrArg PiTensorProduct.map (funext fun i => ?_)
  rcases hR i with h | h <;> rw [h] <;> rfl

/-- The complexified action on a product of a tensor with undotted indices and one with dotted
  indices. -/
lemma complexifiedAction_append_prodT (hL : ∀ i, cL i = .upL ∨ cL i = .downL)
    (hR : ∀ i, cR i = .upR ∨ cR i = .downR) (g : SL(2,ℂ) × SL(2,ℂ)) (x : ℂT(cL)) (y : ℂT(cR)) :
    complexifiedAction (Fin.append cL cR) g (prodT x y) =
      prodT (complexLorentzTensor.tensorRep cL g.1 x)
        (complexLorentzTensor.tensorRep cR (SpecialLinearGroup.map (starRingEnd ℂ) g.2) y) := by
  rw [complexifiedAction_prodT, complexifiedAction_eq_tensorRep_fst hL,
    complexifiedAction_eq_tensorRep_snd hR]

/-- The invariants of the complexified action on undotted indices followed by dotted ones are
  spanned by the products of an invariant tensor of the undotted indices and one of the dotted
  indices. The Reynolds elements of the two factors, applied one after the other, fix an
  invariant and send every product of tensors to a product of invariant tensors. -/
lemma invariants_complexifiedAction_append (hL : ∀ i, cL i = .upL ∨ cL i = .downL)
    (hR : ∀ i, cR i = .upR ∨ cR i = .downR) :
    (complexifiedAction (Fin.append cL cR)).invariants =
      Submodule.map₂ (prodT (S := complexLorentzTensor))
        (complexLorentzTensor.tensorRep cL).invariants
        (complexLorentzTensor.tensorRep cR).invariants := by
  have hP := complexifiedAction_append_prodT hL hR
  refine le_antisymm (fun t ht => ?_) (Submodule.map₂_le.2 fun x hx y hy g => ?_)
  · obtain ⟨rL, hrL⟩ := complexLorentzTensor.hasReynolds cL
    obtain ⟨rR, hrR⟩ := complexLorentzTensor.hasReynolds cR
    let σ : SL(2,ℂ) →* SL(2,ℂ) := SpecialLinearGroup.map (starRingEnd ℂ)
    let ρL : Representation ℂ SL(2,ℂ) ℂT(Fin.append cL cR) :=
      (complexifiedAction (Fin.append cL cR)).comp (MonoidHom.inl _ _)
    let ρR : Representation ℂ SL(2,ℂ) ℂT(Fin.append cL cR) :=
      (complexifiedAction (Fin.append cL cR)).comp ((MonoidHom.inr _ _).comp σ)
    have hPL (x : ℂT(cL)) (y : ℂT(cR)) : ρL.asAlgebraHom rL (prodT x y) =
        prodT ((complexLorentzTensor.tensorRep cL).asAlgebraHom rL x) y :=
      (Representation.map_asAlgebraHom_apply (complexLorentzTensor.tensorRep cL) ρL
        (prodT.flip y) (fun h v => by simp [ρL, hP]) rL x).symm
    have hPR (x : ℂT(cL)) (y : ℂT(cR)) : ρR.asAlgebraHom rR (prodT x y) =
        prodT x ((complexLorentzTensor.tensorRep cR).asAlgebraHom rR y) :=
      (Representation.map_asAlgebraHom_apply (complexLorentzTensor.tensorRep cR) ρR (prodT x)
        (fun h v => by simp [ρR, σ, hP, map_starRingEnd_map_starRingEnd]) rR y).symm
    have ht' : ρL.asAlgebraHom rL (ρR.asAlgebraHom rR t) = t := by
      rw [Representation.asAlgebraHom_apply_of_mem_invariants ρR rR fun h => ht _,
        hrR.augmentation_eq_one, one_smul,
        Representation.asAlgebraHom_apply_of_mem_invariants ρL rL fun h => ht _,
        hrL.augmentation_eq_one, one_smul]
    have key (u : ℂT(cL) ⊗[ℂ] ℂT(cR)) : ρL.asAlgebraHom rL (ρR.asAlgebraHom rR
        (tensorEquivProd u)) ∈ Submodule.map₂ (prodT (S := complexLorentzTensor))
          (complexLorentzTensor.tensorRep cL).invariants
          (complexLorentzTensor.tensorRep cR).invariants := by
      induction u using TensorProduct.inductionOn with
      | tmul x y =>
        rw [show tensorEquivProd (x ⊗ₜ[ℂ] y) = prodT x y from TensorProduct.lift.tmul x y,
          hPR, hPL]
        exact Submodule.apply_mem_map₂ _ (hrL.apply_mem_invariants x trivial)
          (hrR.apply_mem_invariants y trivial)
      | add u v hu hv =>
        rw [map_add, map_add, map_add]
        exact add_mem hu hv
    obtain ⟨u, rfl⟩ :=
      (tensorEquivProd (S := complexLorentzTensor) (c := cL) (c1 := cR)).surjective t
    rw [← ht']
    exact key u
  · rw [hP, (Representation.mem_invariants _ _).1 hx, (Representation.mem_invariants _ _).1 hy]

end complexLorentzTensor

/-!

## C. The invariants of the two actions agree

### C.1. The unipotent lines

A square-zero matrix `G` with `det (1 + z G) = 1`, such as `E` or `F`, gives the line
`z ↦ 1 + z G` in `SL(2, ℂ)`, on which multiplication adds the parameters.

-/

namespace Lorentz.SL2C

section Unipotent

variable {G : Matrix (Fin 2) (Fin 2) ℂ}

/-- For a square-zero matrix `G`, the inverse of `1 + z G` is `1 - z G`. -/
lemma inv_one_add_smul (hGG : G * G = 0) (z : ℂ) : (1 + z • G)⁻¹ = 1 + (-z) • G :=
  Matrix.inv_eq_left_inv (by simp [add_mul, mul_add, hGG])

/-- For a square-zero matrix `G`, multiplying `1 + a G` and `1 + b G` adds the parameters. -/
lemma one_add_smul_mul_one_add_smul (hGG : G * G = 0) (a b : ℂ) :
    (1 + a • G) * (1 + b • G) = 1 + (a + b) • G := by
  simp [add_mul, mul_add, hGG, add_smul, add_assoc]

/-- The element `1 + z G` of `SL(2, ℂ)`, for a matrix `G` with `det (1 + z G) = 1` for every
  `z`, such as `E = !![0, 1; 0, 0]` or `F = !![0, 0; 1, 0]`. -/
def unipotentLine (hG : ∀ z : ℂ, (1 + z • G).det = 1) (z : ℂ) : SL(2,ℂ) := ⟨1 + z • G, hG z⟩

variable (hG : ∀ z : ℂ, (1 + z • G).det = 1)

@[simp]
lemma coe_unipotentLine (z : ℂ) : (unipotentLine hG z : Matrix (Fin 2) (Fin 2) ℂ) = 1 + z • G :=
  rfl

@[simp]
lemma unipotentLine_zero : unipotentLine hG 0 = 1 :=
  Subtype.ext (by simp)

/-- For a square-zero `G`, multiplication on the line `z ↦ 1 + z G` adds the parameters. -/
lemma unipotentLine_add (hGG : G * G = 0) (a b : ℂ) :
    unipotentLine hG (a + b) = unipotentLine hG a * unipotentLine hG b :=
  Subtype.ext (by rw [SpecialLinearGroup.coe_mul, coe_unipotentLine, coe_unipotentLine,
    coe_unipotentLine, one_add_smul_mul_one_add_smul hGG])

end Unipotent

end Lorentz.SL2C

/-!

### C.2. The derivatives of the colours

Along `t ↦ 1 + c₀ t G`, for real `t` and real `G`, the matrix of an undotted colour is holomorphic
in `c₀ t` and that of a dotted colour antiholomorphic, so its derivative at the identity is `c₀`
times an undotted generator plus `c̄₀` times a dotted one. Along `t ↦ (1 + c₀ t G, 1)` the dotted
colours do not move.

-/

namespace complexLorentzTensor

open TensorSpecies Tensor Lorentz.SL2C TensorProduct

variable {n : ℕ} {c : Fin n → Color} {m : ℕ} {cL : Fin n → Color} {cR : Fin m → Color}

section Unipotent

variable {G : Matrix (Fin 2) (Fin 2) ℂ}

/-- The derivative at the identity of the matrices of `t ↦ 1 + t G` on the undotted colours,
  `G` on `upL` and `-Gᵀ` on `downL`, and zero on the other colours. -/
def undottedGenerator (G : Matrix (Fin 2) (Fin 2) ℂ) : (k : Color) → basisIdx k → basisIdx k → ℂ
  | .upL => G
  | .downL => -Gᵀ
  | _ => 0

/-- The derivative at the identity of the matrices of `t ↦ 1 + t G`, for real `G`, on the dotted
  colours, `G` on `upR` and `-Gᵀ` on `downR`, and zero on the other colours. -/
def dottedGenerator (G : Matrix (Fin 2) (Fin 2) ℂ) : (k : Color) → basisIdx k → basisIdx k → ℂ
  | .upR => G
  | .downR => -Gᵀ
  | _ => 0

/-- The derivative on `upL`, written against the two generators. -/
lemma mul_eq_mul_add_star_mul_zero (c₀ x : ℂ) : c₀ * x = c₀ * x + star c₀ * 0 := by ring

/-- The derivative on `downL`, written against the two generators. -/
lemma neg_mul_eq_mul_neg_add_star_mul_zero (c₀ x : ℂ) : -c₀ * x = c₀ * -x + star c₀ * 0 := by
  ring

/-- The derivative on `upR`, written against the two generators. -/
lemma star_mul_eq_mul_zero_add_star_mul {x : ℂ} (hx : star x = x) (c₀ : ℂ) :
    star (c₀ * x) = c₀ * 0 + star c₀ * x := by
  rw [star_mul', hx]
  ring

/-- The derivative on `downR`, written against the two generators. -/
lemma star_neg_mul_eq_mul_zero_add_star_mul_neg {x : ℂ} (hx : star x = x) (c₀ : ℂ) :
    star (-c₀ * x) = c₀ * 0 + star c₀ * -x := by
  rw [star_mul', hx, star_neg]
  ring

variable (hG : ∀ z : ℂ, (1 + z • G).det = 1)
include hG

/-- At the identity of the line `t ↦ 1 + c₀ t G` the matrix of every colour is the unit
  matrix. -/
lemma toMatrix_rep_one_add_smul_zero (k : Color) (c₀ : ℂ) (p q : basisIdx k) :
    LinearMap.toMatrix (complexLorentzTensor.basis k) (complexLorentzTensor.basis k)
      (complexLorentzTensor.rep k (unipotentLine hG (c₀ * ((0 : ℝ) : ℂ)))) p q =
      if p = q then 1 else 0 := by
  rw [Complex.ofReal_zero, mul_zero, unipotentLine_zero, map_one, LinearMap.toMatrix_one,
    Matrix.one_apply]

/-- At the identity of the line `t ↦ (1 + c₀ t G, 1)` the matrix of every colour under the
  complexified action is the unit matrix. -/
lemma toMatrix_rep_complexifiedFactor_zero (k : Color) (c₀ : ℂ) (p q : basisIdx k) :
    LinearMap.toMatrix (complexLorentzTensor.basis k) (complexLorentzTensor.basis k)
      (complexLorentzTensor.rep k
        (complexifiedFactor k (unipotentLine hG (c₀ * ((0 : ℝ) : ℂ)), 1))) p q =
      if p = q then 1 else 0 := by
  rw [Complex.ofReal_zero, mul_zero, unipotentLine_zero, Prod.mk_one_one, map_one, map_one,
    LinearMap.toMatrix_one, Matrix.one_apply]

variable (hGG : G * G = 0) (hGr : ∀ p q, star (G p q) = G p q)
include hGG hGr

/-- Along the line `t ↦ 1 + c₀ t G` of `SL(2, ℂ)`, for a real square-zero `G`, the matrix of a
  Weyl colour has derivative `c₀` times its undotted generator plus `c̄₀` times its dotted
  generator at the identity. -/
lemma hasDerivAt_toMatrix_rep_one_add_smul {k : Color} (hk : k ≠ .up ∧ k ≠ .down) (c₀ : ℂ)
    (p q : basisIdx k) :
    HasDerivAt (fun t : ℝ => LinearMap.toMatrix (complexLorentzTensor.basis k)
      (complexLorentzTensor.basis k) (complexLorentzTensor.rep k (unipotentLine hG (c₀ * t))) p q)
      (c₀ * undottedGenerator G k p q + star c₀ * dottedGenerator G k p q) 0 := by
  have hD := Fermion.hasDerivAt_one_add_smul G c₀
  have hD' := Fermion.hasDerivAt_one_add_smul G (-c₀)
  have hinv (t : ℝ) : (unipotentLine hG (c₀ * t) : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ =
      1 + (-c₀ * t) • G := by
    rw [coe_unipotentLine, inv_one_add_smul hGG, neg_mul]
  cases k
  · exact ((hD p q).congr_deriv (mul_eq_mul_add_star_mul_zero c₀ (G p q))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => congrFun (congrFun (Lorentz.toMatrix_rep_upL _) p) q)
  · refine HasDerivAt.congr_of_eventuallyEq
      ((hD' q p).congr_deriv (neg_mul_eq_mul_neg_add_star_mul_zero c₀ (G q p)))
      (Filter.Eventually.of_forall fun t =>
        (congrFun (congrFun (Lorentz.toMatrix_rep_downL _) p) q).trans
          (by rw [transpose_apply, hinv]))
  · refine HasDerivAt.congr_of_eventuallyEq
      ((hD p q).star.congr_deriv (star_mul_eq_mul_zero_add_star_mul (hGr p q) c₀))
      (Filter.Eventually.of_forall fun t =>
        congrFun (congrFun (Lorentz.toMatrix_rep_upR _) p) q)
  · refine HasDerivAt.congr_of_eventuallyEq
      ((hD' q p).star.congr_deriv (star_neg_mul_eq_mul_zero_add_star_mul_neg (hGr q p) c₀))
      (Filter.Eventually.of_forall fun t =>
        (congrFun (congrFun (Lorentz.toMatrix_rep_downR _) p) q).trans
          (by rw [conjTranspose_apply, hinv]))
  · exact absurd rfl hk.1
  · exact absurd rfl hk.2

/-- Along the line `t ↦ (1 + c₀ t G, 1)` of the complexified Lorentz group, the matrix of a Weyl
  colour under the complexified action has derivative `c₀` times its undotted generator at the
  identity: the dotted colours transform under the second factor, which stays at the
  identity. -/
lemma hasDerivAt_toMatrix_rep_complexifiedFactor {k : Color} (hk : k ≠ .up ∧ k ≠ .down)
    (c₀ : ℂ) (p q : basisIdx k) :
    HasDerivAt (fun t : ℝ => LinearMap.toMatrix (complexLorentzTensor.basis k)
      (complexLorentzTensor.basis k)
      (complexLorentzTensor.rep k (complexifiedFactor k (unipotentLine hG (c₀ * t), 1))) p q)
      (c₀ * undottedGenerator G k p q) 0 := by
  have h := hasDerivAt_toMatrix_rep_one_add_smul hG hGG hGr hk c₀ p q
  have hσ : SpecialLinearGroup.map (starRingEnd ℂ) (1 : SL(2,ℂ)) = 1 := map_one _
  cases k
  · exact h.congr_deriv (mul_eq_mul_add_star_mul_zero c₀ _).symm
  · exact h.congr_deriv (mul_eq_mul_add_star_mul_zero c₀ _).symm
  · refine HasDerivAt.congr_of_eventuallyEq ((hasDerivAt_const (0 : ℝ)
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) p q)).congr_deriv (mul_zero c₀).symm)
      (Filter.Eventually.of_forall fun t => ?_)
    change LinearMap.toMatrix _ _ (complexLorentzTensor.rep .upR
      (SpecialLinearGroup.map (starRingEnd ℂ) 1)) p q = _
    rw [hσ, map_one, LinearMap.toMatrix_one]
  · refine HasDerivAt.congr_of_eventuallyEq ((hasDerivAt_const (0 : ℝ)
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) p q)).congr_deriv (mul_zero c₀).symm)
      (Filter.Eventually.of_forall fun t => ?_)
    change LinearMap.toMatrix _ _ (complexLorentzTensor.rep .downR
      (SpecialLinearGroup.map (starRingEnd ℂ) 1)) p q = _
    rw [hσ, map_one, LinearMap.toMatrix_one]
  · exact absurd rfl hk.1
  · exact absurd rfl hk.2

/-!

### C.3. The derivative argument

-/

variable (hc : ∀ i, c i ≠ .up ∧ c i ≠ .down)
include hc

/-- An invariant tensor with Weyl colours is killed by the undotted generator acting on its
  undotted indices, one at a time. Along the line `t ↦ 1 + c₀ t G` its components are constant,
  and their derivative is `c₀` times this action plus `c̄₀` times that on the dotted indices.
  Taking `c₀ = 1` and `c₀ = i` separates the two. -/
lemma sum_undottedGenerator_mul_repr_eq_zero {t : ℂT(c)}
    (ht : t ∈ (complexLorentzTensor.tensorRep c).invariants)
    (φ : ComponentIdx (S := complexLorentzTensor) c) :
    ∑ s, ∑ q, undottedGenerator G (c s) (φ s) q *
      (Tensor.basis c).repr t (Function.update φ s q) = 0 := by
  obtain ⟨X, hX⟩ : ∃ X, ∑ s, ∑ q, undottedGenerator G (c s) (φ s) q *
      (Tensor.basis c).repr t (Function.update φ s q) = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, ∑ s, ∑ q, dottedGenerator G (c s) (φ s) q *
      (Tensor.basis c).repr t (Function.update φ s q) = Y := ⟨_, rfl⟩
  have key (c₀ : ℂ) : c₀ * X + star c₀ * Y = 0 := by
    have h := SlotAction.hasDerivAt_sum_mul_prod (κ := fun s => basisIdx (c s))
      (K := fun t' s => LinearMap.toMatrix (complexLorentzTensor.basis (c s))
        (complexLorentzTensor.basis (c s))
        (complexLorentzTensor.rep (c s) (unipotentLine hG (c₀ * t'))))
      (fun s => toMatrix_rep_one_add_smul_zero hG (c s) c₀)
      (fun s => hasDerivAt_toMatrix_rep_one_add_smul hG hGG hGr (hc s) c₀)
      (fun ψ => (Tensor.basis c).repr t ψ) φ
    have hconst : (fun t' : ℝ => ∑ ψ, (Tensor.basis c).repr t ψ * ∏ s, LinearMap.toMatrix
        (complexLorentzTensor.basis (c s)) (complexLorentzTensor.basis (c s))
        (complexLorentzTensor.rep (c s) (unipotentLine hG (c₀ * t'))) (φ s) (ψ s)) =
        fun _ => (Tensor.basis c).repr t φ := funext fun t' => by
      have h1 := congrArg (fun x => (Tensor.basis c).repr x φ)
        ((Representation.mem_invariants _ _).1 ht (unipotentLine hG (c₀ * t')))
      simp only [tensorRep_apply, basis_repr_smul] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun ψ _ => mul_comm _ _
    rw [hconst] at h
    rw [← hX, ← hY]
    simpa only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc] using
      h.unique (hasDerivAt_const 0 _)
  rw [hX]
  have h1 := key 1
  have hI := key Complex.I
  simp only [star_one, one_mul, Complex.star_def, Complex.conj_I] at h1 hI
  have hAB : X - Y = 0 := (mul_eq_zero.1 (by linear_combination hI :
    Complex.I * (X - Y) = 0)).resolve_left Complex.I_ne_zero
  linear_combination (h1 + hAB) / 2

/-- An invariant tensor with Weyl colours is fixed by `(1 + z G, 1)` under the complexified
  action. Along `s ↦ (1 + s z G, 1)` the derivative of its components at the identity is `z` times
  the undotted generator acting on them, which vanishes, so by the group law they are constant. -/
lemma complexifiedAction_one_add_smul_one {t : ℂT(c)}
    (ht : t ∈ (complexLorentzTensor.tensorRep c).invariants) (z : ℂ) :
    complexifiedAction c (unipotentLine hG z, 1) t = t := by
  let F : ℝ → ℂT(c) →ₗ[ℂ] ℂT(c) := fun s => complexifiedAction c (unipotentLine hG (z * s), 1)
  have hF (s h : ℝ) : F (s + h) = F s ∘ₗ F h := by
    simp only [F, ← Module.End.mul_eq_comp, ← map_mul, Prod.mk_mul_mk, mul_one,
      Complex.ofReal_add, mul_add, unipotentLine_add hG hGG]
  have hF0 : F 0 = LinearMap.id := by
    simp only [F, Complex.ofReal_zero, mul_zero, unipotentLine_zero, Prod.mk_one_one, map_one]
    rfl
  have h := (Tensor.basis c).apply_eq_self_of_hasDerivAt_repr hF hF0 (v := t) (fun φ => ?_) 1
  · simpa [F] using h
  have hD := SlotAction.hasDerivAt_sum_mul_prod (κ := fun s => basisIdx (c s))
    (K := fun h s => LinearMap.toMatrix (complexLorentzTensor.basis (c s))
      (complexLorentzTensor.basis (c s)) (complexLorentzTensor.rep (c s)
        (complexifiedFactor (c s) (unipotentLine hG (z * h), 1))))
    (fun s => toMatrix_rep_complexifiedFactor_zero hG (c s) z)
    (fun s => hasDerivAt_toMatrix_rep_complexifiedFactor hG hGG hGr (hc s) z)
    (fun ψ => (Tensor.basis c).repr t ψ) φ
  refine HasDerivAt.congr_of_eventuallyEq (hD.congr_deriv ?_)
    (Filter.Eventually.of_forall fun h => ?_)
  · simp only [mul_assoc, ← Finset.mul_sum,
      sum_undottedGenerator_mul_repr_eq_zero hG hGG hGr hc ht φ, mul_zero]
  · change (Tensor.basis c).repr (complexifiedAction c _ t) φ = _
    rw [basis_repr_complexifiedAction]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

end Unipotent

/-!

### C.4. The invariants

`SL(2, ℂ)` is generated by the unipotent elements `1 + z E` and `1 + z F`, so an invariant tensor
with Weyl colours is fixed by `(M, 1)` for every `M`. It is fixed by `(M, M̄)`, being invariant,
and so by `(1, N) = (N̄, N) (N̄⁻¹, 1)` for every `N` as well.

-/

/-- An invariant tensor with Weyl colours is fixed by `(M, 1)` under the complexified action. -/
lemma complexifiedAction_mk_one_apply (hc : ∀ i, c i ≠ .up ∧ c i ≠ .down) {t : ℂT(c)}
    (ht : t ∈ (complexLorentzTensor.tensorRep c).invariants) (M : SL(2,ℂ)) :
    complexifiedAction c (M, 1) t = t := by
  have hU (z : ℂ) : complexifiedAction c (Fermion.upperUnipotent z, 1) t = t :=
    complexifiedAction_one_add_smul_one (G := !![0, 1; 0, 0])
      (fun z => (Fermion.upperUnipotent z).2) (by simp [← Matrix.ext_iff, Fin.forall_fin_two])
      (fun p q => by fin_cases p <;> fin_cases q <;> simp) hc ht z
  have hL (z : ℂ) : complexifiedAction c (Fermion.lowerUnipotent z, 1) t = t :=
    complexifiedAction_one_add_smul_one (G := !![0, 0; 1, 0])
      (fun z => (Fermion.lowerUnipotent z).2) (by simp [← Matrix.ext_iff, Fin.forall_fin_two])
      (fun p q => by fin_cases p <;> fin_cases q <;> simp) hc ht z
  obtain ⟨a, x, r, y, rfl⟩ := Fermion.exists_eq_lowerUnipotent_mul_upperUnipotent M
  rw [show ((Fermion.lowerUnipotent a * Fermion.upperUnipotent x * Fermion.lowerUnipotent r *
      Fermion.upperUnipotent y, 1) : SL(2,ℂ) × SL(2,ℂ)) = (Fermion.lowerUnipotent a, 1) *
      (Fermion.upperUnipotent x, 1) * (Fermion.lowerUnipotent r, 1) *
      (Fermion.upperUnipotent y, 1) by simp, map_mul, map_mul, map_mul]
  simp only [mul_apply_eq_comp, hU, hL]

/-- The invariant tensors with Weyl colours are the same for `SL(2, ℂ)` and for the complexified
  Lorentz group `SL(2, ℂ) × SL(2, ℂ)`. -/
lemma invariants_complexifiedAction (hc : ∀ i, c i ≠ .up ∧ c i ≠ .down) :
    (complexifiedAction c).invariants = (complexLorentzTensor.tensorRep c).invariants := by
  ext t
  refine ⟨fun ht g => ?_, fun ht => ?_⟩
  · rw [← complexifiedAction_toComplexified]
    exact ht _
  rw [Representation.mem_invariants_iff_comp_inl_inr]
  refine ⟨fun M => complexifiedAction_mk_one_apply hc ht M, fun N => ?_⟩
  let N' := SpecialLinearGroup.map (starRingEnd ℂ) N
  have e : MonoidHom.inr _ _ N = toComplexified N' * (N'⁻¹, 1) := by
    simp [N', toComplexified_apply, map_starRingEnd_map_starRingEnd]
  change complexifiedAction c (MonoidHom.inr _ _ N) t = t
  rw [e, map_mul, mul_apply_eq_comp, complexifiedAction_mk_one_apply hc ht,
    complexifiedAction_toComplexified]
  exact ht _

/-- The invariant tensors with undotted indices followed by dotted ones are spanned by the
  products of an invariant tensor of the undotted indices and one of the dotted indices. -/
lemma invariants_append_eq_map₂_prodT (hL : ∀ i, cL i = .upL ∨ cL i = .downL)
    (hR : ∀ i, cR i = .upR ∨ cR i = .downR) :
    (complexLorentzTensor.tensorRep (Fin.append cL cR)).invariants =
      Submodule.map₂ (prodT (S := complexLorentzTensor))
        (complexLorentzTensor.tensorRep cL).invariants
        (complexLorentzTensor.tensorRep cR).invariants := by
  rw [← invariants_complexifiedAction, invariants_complexifiedAction_append hL hR]
  refine Fin.addCases (fun j => ?_) (fun j => ?_)
  · rw [Fin.append_left]
    rcases hL j with h | h <;> simp [h]
  · rw [Fin.append_right]
    rcases hR j with h | h <;> simp [h]

/-!

## D. A left- and a right-handed Weyl index

### D.1. The invariant tensors

A tensor with a left- and a right-handed Weyl index is, by C, a combination of products of an
invariant tensor with one left-handed index and one with one right-handed index. The element `-1`
negates a single Weyl index, so there are none.

-/

/-- The only invariant tensor with a left- and a right-handed Weyl index is zero. -/
lemma invariants_upL_upR_eq_bot :
    (complexLorentzTensor.tensorRep ![.upL, .upR]).invariants = ⊥ := by
  have h := invariants_append_eq_map₂_prodT (cL := ![Color.upL]) (cR := ![Color.upR])
    (fun i => Or.inl (by fin_cases i; rfl)) (fun i => Or.inl (by fin_cases i; rfl))
  rw [invariants_eq_bot_of_odd_weyl (c := ![Color.upL]) (by decide), Submodule.map₂_bot_left] at h
  exact invariants_tensorRep_eq_bot_of_permT (IsReindexing.on_id.2 fun i => by fin_cases i <;> rfl)
    h

end complexLorentzTensor

namespace Lorentz

open Matrix MatrixGroups SL2C TensorSpecies complexLorentzTensor

/-!

### D.2. The reduction to zero

The dual colours `![.downL, .downR]` are the two indices of `![.upL, .upR]` dualised in turn, so
they carry no invariant tensor but zero either (`invariants_tensorRep_eq_bot_of_dual`).

-/

/-- The invariants of the range of an equivariant map out of the tensors with a left- and a
  right-handed Weyl index, or with their duals, reduce to `⊥`. A Lorentz invariant of
  `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, lies in `S`. -/
lemma reducesInvariantsTo_bot_leftRight {k k' : complexLorentzTensor.Color}
    (hk : (k = .upL ∧ k' = .upR) ∨ (k = .downL ∧ k' = .downR)) {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[k, k'] →ₗ[ℂ] B}
    (hf : complexLorentzTensor.IsEquivariant ![k, k'] repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) ⊥ := by
  refine hf.reducesInvariantsTo_bot (complexLorentzTensor.hasReynolds _) ?_
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact invariants_upL_upR_eq_bot
  · refine invariants_tensorRep_eq_bot_of_dual (c := ![.downL, .upR]) 1
      (invariants_tensorRep_eq_bot_of_dual 0 invariants_upL_upR_eq_bot fun j => ?_) fun j => ?_ <;>
      fin_cases j <;> rfl

/-!

### D.3. Peeling the pair spans off a Lorentz-stable submodule

An equivariant map out of `ℂT[.downL, .downR]` carries no invariant, so the span of its
components, here the join of the lines through them, reduces to `⊥`. Each such span is stable under
the Lorentz group, so `ReducesInvariantsTo.biSup` combines the reductions over a finite family of
them, and a whole join is discarded from a Lorentz-stable submodule.

-/

section Peeling

variable {B : Type} [AddCommGroup B] [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- A finite join of the spans of families with a dual left- and a dual right-handed Weyl index
  carries no Lorentz invariant modulo a Lorentz-stable submodule. Such a family has no invariant,
  so each span reduces to `⊥`, and `ReducesInvariantsTo.biSup` combines the reductions. A Lorentz
  invariant of the join together with `S` lies in `S`. -/
lemma mem_of_lorentz_invariant_biSup_dualLeftRightWeyl_span {ι : Type} [DecidableEq ι]
    {T : ι → Fin 2 × Fin 2 → B} (hT : ∀ i, complexLorentzTensor.IsEquivariant ![.downL, .downR]
      repLorentz (liftComponents (T i ∘ pairIdx)))
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (s : Finset ι)
    {x : B} (hx : x ∈ (⨆ i ∈ s, ⨆ l, ℂ ∙ T i l) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hr : ∀ i, (⨆ l, ℂ ∙ T i l) = LinearMap.range (liftComponents (S := complexLorentzTensor)
      (c := ![.downL, .downR]) (T i ∘ pairIdx)) := fun i => by
    rw [range_liftComponents_comp, Submodule.span_range_eq_iSup]
  simp_rw [hr] at hx
  simpa using ReducesInvariantsTo.biSup
    (fun i => reducesInvariantsTo_bot_leftRight (Or.inr ⟨rfl, rfl⟩) (hT i))
    (fun i => (hT i).isStableUnder_range) isStableUnder_bot s S hS x hx hinv

/-- The version of `mem_of_lorentz_invariant_biSup_dualLeftRightWeyl_span` joining over a
  whole finite index type. -/
lemma mem_of_lorentz_invariant_iSup_dualLeftRightWeyl_span {ι : Type} [Fintype ι]
    [DecidableEq ι] {T : ι → Fin 2 × Fin 2 → B}
    (hT : ∀ i, complexLorentzTensor.IsEquivariant ![.downL, .downR] repLorentz
      (liftComponents (T i ∘ pairIdx))) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ (⨆ i, ⨆ l, ℂ ∙ T i l) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  refine mem_of_lorentz_invariant_biSup_dualLeftRightWeyl_span hT S hS Finset.univ ?_ hinv
  refine sup_le_sup_right (iSup_le fun i => ?_) S hx
  exact le_iSup₂_of_le i (Finset.mem_univ i) le_rfl

end Peeling

end Lorentz

/-!

## E. Four-vector indices through the Pauli matrices

The Pauli matrices change each of `n` four-vector indices into a bispinor index, a left- and a
right-handed Weyl index (`Lorentz.pauliTransform`). Listing the `n` left-handed indices first and
then the `n` right-handed ones, this is an injective equivariant map `pauliTensorMap n` from the
tensors with `n` four-vector indices into the tensors with colours
`Fin.append (fun _ => .upL) (fun _ => .upR)` (E.1). By C the invariants of the latter are products
of invariants with `n` left-handed and with `n` right-handed indices. For odd `n` there are none,
the element `-1` negating an odd number of Weyl indices, and so the tensors with an odd number of
four-vector indices carry no invariant but zero (E.2).

### E.1. The Pauli change of indices on tensors

-/

namespace complexLorentzTensor

open TensorSpecies Tensor Lorentz

/-- The component indices of a tensor with `n` left-handed Weyl indices followed by `n`
  right-handed ones, as `n` bispinor indices, the `s`-th left-handed index paired with the `s`-th
  right-handed one. -/
noncomputable def bispinorIdx (n : ℕ) : ComponentIdx (S := complexLorentzTensor)
    (Fin.append (fun _ : Fin n => Color.upL) (fun _ : Fin n => Color.upR)) ≃
      (Fin n → Fin 2 × Fin 2) :=
  ComponentIdx.prod.trans (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin 2)
    (fun _ => Fin 2)).symm

/-- The matrix entry of a colour, transported along an equality of colours. -/
lemma toMatrix_rep_basisIdxCongr {k k' : Color} (h : k = k') (g : SL(2,ℂ)) (x y : basisIdx k) :
    LinearMap.toMatrix (complexLorentzTensor.basis k) (complexLorentzTensor.basis k)
      (complexLorentzTensor.rep k g) x y =
    LinearMap.toMatrix (complexLorentzTensor.basis k') (complexLorentzTensor.basis k')
      (complexLorentzTensor.rep k' g) (basisIdxCongr h x) (basisIdxCongr h y) := by
  subst h
  rfl

/-- On `n` bispinor indices, the product of the matrix entries of `g` over the `2 n` Weyl indices
  is the product of the entries of the bispinor matrix of `g`. -/
lemma prod_bispinorMatrix_bispinorIdx (n : ℕ) (g : SL(2,ℂ))
    (φ ψ : ComponentIdx (S := complexLorentzTensor)
      (Fin.append (fun _ : Fin n => Color.upL) (fun _ : Fin n => Color.upR))) :
    ∏ s, bispinorMatrix g (bispinorIdx n φ s) (bispinorIdx n ψ s) =
      ∏ i, LinearMap.toMatrix
        (complexLorentzTensor.basis (Fin.append (fun _ : Fin n => Color.upL) (fun _ => .upR) i))
        (complexLorentzTensor.basis (Fin.append (fun _ : Fin n => Color.upL) (fun _ => .upR) i))
        (complexLorentzTensor.rep (Fin.append (fun _ : Fin n => Color.upL) (fun _ => .upR) i) g)
        (φ i) (ψ i) := by
  rw [Fin.prod_univ_add, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [toMatrix_rep_basisIdxCongr (Fin.append_left _ _ s),
    toMatrix_rep_basisIdxCongr (Fin.append_right _ _ s)]
  exact congrArg₂ (· * ·) (congrFun (congrFun (toMatrix_rep_upL g) _) _).symm
    (congrFun (congrFun (toMatrix_rep_upR g) _) _).symm

/-- The change of every four-vector index of a tensor into a bispinor index by the covariant
  Pauli matrices, `μ ↦ (σ_μ)_{αα̇}`, landing in the tensors with the left-handed Weyl indices of
  the bispinor indices followed by their right-handed ones. -/
noncomputable def pauliTensorMap (n : ℕ) : ℂT(fun _ : Fin n => Color.up) →ₗ[ℂ]
    ℂT(Fin.append (fun _ : Fin n => Color.upL) (fun _ : Fin n => Color.upR)) :=
  (componentEquiv (bispinorIdx n)).symm.toLinearMap ∘ₗ pauliTransform ∘ₗ
    (coeffEquiv n).toLinearMap

/-- The Pauli change of indices commutes with `SL(2, ℂ)`. -/
lemma pauliTensorMap_smul (n : ℕ) (g : SL(2,ℂ)) (t : ℂT(fun _ : Fin n => Color.up)) :
    pauliTensorMap n (g • t) = g • pauliTensorMap n t := by
  apply (componentEquiv (bispinorIdx n)).injective
  rw [componentEquiv_smul (bispinorIdx n) (A := fun g a b => ∏ s, bispinorMatrix g (a s) (b s))
    (prod_bispinorMatrix_bispinorIdx n)]
  simp only [pauliTensorMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, coeffEquiv_smul]
  exact (act_bispinorMatrix_pauliTransform g _).symm

/-- The Pauli change of indices is injective. -/
lemma pauliTensorMap_injective (n : ℕ) : Function.Injective (pauliTensorMap n) :=
  (componentEquiv (bispinorIdx n)).symm.injective.comp
    (pauliTransform_injective.comp (coeffEquiv n).injective)

/-- The Pauli change of indices maps invariant tensors to invariant tensors. -/
lemma pauliTensorMap_mem_invariants {n : ℕ} {t : ℂT(fun _ : Fin n => Color.up)}
    (ht : t ∈ (complexLorentzTensor.tensorRep (fun _ : Fin n => Color.up)).invariants) :
    pauliTensorMap n t ∈ (complexLorentzTensor.tensorRep
      (Fin.append (fun _ : Fin n => Color.upL) (fun _ : Fin n => Color.upR))).invariants :=
  fun g => by
    rw [tensorRep_apply, ← pauliTensorMap_smul, ← tensorRep_apply,
      (Representation.mem_invariants _ _).1 ht g]

/-!

### E.2. An odd number of four-vector indices

-/

/-- There are no invariant tensors with an odd number of four-vector indices but zero. The Pauli
  change of indices sends them injectively to invariant tensors with `n` left- and `n`
  right-handed Weyl indices, products of invariants with `n` left-handed indices, of which there
  are none for odd `n`, the element `-1` negating them. -/
lemma invariants_up_pow_eq_bot_of_odd {n : ℕ} (hn : Odd n) :
    (complexLorentzTensor.tensorRep (fun _ : Fin n => Color.up)).invariants = ⊥ := by
  have hW : (complexLorentzTensor.tensorRep
      (Fin.append (fun _ : Fin n => Color.upL) (fun _ : Fin n => Color.upR))).invariants = ⊥ := by
    rw [invariants_append_eq_map₂_prodT (fun _ => Or.inl rfl) (fun _ => Or.inl rfl),
      invariants_eq_bot_of_odd_weyl (c := fun _ : Fin n => Color.upL) (by simpa using hn),
      Submodule.map₂_bot_left]
  refine Representation.invariants_eq_bot_of_forall fun t ht => pauliTensorMap_injective n ?_
  have h := pauliTensorMap_mem_invariants ht
  rw [hW, Submodule.mem_bot] at h
  rw [h, map_zero]

end complexLorentzTensor

namespace Lorentz

open complexLorentzTensor

/-- The range of an equivariant map out of the tensors with an odd number of four-vector indices
  reduces to `⊥`. A Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable
  submodule, lies in `S`. -/
lemma ComplexVector.reducesInvariantsTo_bot_of_odd {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {n : ℕ} (hn : Odd n)
    {f : ℂT(fun _ : Fin n => Color.up) →ₗ[ℂ] B}
    (hf : complexLorentzTensor.IsEquivariant (fun _ : Fin n => .up) repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) ⊥ :=
  TensorSpecies.IsEquivariant.reducesInvariantsTo_bot hf (complexLorentzTensor.hasReynolds _)
    (complexLorentzTensor.invariants_up_pow_eq_bot_of_odd hn)

end Lorentz
