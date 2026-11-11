/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Physlib.Mathematics.ForMathlib.Contraction

/-!

# Semilinear maps of tensor products and of bases

A family of semilinear maps acts on a tensor product factor by factor, and two bases give the
conjugate-linear equivalence that conjugates the coordinates.

## i. Overview

Mathlib's `PiTensorProduct.map` applies a family of linear maps to `⨂[R] i, s i`, one per factor.
`PiTensorProduct.mapₛₗ` does the same for a family of maps that are semilinear along one ring
endomorphism `σ`, as conjugate-linear maps are along `star`. It sends `⨂ x i` to `⨂ f i (x i)` and
is semilinear along `σ`, since a scalar of any one factor passes through `σ` once.
`PiTensorProduct.congrₛₗ` is the equivalence of a family of semilinear equivalences.

A basis `b` of `M`, a basis `b'` of `M'` and an equivalence `e` of their labels give the
conjugate-linear equivalence `Module.Basis.starEquiv b b' e : M ≃ₗ⋆[R] M'`. It conjugates the
coordinates of a vector in `b` and reads them in `b'`, the coordinate at `μ` moving to `e μ`. A
conjugate-linear map that sends each `b μ` to `b' (e μ)` is this equivalence. Conjugating both
factors along the same labels conjugates the coordinate pairing of two bases. When conjugate-linear
maps of the two factors conjugate one invariant coordinate pairing into another, the map of the
second factor commutes with the group action when the map of the first does.

A semilinear equivalence keeps the finite rank, so a module and its conjugate have the same
dimension.

## ii. Key results

- `PiTensorProduct.mapₛₗ` applies a family of semilinear maps to a tensor product, and
  `PiTensorProduct.congrₛₗ` a family of semilinear equivalences, with
  `PiTensorProduct.congrₛₗ_congrₛₗ` : maps that undo the `f i` undo `congrₛₗ f`.
- `Module.Basis.starEquiv` conjugates the coordinates of `b` and reads them in `b'`, and
  `Module.Basis.eq_starEquiv` proves that it is the only conjugate-linear map sending `b μ` to
  `b' (e μ)`.
- `Module.Basis.star_coordPairing_starEquiv` proves that conjugating both factors conjugates the
  coordinate pairing, and `Module.Basis.map_rep_of_star_coordPairing` that a conjugation of
  invariant coordinate pairings commutes with the group action on the second factor when it does
  on the first.
- `LinearEquiv.finrank_eqₛₗ` : a semilinear equivalence keeps the finite rank.

## iii. Table of contents

- A. Semilinear maps of tensor products
- B. Conjugating the coordinates of a basis
- C. The rank under a semilinear equivalence

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct

/-!

## A. Semilinear maps of tensor products

-/

namespace PiTensorProduct

variable {ι R : Type*} [CommSemiring R] {s t : ι → Type*} [∀ i, AddCommMonoid (s i)]
  [∀ i, Module R (s i)] [∀ i, AddCommMonoid (t i)] [∀ i, Module R (t i)]

/-- The semilinear map `⨂ x i ↦ ⨂ f i (x i)` of a family of maps semilinear along `σ`. -/
noncomputable def mapₛₗ {σ : R →+* R} (f : Π i, s i →ₛₗ[σ] t i) :
    (⨂[R] i, s i) →ₛₗ[σ] ⨂[R] i, t i :=
  let φ : (⨂[R] i, s i) →+ ⨂[R] i, t i :=
    liftAddHom (fun p : R × Π i, s i => σ p.1 • tprod R fun i => f i (p.2 i))
      (fun r x i hx => by
        rw [(tprod R).map_coord_zero i (show f i (x i) = 0 by rw [hx, map_zero]), smul_zero])
      (fun x => by rw [map_zero, zero_smul])
      (fun r x i m₁ m₂ => by
        simp only [Function.apply_update (fun i => f i), map_add, ← smul_add,
          (tprod R).map_update_add])
      (fun r r' x => by rw [map_add, add_smul])
      (fun r x i r' => by
        simp only [Function.apply_update (fun i => f i), map_smulₛₗ, (tprod R).map_update_smul,
          Function.update_eq_self, smul_smul, map_mul, mul_comm])
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun r x => by
      induction x using PiTensorProduct.induction_on' with
      | tprodCoeff z x =>
        rw [smul_tprodCoeff']
        change σ (r • z) • (tprod R fun i => f i (x i)) =
          σ r • σ z • (tprod R fun i => f i (x i))
        rw [smul_eq_mul, map_mul, mul_smul]
      | add x y hx hy => rw [smul_add, φ.map_add, φ.map_add, hx, hy, smul_add] }

@[simp]
lemma mapₛₗ_tprod {σ : R →+* R} (f : Π i, s i →ₛₗ[σ] t i) (x : Π i, s i) :
    mapₛₗ f (tprod R x) = tprod R fun i => f i (x i) := by
  change σ 1 • (tprod R fun i => f i (x i)) = _
  rw [map_one, one_smul]

/-- The semilinear equivalence `⨂ x i ↦ ⨂ f i (x i)` of a family of semilinear equivalences. -/
noncomputable def congrₛₗ {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (f : Π i, s i ≃ₛₗ[σ] t i) : (⨂[R] i, s i) ≃ₛₗ[σ] ⨂[R] i, t i :=
  LinearEquiv.ofLinearMap (mapₛₗ fun i => (f i).toLinearMap)
    (mapₛₗ fun i => (f i).symm.toLinearMap)
    (PiTensorProduct.ext <| MultilinearMap.ext fun x => by simp)
    (PiTensorProduct.ext <| MultilinearMap.ext fun x => by simp)

@[simp]
lemma congrₛₗ_tprod {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (f : Π i, s i ≃ₛₗ[σ] t i) (x : Π i, s i) :
    congrₛₗ f (tprod R x) = tprod R fun i => f i (x i) :=
  mapₛₗ_tprod _ x

/-- Applying `congrₛₗ f` and then `congrₛₗ g`, for maps `g i` that undo the `f i`, gives back the
tensor. -/
lemma congrₛₗ_congrₛₗ {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (f : Π i, s i ≃ₛₗ[σ] t i) (g : Π i, t i ≃ₛₗ[σ'] s i) (h : ∀ i x, g i (f i x) = x)
    (x : ⨂[R] i, s i) : congrₛₗ g (congrₛₗ f x) = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [LinearEquiv.map_smulₛₗ, LinearEquiv.map_smulₛₗ, congrₛₗ_tprod, congrₛₗ_tprod,
      RingHomInvPair.comp_apply_eq]
    simp only [h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end PiTensorProduct

/-!

## B. Conjugating the coordinates of a basis

-/

namespace Module.Basis

variable {R : Type*} [CommSemiring R] [StarRing R] {ι ι' M M' : Type*} [AddCommMonoid M]
  [Module R M] [AddCommMonoid M'] [Module R M']

/-- The conjugate-linear equivalence that conjugates the coordinates of a vector in `b` and reads
them in `b'`, the coordinate at `μ` moving to `e μ`. -/
noncomputable def starEquiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') :
    M ≃ₗ⋆[R] M' :=
  b.repr.trans <| (Finsupp.mapRange.linearEquiv (starLinearEquiv R)).trans <|
    (Finsupp.domLCongr e).trans b'.repr.symm

/-- The coordinates of `starEquiv b b' e v` are the conjugates of those of `v`. -/
@[simp]
lemma repr_starEquiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') (v : M) (μ : ι') :
    b'.repr (starEquiv b b' e v) μ = star (b.repr v (e.symm μ)) := by
  simp only [starEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Finsupp.domLCongr_apply]
  rfl

/-- `starEquiv b b' e` sends the basis vector `b μ` to `b' (e μ)`. -/
@[simp]
lemma starEquiv_apply_self (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') (μ : ι) :
    starEquiv b b' e (b μ) = b' (e μ) := by
  simp [starEquiv, Finsupp.mapRange_single]

/-- Conjugating back along an inverse label map gives back the vector. -/
lemma starEquiv_starEquiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') (e' : ι' ≃ ι)
    (he : ∀ μ, e' (e μ) = μ) (v : M) : starEquiv b' b e' (starEquiv b b' e v) = v :=
  b.repr.injective <| Finsupp.ext fun μ => by
    simp [e'.symm_apply_eq.2 (he μ).symm]

/-- A conjugate-linear map that sends `b μ` to `b' (e μ)` is `starEquiv b b' e`. -/
lemma eq_starEquiv {F : Type*} [FunLike F M M']
    [SemilinearMapClass F (starRingEnd R) M M'] (b : Basis ι R M) (b' : Basis ι' R M')
    (e : ι ≃ ι') (f : F) (hf : ∀ μ, f (b μ) = b' (e μ)) (v : M) :
    f v = starEquiv b b' e v :=
  LinearMap.congr_fun (b.ext (f₁ := (f : M →ₗ⋆[R] M')) (f₂ := (starEquiv b b' e).toLinearMap)
    fun μ => by simp [hf]) v

/-- `starEquiv` intertwines `ρ` and `ρ'` when the matrix of `ρ'` is the conjugate of that of
`ρ`, `ρ'_{e ν, e μ} = (ρ_{ν μ})*`. -/
lemma starEquiv_map_of_repr (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι')
    (ρ : M →ₗ[R] M) (ρ' : M' →ₗ[R] M')
    (h : ∀ μ ν, b'.repr (ρ' (b' (e μ))) (e ν) = star (b.repr (ρ (b μ)) ν)) (v : M) :
    starEquiv b b' e (ρ v) = ρ' (starEquiv b b' e v) :=
  LinearMap.congr_fun (b.ext (f₁ := (starEquiv b b' e).toLinearMap.comp ρ)
    (f₂ := ρ'.comp (starEquiv b b' e).toLinearMap) fun μ =>
      b'.repr.injective <| Finsupp.ext fun ν => by
        obtain ⟨ν, rfl⟩ := e.surjective ν
        simpa using (h μ ν).symm) v

/-- Conjugating both factors along the same labels conjugates the coordinate pairing,
`(∑ μ, x^μ y_μ)* = ∑ μ, (x^μ)* (y_μ)*`. -/
lemma star_coordPairing_starEquiv [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    {N N' : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']
    (b₁ : Basis ι R M) (b₂ : Basis ι R N) (b₁' : Basis ι' R M') (b₂' : Basis ι' R N')
    (e : ι ≃ ι') (x : M) (y : N) :
    star (b₁.coordPairing b₂ (x ⊗ₜ y)) =
      b₁'.coordPairing b₂' (starEquiv b₁ b₁' e x ⊗ₜ starEquiv b₂ b₂' e y) := by
  rw [coordPairing_tmul, coordPairing_tmul]
  simp only [star_sum, star_mul']
  exact Fintype.sum_equiv e _ _ fun μ => by simp

/-- Let conjugate-linear maps `f` of `M` and `f'` of `N` conjugate the coordinate pairing of `b₁`
and `b₂` into that of `b₁'` and `b₂'`, both invariant. If `f` commutes with the group action, so
does `f'`. -/
lemma map_rep_of_star_coordPairing [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    {N N' G : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N'] [Group G]
    {ρ₁ : Representation R G M} {ρ₂ : Representation R G N} {ρ₁' : Representation R G M'}
    {ρ₂' : Representation R G N'} {b₁ : Basis ι R M} {b₂ : Basis ι R N} {b₁' : Basis ι' R M'}
    {b₂' : Basis ι' R N'}
    (h : ∀ g x y, b₁.coordPairing b₂ (ρ₁ g x ⊗ₜ ρ₂ g y) = b₁.coordPairing b₂ (x ⊗ₜ y))
    (h' : ∀ g x y, b₁'.coordPairing b₂' (ρ₁' g x ⊗ₜ ρ₂' g y) = b₁'.coordPairing b₂' (x ⊗ₜ y))
    (f : M ≃ₗ⋆[R] M') (f' : N ≃ₗ⋆[R] N')
    (hf' : ∀ u α, star (b₁.coordPairing b₂ (u ⊗ₜ α)) = b₁'.coordPairing b₂' (f u ⊗ₜ f' α))
    (hf : ∀ g v, f (ρ₁ g v) = ρ₁' g (f v)) (g : G) (α : N) :
    f' (ρ₂ g α) = ρ₂' g (f' α) := by
  have hr (u : M) (α : N) : b₁.coordPairing b₂ (u ⊗ₜ ρ₂ g α) =
      b₁.coordPairing b₂ (ρ₁ g⁻¹ u ⊗ₜ α) := by
    simpa using h g (ρ₁ g⁻¹ u) α
  have hr' (u : M') (α : N') : b₁'.coordPairing b₂' (u ⊗ₜ ρ₂' g α) =
      b₁'.coordPairing b₂' (ρ₁' g⁻¹ u ⊗ₜ α) := by
    simpa using h' g (ρ₁' g⁻¹ u) α
  refine (isPerfPair_coordPairing b₁' b₂').bijective_right.1 (LinearMap.ext fun u' => ?_)
  obtain ⟨u, rfl⟩ := f.surjective u'
  change b₁'.coordPairing b₂' (f u ⊗ₜ f' (ρ₂ g α)) = b₁'.coordPairing b₂' (f u ⊗ₜ ρ₂' g (f' α))
  rw [← hf', hr, hf', hf, hr']

end Module.Basis

/-!

## C. The rank under a semilinear equivalence

-/

namespace LinearEquiv

variable {R M M' : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M']
  [Module R M'] {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- A semilinear equivalence keeps the finite rank, as `v ↦ v̄` does. -/
lemma finrank_eqₛₗ (f : M ≃ₛₗ[σ] M') : Module.finrank R M = Module.finrank R M' := by
  simpa [Module.finrank] using congr(Cardinal.toNat $(lift_rank_eq_of_equiv_equiv σ f.toAddEquiv
    (Function.bijective_iff_has_inverse.mpr ⟨σ', fun _ => RingHomInvPair.comp_apply_eq,
      fun _ => RingHomInvPair.comp_apply_eq₂⟩) (map_smulₛₗ f)))

end LinearEquiv
