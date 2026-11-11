/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RepresentationTheory.Invariants
public import Physlib.Mathematics.ForMathlib.Contraction
public import Physlib.Mathematics.ForMathlib.TensorProductMatrix

/-!

# Tensors as linear maps through the coordinate pairing

Two bases with the same labels read a tensor of `M ⊗ U` as a linear map `N → U`.

## i. Overview

Mathlib reads a tensor of `Module.Dual R N ⊗ U` as a linear map `N → U`
(`dualTensorHomEquivOfBasis`). When `M` is paired with `N` by the coordinate pairing of two bases
`b` and `b'` with the same labels (`Module.Basis.coordPairing`), `M` plays the role of the dual of
`N`, so a tensor of `M ⊗ U` is a linear map `N → U`. For a covector index this reads a metric
`g_μν` as the map `v^μ ↦ v^μ g_μν`.

The delta `∑ I, b I ⊗ b' I` of the two bases is the tensor of the identity map. The matrix of the
linear map of `z` is the transpose of the matrix of components of `z`, so two tensors give inverse
maps when their matrices of components are inverse.

A tensor `z` of `M ⊗ M` gives the bilinear form `(u, v) ↦ ⟨v, z u⟩` on `N`. Swapping the factors
of `z` swaps its arguments, so the form is symmetric when `z` is and alternating when `z` is
antisymmetric.

When the coordinate pairing is invariant under representations of a group, the linear map of
`Λz` is `Λ ∘ z ∘ Λ⁻¹`, so `z` is invariant exactly when its linear map is an intertwining map,
and the delta is invariant.

A tensor `z` of `M ⊗ P` whose linear map `N → P` is bijective has an inverse, the tensor of
`Q ⊗ N` whose linear map `P → N` inverts it, for bases `d` of `P` and `d'` of `Q`. The inverse is
unique, involutive, and commutes with the group action. When the linear map of `z` is not
bijective the inverse is the junk value `0`, so every lemma about it assumes bijectivity.

## ii. Key results

- `Module.Basis.coordTensorHomEquiv` : a tensor of `M ⊗ U` as a linear map `N → U`.
- `Module.Basis.coordDelta` : the delta `∑ I, b I ⊗ b' I`, and
  `Module.Basis.coordTensorHomEquiv_coordDelta` : it is the identity map.
- `Module.Basis.toMatrix_coordTensorHomEquiv` : the matrix of the linear map is the transpose of
  the matrix of components.
- `Module.Basis.coordTensorHomEquiv_comp_of_mul_eq_one` : two tensors give inverse maps when their
  matrices of components are inverse.
- `Module.Basis.isSymm_coordTensorHomEquiv_of_comm_eq` and
  `Module.Basis.isAlt_coordTensorHomEquiv_of_comm_eq_neg` : the bilinear form `(u, v) ↦ ⟨v, z u⟩`
  is symmetric when `comm z = z` and alternating when `comm z = -z`.
- `Module.Basis.coordTensorHomEquiv_map_rep` : the linear map of `(Λ ⊗ f) z` is
  `f ∘ z ∘ Λ⁻¹`, and `Module.Basis.isIntertwiningMap_coordTensorHomEquiv_iff` : `z` is invariant
  exactly when its linear map is an intertwining map.
- `Module.Basis.coordDelta_invariant` : the delta is invariant.
- `Module.Basis.coordInverse` : the inverse of a tensor, with
  `Module.Basis.coordTensorHomEquiv_coordInverse_comp` and
  `Module.Basis.comp_coordTensorHomEquiv_coordInverse` : it is a left and a right inverse,
  `Module.Basis.coordInverse_eq_of_comp_eq_id` : it is unique,
  `Module.Basis.coordInverse_coordInverse` : `(z⁻¹)⁻¹ = z`, and
  `Module.Basis.coordInverse_map_rep` : `(Λz)⁻¹ = Λ(z⁻¹)`.

## iii. Table of contents

- A. Tensors as linear maps through the coordinate pairing
- B. The bilinear form of a tensor
- C. Equivariance
- D. The inverse

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace Module.Basis

open TensorProduct

/-!

## A. Tensors as linear maps through the coordinate pairing

-/

variable {R ι M N U U' : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup U] [Module R U] [AddCommGroup U']
    [Module R U']

/-- `M ⊗ U` as the linear maps `N → U`, reading `M` as the dual of `N` through the coordinate
pairing. It sends `x ⊗ y` to `v ↦ b'.coordPairing b (v ⊗ x) • y`. -/
noncomputable def coordTensorHomEquiv (b : Module.Basis ι R M) (b' : Module.Basis ι R N) :
    M ⊗[R] U ≃ₗ[R] (N →ₗ[R] U) :=
  (TensorProduct.congr (TensorProduct.curry (b'.coordPairing b)).flip.toPerfPair
    (LinearEquiv.refl R U)).trans (dualTensorHomEquivOfBasis b')

/-- A pure tensor `x ⊗ y` acts as `v ↦ b'.coordPairing b (v ⊗ x) • y`. -/
@[simp]
lemma coordTensorHomEquiv_tmul (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (x : M) (y : U)
    (v : N) : b.coordTensorHomEquiv b' (x ⊗ₜ[R] y) v = b'.coordPairing b (v ⊗ₜ[R] x) • y :=
  rfl

/-- Applying `f` to the second factor composes with `f`, `(id ⊗ f) z = f ∘ z`. -/
lemma coordTensorHomEquiv_lTensor (b : Module.Basis ι R M) (b' : Module.Basis ι R N)
    (f : U →ₗ[R] U') (z : M ⊗[R] U) :
    b.coordTensorHomEquiv b' (f.lTensor M z) = f ∘ₗ b.coordTensorHomEquiv b' z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => ext v; simp
  | add z z' hz hz' => simp only [map_add, hz, hz', LinearMap.comp_add]

/-- The delta `∑ I, b I ⊗ b' I` of two bases with the same labels. -/
noncomputable def coordDelta (b : Module.Basis ι R M) (b' : Module.Basis ι R N) : M ⊗[R] N :=
  ∑ I, b I ⊗ₜ b' I

/-- The delta read as a linear map is the identity. -/
lemma coordTensorHomEquiv_coordDelta (b : Module.Basis ι R M) (b' : Module.Basis ι R N) :
    b.coordTensorHomEquiv b' (b.coordDelta b') = LinearMap.id :=
  b'.ext fun J => by
    simp [coordDelta, coordPairing_basis_basis, Finset.sum_ite_eq]

omit [DecidableEq ι] in
/-- Swapping the factors of the delta swaps the bases,
`comm (∑ I, b I ⊗ b' I) = ∑ I, b' I ⊗ b I`. -/
lemma comm_coordDelta (b : Module.Basis ι R M) (b' : Module.Basis ι R N) :
    TensorProduct.comm R M N (b.coordDelta b') = b'.coordDelta b := by
  simp only [coordDelta, map_sum, TensorProduct.comm_tmul]

/-- The components of the delta form the identity matrix. -/
lemma tensorProduct_repr_coordDelta (b : Module.Basis ι R M) (b' : Module.Basis ι R N)
    (I J : ι) : (b.tensorProduct b').repr (b.coordDelta b') (I, J) = if I = J then 1 else 0 := by
  simp [coordDelta, Finsupp.single_apply]

/-- `coordTensorHomEquiv` in components, `(z v)_J = ∑ I, v_I z_{IJ}`. -/
lemma repr_coordTensorHomEquiv {κ N' : Type*} [AddCommGroup N'] [Module R N']
    (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (d : Module.Basis κ R N')
    (z : M ⊗[R] N') (v : N) (J : κ) :
    d.repr (b.coordTensorHomEquiv b' z v) J =
      ∑ I, b'.repr v I * (b.tensorProduct d).repr z (I, J) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy, mul_add, Finset.sum_add_distrib]
  | tmul x y => simp [coordPairing_tmul, Finset.sum_mul, mul_assoc, mul_comm (d.repr y J)]

/-- The matrix of `coordTensorHomEquiv z` is the transpose of the matrix of components of `z`. -/
lemma toMatrix_coordTensorHomEquiv {κ N' : Type*} [Fintype κ] [AddCommGroup N'] [Module R N']
    (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (d : Module.Basis κ R N') (z : M ⊗[R] N') :
    LinearMap.toMatrix b' d (b.coordTensorHomEquiv b' z) =
      (Matrix.of fun I J => (b.tensorProduct d).repr z (I, J)).transpose := by
  ext J I
  simp [LinearMap.toMatrix_apply, repr_coordTensorHomEquiv, Finsupp.single_apply]

/-- Two tensors of `M ⊗ M` and `N ⊗ N` give inverse linear maps when their matrices of
components multiply to the identity. -/
lemma coordTensorHomEquiv_comp_of_mul_eq_one (b : Module.Basis ι R M) (b' : Module.Basis ι R N)
    (F : M ⊗[R] M) (F' : N ⊗[R] N)
    (h : Matrix.of (fun I J => (b'.tensorProduct b').repr F' (I, J)) *
      Matrix.of (fun I J => (b.tensorProduct b).repr F (I, J)) = 1) :
    b.coordTensorHomEquiv b' F ∘ₗ b'.coordTensorHomEquiv b F' = LinearMap.id := by
  apply (LinearMap.toMatrix b b).injective
  rw [LinearMap.toMatrix_comp _ b', toMatrix_coordTensorHomEquiv, toMatrix_coordTensorHomEquiv,
    ← Matrix.transpose_mul, h, Matrix.transpose_one, LinearMap.toMatrix_id]

/-- Swapping the factors of `F` and `F'` swaps the order of composition, `F F' = 1` read along the
second factors from `F' F = 1` read along the first. -/
lemma coordTensorHomEquiv_comm_comp_comm (b : Module.Basis ι R M) (b' : Module.Basis ι R N)
    (F : M ⊗[R] M) (F' : N ⊗[R] N)
    (h : b'.coordTensorHomEquiv b F' ∘ₗ b.coordTensorHomEquiv b' F = LinearMap.id) :
    b.coordTensorHomEquiv b' (TensorProduct.comm R M M F) ∘ₗ
      b'.coordTensorHomEquiv b (TensorProduct.comm R N N F') = LinearMap.id := by
  -- The matrices of `comm F'` and `comm F` are the transposes of those in `h`.
  refine coordTensorHomEquiv_comp_of_mul_eq_one b b' _ _ ?_
  have h := congrArg (LinearMap.toMatrix b' b') h
  rw [LinearMap.toMatrix_comp _ b, toMatrix_coordTensorHomEquiv, toMatrix_coordTensorHomEquiv,
    LinearMap.toMatrix_id] at h
  convert h using 2 <;> ext <;> simp [tensorProduct_repr_comm]

/-!

## B. The bilinear form of a tensor

-/

/-- Swapping the factors of `z` swaps the arguments of `(u, v) ↦ ⟨v, z u⟩`. -/
lemma coordPairing_coordTensorHomEquiv_comm (b : Module.Basis ι R M) (b' : Module.Basis ι R N)
    (z : M ⊗[R] M) (u v : N) :
    b'.coordPairing b (v ⊗ₜ b.coordTensorHomEquiv b' (TensorProduct.comm R M M z) u) =
      b'.coordPairing b (u ⊗ₜ b.coordTensorHomEquiv b' z v) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, tmul_add, hz, hz']
  | tmul x y =>
    simp only [TensorProduct.comm_tmul, coordTensorHomEquiv_tmul, tmul_smul, map_smul,
      smul_eq_mul]
    exact mul_comm _ _

/-- The bilinear form `(u, v) ↦ ⟨v, z u⟩` is symmetric when `comm z = z`. -/
lemma isSymm_coordTensorHomEquiv_of_comm_eq (b : Module.Basis ι R M) (b' : Module.Basis ι R N)
    {z : M ⊗[R] M} (hz : TensorProduct.comm R M M z = z) :
    LinearMap.BilinForm.IsSymm
      ((TensorProduct.curry (b'.coordPairing b)).flip ∘ₗ b.coordTensorHomEquiv b' z) :=
  ⟨fun u v => by
    change _ = b'.coordPairing b (u ⊗ₜ b.coordTensorHomEquiv b' z v)
    rw [← coordPairing_coordTensorHomEquiv_comm, hz]
    rfl⟩

/-- The bilinear form `(u, v) ↦ ⟨v, z u⟩` is alternating when `comm z = -z`, over a ring of
characteristic zero. -/
lemma isAlt_coordTensorHomEquiv_of_comm_eq_neg [NoZeroDivisors R] [CharZero R]
    (b : Module.Basis ι R M) (b' : Module.Basis ι R N) {z : M ⊗[R] M}
    (hz : TensorProduct.comm R M M z = -z) :
    LinearMap.IsAlt ((TensorProduct.curry (b'.coordPairing b)).flip ∘ₗ
      b.coordTensorHomEquiv b' z) := by
  refine LinearMap.isAlt_iff_eq_neg_flip.mpr (LinearMap.ext₂ fun u v => ?_)
  change b'.coordPairing b (v ⊗ₜ b.coordTensorHomEquiv b' z u) =
    -b'.coordPairing b (u ⊗ₜ b.coordTensorHomEquiv b' z v)
  rw [← coordPairing_coordTensorHomEquiv_comm, hz, map_neg, LinearMap.neg_apply, tmul_neg,
    map_neg]

/-!

## C. Equivariance

When the coordinate pairing of `b` and `b'` is invariant under representations `ρ` on `M` and `ρ'`
on `N`, the group acts on a tensor of `M ⊗ U` as `Λ ∘ z ∘ Λ⁻¹` on its linear map.

-/

section

variable {G : Type*} [Group G] {ρ : Representation R G M} {ρ' : Representation R G N}
  {b : Module.Basis ι R M} {b' : Module.Basis ι R N}

/-- The linear map of `(Λ ⊗ f) z` is `f ∘ z ∘ Λ⁻¹` when the coordinate pairing is invariant. -/
lemma coordTensorHomEquiv_map_rep
    (hρ : ∀ g x y, b.coordPairing b' (ρ g x ⊗ₜ ρ' g y) = b.coordPairing b' (x ⊗ₜ y))
    (f : U →ₗ[R] U') (z : M ⊗[R] U) (g : G) :
    b.coordTensorHomEquiv b' (TensorProduct.map (ρ g) f z) =
      f ∘ₗ b.coordTensorHomEquiv b' z ∘ₗ ρ' g⁻¹ := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz', LinearMap.add_comp, LinearMap.comp_add]
  | tmul x y =>
    ext v
    simpa [coordPairing_comm b' b] using
      congrArg (· • f y) (hρ g x (ρ' g⁻¹ v))

/-- The linear map of `(Λ ⊗ f) z` is bijective when those of `f` and `z` are. -/
lemma bijective_coordTensorHomEquiv_map_rep
    (hρ : ∀ g x y, b.coordPairing b' (ρ g x ⊗ₜ ρ' g y) = b.coordPairing b' (x ⊗ₜ y))
    {f : U →ₗ[R] U'} (hf : Function.Bijective f) {z : M ⊗[R] U}
    (hz : Function.Bijective (b.coordTensorHomEquiv b' z)) (g : G) :
    Function.Bijective (b.coordTensorHomEquiv b' (TensorProduct.map (ρ g) f z)) := by
  rw [coordTensorHomEquiv_map_rep hρ, LinearMap.coe_comp, LinearMap.coe_comp]
  exact hf.comp (hz.comp (ρ'.apply_bijective g⁻¹))

/-- A tensor is invariant exactly when its linear map is an intertwining map. -/
lemma isIntertwiningMap_coordTensorHomEquiv_iff
    (hρ : ∀ g x y, b.coordPairing b' (ρ g x ⊗ₜ ρ' g y) = b.coordPairing b' (x ⊗ₜ y))
    {σ : Representation R G U} (z : M ⊗[R] U) :
    ρ'.IsIntertwiningMap σ (b.coordTensorHomEquiv b' z) ↔
      ∀ g, TensorProduct.map (ρ g) (σ g) z = z := by
  rw [← Representation.mem_linHom_invariants_iff_isIntertwining]
  exact forall_congr' fun g => by
    rw [← (b.coordTensorHomEquiv b').injective.eq_iff, coordTensorHomEquiv_map_rep hρ]

/-- The delta is invariant when the coordinate pairing is. -/
lemma coordDelta_invariant
    (hρ : ∀ g x y, b.coordPairing b' (ρ g x ⊗ₜ ρ' g y) = b.coordPairing b' (x ⊗ₜ y)) (g : G) :
    TensorProduct.map (ρ g) (ρ' g) (b.coordDelta b') = b.coordDelta b' :=
  (isIntertwiningMap_coordTensorHomEquiv_iff hρ _).1
    (by rw [coordTensorHomEquiv_coordDelta]; exact ⟨fun _ _ => rfl⟩) g

end

/-!

## D. The inverse

A tensor `z` of `M ⊗ P` is a linear map `N → P`. Its inverse is the tensor of `Q ⊗ N` whose linear
map `P → N` inverts it, read through the bases `d` of `P` and `d'` of `Q`.

-/

section

variable {κ P Q : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] (b : Module.Basis ι R M) (b' : Module.Basis ι R N)
  (d : Module.Basis κ R P) (d' : Module.Basis κ R Q)

open scoped Classical in
/-- The inverse of `z : M ⊗ P`, the tensor of `Q ⊗ N` whose linear map `P → N` inverts that of `z`,
and the junk value `0` when the linear map of `z` is not bijective. -/
noncomputable def coordInverse (z : M ⊗[R] P) : Q ⊗[R] N :=
  if h : Function.Bijective (b.coordTensorHomEquiv b' z) then
    (d'.coordTensorHomEquiv d).symm (LinearEquiv.ofBijective _ h).symm.toLinearMap
  else 0

variable {b b' d d'}

/-- The linear map of the inverse is the inverse of the linear map. -/
lemma coordTensorHomEquiv_coordInverse {z : M ⊗[R] P}
    (h : Function.Bijective (b.coordTensorHomEquiv b' z)) :
    d'.coordTensorHomEquiv d (b.coordInverse b' d d' z) =
      (LinearEquiv.ofBijective _ h).symm.toLinearMap := by
  simp [coordInverse, h]

/-- The linear map of the inverse is bijective. -/
lemma bijective_coordTensorHomEquiv_coordInverse {z : M ⊗[R] P}
    (h : Function.Bijective (b.coordTensorHomEquiv b' z)) :
    Function.Bijective (d'.coordTensorHomEquiv d (b.coordInverse b' d d' z)) := by
  rw [coordTensorHomEquiv_coordInverse h]
  exact (LinearEquiv.ofBijective _ h).symm.bijective

/-- The inverse is a left inverse, as linear maps. -/
lemma coordTensorHomEquiv_coordInverse_comp {z : M ⊗[R] P}
    (h : Function.Bijective (b.coordTensorHomEquiv b' z)) :
    d'.coordTensorHomEquiv d (b.coordInverse b' d d' z) ∘ₗ b.coordTensorHomEquiv b' z =
      LinearMap.id := by
  rw [coordTensorHomEquiv_coordInverse h]
  exact (LinearEquiv.ofBijective _ h).symm_comp

/-- The inverse is a right inverse, as linear maps. -/
lemma comp_coordTensorHomEquiv_coordInverse {z : M ⊗[R] P}
    (h : Function.Bijective (b.coordTensorHomEquiv b' z)) :
    b.coordTensorHomEquiv b' z ∘ₗ d'.coordTensorHomEquiv d (b.coordInverse b' d d' z) =
      LinearMap.id := by
  rw [coordTensorHomEquiv_coordInverse h]
  exact (LinearEquiv.ofBijective _ h).comp_symm

/-- A tensor `w` whose linear map is a left inverse of that of `z` is the inverse of `z`. -/
lemma coordInverse_eq_of_comp_eq_id {z : M ⊗[R] P}
    (h : Function.Bijective (b.coordTensorHomEquiv b' z)) {w : Q ⊗[R] N}
    (hw : d'.coordTensorHomEquiv d w ∘ₗ b.coordTensorHomEquiv b' z = LinearMap.id) :
    b.coordInverse b' d d' z = w :=
  (d'.coordTensorHomEquiv d).injective <| (LinearMap.cancel_right h.2).1 <| by
    rw [coordTensorHomEquiv_coordInverse_comp h, hw]

/-- The inverse of the inverse is the tensor itself. -/
lemma coordInverse_coordInverse {z : M ⊗[R] P}
    (h : Function.Bijective (b.coordTensorHomEquiv b' z)) :
    d'.coordInverse d b' b (b.coordInverse b' d d' z) = z :=
  coordInverse_eq_of_comp_eq_id (bijective_coordTensorHomEquiv_coordInverse h)
    (comp_coordTensorHomEquiv_coordInverse h)

/-- The inverse commutes with the group action, `(Λz)⁻¹ = Λ(z⁻¹)`, when the coordinate pairings of
`b` and `b'` and of `d` and `d'` are invariant. -/
lemma coordInverse_map_rep {G : Type*} [Group G] {ρ : Representation R G M}
    {ρ' : Representation R G N} {σ : Representation R G P} {σ' : Representation R G Q}
    (hρ : ∀ g x y, b.coordPairing b' (ρ g x ⊗ₜ ρ' g y) = b.coordPairing b' (x ⊗ₜ y))
    (hσ : ∀ g x y, d.coordPairing d' (σ g x ⊗ₜ σ' g y) = d.coordPairing d' (x ⊗ₜ y))
    {z : M ⊗[R] P} (h : Function.Bijective (b.coordTensorHomEquiv b' z)) (g : G) :
    b.coordInverse b' d d' (TensorProduct.map (ρ g) (σ g) z) =
      TensorProduct.map (σ' g) (ρ' g) (b.coordInverse b' d d' z) := by
  have hσ' : ∀ g x y, d'.coordPairing d (σ' g x ⊗ₜ σ g y) = d'.coordPairing d (x ⊗ₜ y) :=
    fun g x y => by rw [coordPairing_comm, hσ, coordPairing_comm]
  refine coordInverse_eq_of_comp_eq_id
    (bijective_coordTensorHomEquiv_map_rep hρ (σ.apply_bijective g) h g) (LinearMap.ext fun x => ?_)
  simp [coordTensorHomEquiv_map_rep hρ, coordTensorHomEquiv_map_rep hσ',
    Representation.inv_self_apply, Representation.self_inv_apply,
    ← LinearMap.comp_apply (d'.coordTensorHomEquiv d _), coordTensorHomEquiv_coordInverse_comp h]

end

end Module.Basis
