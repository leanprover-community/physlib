/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Elab
public import Physlib.Relativity.Tensors.RealTensor.CoVector.Representation
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
/-!

# The species of real Lorentz tensors

Real Lorentz tensors in `d + 1` dimensions as a species, with the Minkowski metric `η`.

## i. Overview

Real Lorentz tensors have one kind of index, the vector index `vec`. An upper index has the color
`⟨vec, up⟩` and a lower index the color `⟨vec, down⟩`. A color is a label. The species assigns to
it a space: `V ⟨vec, up⟩ = Lorentz.Vector d`, the contravariant vectors `v^μ` with basis `e_μ`,
and `V ⟨vec, down⟩ = Lorentz.CoVector d`, the covariant vectors `w_μ` with basis `e^μ`. Both are
functions `Fin 1 ⊕ Fin d → ℝ` with Mathlib's analysis, so `V ⟨vec, up⟩ = ℝ⁴` for `d = 3`. The
labels `μ` run over `Fin 1 ⊕ Fin d`, with `Sum.inl 0` the time direction and `Sum.inr i` the space
directions. A Lorentz transformation `Λ : LorentzGroup d` acts on an upper index by
`(Λv)^μ = Λ^μ_ν v^ν` and on a lower index by `(Λw)_μ = (Λ⁻¹)^ν_μ w_ν`. The two colors are named
`realLorentz.up` and `realLorentz.down`, and `ℝT[d, up, down]` is the space of the tensors
`T^μ_ν`, under `open scoped Tensors.realLorentz`.

The contraction `u^μ w_μ` is the coordinate pairing `∑ μ, u^μ w_μ` of the two bases and the
delta is `δ_μ^ν = ∑ μ, e^μ ⊗ e_μ`. The one physical input is that the pairing is Lorentz invariant
(`realLorentz.coordPairing_rep`). The metric is `η = ∑ μ, η_μμ e_μ ⊗ e_μ` (`realLorentz.metric`),
with the matrix `diag(1, -1, …, -1)` at both colors.

So the general results apply. For example `η^μν η_νρ = δ^μ_ρ` is
`Species.contr_formTensor_formTensor` at `up`, and lowering an index, `v^μ ↦ v_ν = v^μ η_μν`, is
`(realLorentz d).toDual up`.

The Lorentz vectors and covectors, the spaces of the two colors, are tensors with one upper index
and one lower index respectively (`Tensorial`). A vector transforms by `Λ *ᵥ v` and a covector by
`(Λ⁻¹)ᵀ *ᵥ ω`, and both enter index notation directly, as in `{v | μ ⊗ ω | μ}ᵀ` for `v^μ ω_μ`.

## ii. Key results

- `realLorentz.coordPairing_rep` : the pairing `v^μ ω_μ` is Lorentz invariant.
- `realLorentz` : the species of real Lorentz tensors, with the colors `realLorentz.up` and
  `realLorentz.down` and the spaces of tensors `ℝT[d, up, down]` (scoped).
- `realLorentz.metric` and the instances `(realLorentz d).HasForm κ` and
  `(realLorentz d).IsSymmetricForm κ` : the Minkowski metric `η`.
- `realLorentz.tensorBasis_repr_formTensor` : the components of `η^μν` and `η_μν` are the
  Minkowski matrix, and `realLorentz.tensorBasis_repr_deltaTensor` : those of `δ` the identity.
- `realLorentz.vectorTensorial` and `realLorentz.coVectorTensorial` : Lorentz vectors and
  covectors as tensors, with the actions `Lorentz.Vector.rep` and `Lorentz.CoVector.rep`.
- `realLorentz.tensorBasis_repr_toTensor_vector` and
  `realLorentz.tensorBasis_repr_toTensor_coVector` : the components of the tensor of a vector or a
  covector are its components, and `realLorentz.toTensor_symm_vector_apply` : the converse for a
  vector. `realLorentz.toTensor_basis_vector` : a basis vector is a basis tensor.
- `realLorentz.tensorBasis_repr_toTensor_vector_tmul` and
  `realLorentz.tensorBasis_repr_toTensor_coVector_tmul` : the components of the tensor of an
  element of `Vector d ⊗ Vector d` or `CoVector d ⊗ Vector d` are its coordinates in the product
  basis.
- `realLorentz.tensorBasis_repr_contr_vector_coVector` : the contraction `v^μ ω_μ` is
  `∑ μ, v^μ ω_μ`, and `realLorentz.contr_vector_coVector_rep` : it is Lorentz invariant.
- `realLorentz.tensorBasis_repr_formTensor_contr_vector` : the Minkowski product `⟪v, w⟫ₘ` is the
  contraction `η_μν v^μ w^ν`.
- `realLorentz.basis_repr_toDual` and `realLorentz.tensorBasis_repr_toDualAt` : lowering or raising
  an index multiplies its component by `η_νν`.
- `Lorentz.Vector.tensorComponent` : the component `F^μν` of `F` in `Vector d ⊗ Vector d`.
- `realLorentz.tensorBasis_repr_toDualAt_contr_vector_tmul` : the contraction `F_μν G^μν` in
  components.

## iii. Table of contents

- A. The species
- B. The Minkowski metric
- C. Dual bases and components of the metric and the delta
- D. Lorentz vectors and covectors as tensors

## iv. References

-/

@[expose] public section

open TensorProduct Lorentz Matrix

namespace Tensors

/-!

## A. The species

-/

/-- The kinds of real Lorentz index. There is one, the vector index `vec`, carried up as `v^μ` and
down as `w_μ`. -/
inductive realLorentz.Kind
  /-- The Lorentz vector index. -/
  | vec

/-- The vector space of a real Lorentz index of color `c`: `Vector d` for an upper index and
`CoVector d` for a lower one. -/
def realLorentz.IndexSpace (d : ℕ) (c : Color realLorentz.Kind) : Type :=
  match c.variance.isUp with
  | true => Vector d
  | false => CoVector d

noncomputable instance (d : ℕ) : ∀ c, AddCommGroup (realLorentz.IndexSpace d c)
  | ⟨_, .up⟩ => inferInstanceAs (AddCommGroup (Vector d))
  | ⟨_, .down⟩ => inferInstanceAs (AddCommGroup (CoVector d))

noncomputable instance (d : ℕ) : ∀ c, Module ℝ (realLorentz.IndexSpace d c)
  | ⟨_, .up⟩ => inferInstanceAs (Module ℝ (Vector d))
  | ⟨_, .down⟩ => inferInstanceAs (Module ℝ (CoVector d))

namespace realLorentz

/-- The action of the Lorentz group on an index, `Vector.rep` up and `CoVector.rep` down. -/
noncomputable abbrev IndexSpace.rep (d : ℕ) :
    (c : Color Kind) → Representation ℝ (LorentzGroup d) (IndexSpace d c)
  | ⟨_, .up⟩ => Vector.rep
  | ⟨_, .down⟩ => CoVector.rep

/-- The basis of an index, `Vector.basis` up and `CoVector.basis` down. -/
noncomputable abbrev IndexSpace.basis (d : ℕ) :
    (c : Color Kind) → Module.Basis (Fin 1 ⊕ Fin d) ℝ (IndexSpace d c)
  | ⟨_, .up⟩ => Vector.basis
  | ⟨_, .down⟩ => CoVector.basis

/-- The coordinate pairing of `Vector.basis` and `CoVector.basis` is `v^μ ω_μ = v ⬝ᵥ ω`. -/
lemma coordPairing_vector_coVector (d : ℕ) (v : Vector d) (ω : CoVector d) :
    Vector.basis.coordPairing CoVector.basis (v ⊗ₜ ω) = (v : Fin 1 ⊕ Fin d → ℝ) ⬝ᵥ ω := by
  simp [Module.Basis.coordPairing_tmul, Vector.basis_repr_apply, CoVector.basis_repr_apply,
    dotProduct]

/-- The pairing `v^μ ω_μ` of a vector and a covector is Lorentz invariant,
`(Λ v) ⬝ᵥ ((Λ⁻¹)ᵀ ω) = v ⬝ᵥ ω`. -/
lemma dotProduct_rep (d : ℕ) (Λ : LorentzGroup d) (v : Vector d) (ω : CoVector d) :
    (Vector.rep Λ v : Fin 1 ⊕ Fin d → ℝ) ⬝ᵥ CoVector.rep Λ ω = v ⬝ᵥ ω := by
  change (Λ.1 *ᵥ v) ⬝ᵥ ((Λ⁻¹).1ᵀ *ᵥ ω) = _
  rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, LorentzGroup.coe_inv,
    LorentzGroup.subtype_inv_mul, one_mulVec]

/-- The coordinate pairing of an index with its dual is Lorentz invariant. At a lower index it is
the pairing at the upper index with its factors swapped (`Species.invariant_of_up`). -/
lemma coordPairing_rep (d : ℕ) : ∀ (c : Color Kind) (Λ : LorentzGroup d) (x : IndexSpace d c)
    (y : IndexSpace d c.dual),
    (IndexSpace.basis d c).coordPairing (IndexSpace.basis d c.dual)
        (IndexSpace.rep d c Λ x ⊗ₜ IndexSpace.rep d c.dual Λ y) =
      (IndexSpace.basis d c).coordPairing (IndexSpace.basis d c.dual) (x ⊗ₜ y) :=
  Species.invariant_of_up (basisIdx := fun _ => Fin 1 ⊕ Fin d) _ _ fun _ Λ x y =>
    (coordPairing_vector_coVector d _ _).trans <|
      (dotProduct_rep d Λ x y).trans (coordPairing_vector_coVector d x y).symm

end realLorentz

open realLorentz in
/-- Real Lorentz tensors in `d + 1` dimensions, on `Vector d` and `CoVector d` with their
representations and bases. The labels `Fin 1 ⊕ Fin d` put time first. At a concrete color each
field is the `Vector` or `CoVector` one by `rfl`, as in `(realLorentz d).rep up = Vector.rep`. -/
noncomputable def realLorentz (d : ℕ) :
    Species ℝ (LorentzGroup d) Kind (fun _ => Fin 1 ⊕ Fin d) where
  V := IndexSpace d
  rep := IndexSpace.rep d
  basis := IndexSpace.basis d
  invariant := coordPairing_rep d

namespace realLorentz

/-- The color of an upper Lorentz index, `v^μ`. -/
abbrev up : Color Kind := ⟨.vec, .up⟩

/-- The color of a lower Lorentz index, `w_μ`. -/
abbrev down : Color Kind := ⟨.vec, .down⟩

/-- The real Lorentz tensors in `d + 1` dimensions with the colors listed, as `ℝT[d, up, down]` for
`T^μ_ν`. The colors are read in the namespace `realLorentz`. The notation is active under
`open scoped Tensors.realLorentz`. -/
scoped syntax (name := realLorentzSyntax) "ℝT[" term,+ "]" : term

macro_rules (kind := realLorentzSyntax)
  | `(ℝT[$d]) => `((Tensors.realLorentz $d).Tensor ![])
  | `(ℝT[$d, $cs,*]) => `((Tensors.realLorentz $d).Tensor (open Tensors.realLorentz in ![$cs,*]))

end realLorentz

/-!

## B. The Minkowski metric

-/

namespace realLorentz

/-- The Minkowski metric `∑ μ, η_μμ e_μ ⊗ e_μ` at the color `c`, with `η = diag(1, -1, …, -1)`:
`η^μν` at an upper color and `η_μν` at a lower one. -/
noncomputable def metric (d : ℕ) (c : Color Kind) : (realLorentz d).V c ⊗[ℝ] (realLorentz d).V c :=
  ∑ μ, minkowskiMatrix μ μ • ((realLorentz d).basis c μ ⊗ₜ (realLorentz d).basis c μ)

/-- The coordinates of `metric d c` in Mathlib's product basis are the Minkowski matrix. -/
lemma basis_tensorProduct_repr_metric (d : ℕ) (c : Color Kind) (μ ν : Fin 1 ⊕ Fin d) :
    (((realLorentz d).basis c).tensorProduct ((realLorentz d).basis c)).repr (metric d c) (μ, ν) =
      minkowskiMatrix μ ν := by
  rw [metric, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single μ
    (fun x _ hx => by simp [Module.Basis.tensorProduct_repr_tmul_apply, Finsupp.single_apply, hx])
    (by simp)]
  by_cases h : μ = ν
  · subst h
    simp [Module.Basis.tensorProduct_repr_tmul_apply]
  · simp [Module.Basis.tensorProduct_repr_tmul_apply, h]

/-- The metric is Lorentz invariant, `Λ η Λᵀ = η` at an upper color and `Λ⁻¹ᵀ η Λ⁻¹ = η` at a
lower one. -/
lemma metric_invariant (d : ℕ) (c : Color Kind) (Λ : LorentzGroup d) :
    TensorProduct.map ((realLorentz d).rep c Λ) ((realLorentz d).rep c Λ) (metric d c) =
      metric d c := by
  let e := ((realLorentz d).basis c).tensorProductToMatrix ((realLorentz d).basis c)
  have he : e (metric d c) = minkowskiMatrix := Matrix.ext (basis_tensorProduct_repr_metric d c)
  refine e.injective ((Module.Basis.tensorProductToMatrix_map _ _ _ _ _).trans ?_)
  rw [he]
  match c with
  | ⟨_, .up⟩ =>
    rw [show LinearMap.toMatrix ((realLorentz d).basis up) ((realLorentz d).basis up)
        ((realLorentz d).rep up Λ) = Λ.1 from Vector.rep_toMatrix d Λ,
      LorentzGroup.mul_minkowskiMatrix_mul_transpose]
  | ⟨_, .down⟩ =>
    rw [show LinearMap.toMatrix ((realLorentz d).basis down) ((realLorentz d).basis down)
        ((realLorentz d).rep down Λ) = Λ.1⁻¹ᵀ from CoVector.rep_toMatrix d Λ,
      Matrix.transpose_transpose, ← LorentzGroup.coe_inv,
      LorentzGroup.transpose_mul_minkowskiMatrix_mul_self]

/-- The metrics at a color and at its dual are inverse, `η^μν η_νρ = δ^μ_ρ`, since `η² = 1`. -/
lemma metric_inverse (d : ℕ) (c : Color Kind) :
    (realLorentz d).toLin (metric d c) ∘ₗ (realLorentz d).toLin (metric d c.dual) =
      LinearMap.id :=
  Species.toLin_comp_toLin_of_mul_eq_one _ _ <| by
    simp only [basis_tensorProduct_repr_metric]
    exact minkowskiMatrix.sq

end realLorentz

/-- The Minkowski metric `η`, `diag(1, -1, …, -1)` at both colors of every kind. The signature is
mostly minus. -/
noncomputable instance (d : ℕ) (κ : realLorentz.Kind) : (realLorentz d).HasForm κ where
  formAt v := realLorentz.metric d ⟨κ, v⟩
  formAt_invariant v := realLorentz.metric_invariant d ⟨κ, v⟩
  formAt_inverse v := realLorentz.metric_inverse d ⟨κ, v⟩

/-- The Minkowski metric is symmetric. -/
instance (d : ℕ) (κ : realLorentz.Kind) : (realLorentz d).IsSymmetricForm κ where
  comm_form v := by
    change TensorProduct.comm ℝ _ _ (realLorentz.metric d ⟨κ, v⟩) = realLorentz.metric d ⟨κ, v⟩
    simp [realLorentz.metric]

/-!

## C. Dual bases and components of the metric and the delta

-/

namespace realLorentz

/-- The components of the metric are the Minkowski matrix, `η_μν` at a lower color and `η^μν` at an
upper one. -/
lemma formMatrix_apply (d : ℕ) (c : Color Kind) (μ ν : Fin 1 ⊕ Fin d) :
    (realLorentz d).formMatrix c μ ν = minkowskiMatrix μ ν :=
  basis_tensorProduct_repr_metric d c μ ν

/-- The components of the metric are the Minkowski matrix `diag(1, -1, …, -1)`: at the labels
`![α, β]` they are `η^αβ` at an upper color and `η_αβ` at a lower one. The labels are any
`μ : Fin 2 → Fin 1 ⊕ Fin d`, as in `Species.tensorBasis_repr_twoSlotEquiv`. -/
lemma tensorBasis_repr_formTensor (d : ℕ) (c : Color Kind) (μ : Fin 2 → Fin 1 ⊕ Fin d) :
    ((realLorentz d).tensorBasis ![c, c]).repr ((realLorentz d).formTensor c) μ =
      minkowskiMatrix (μ 0) (μ 1) := by
  rw [Species.tensorBasis_repr_formTensor, formMatrix_apply]

/-- The components of the delta are those of the identity matrix, `δ^μ_ν = 1` for `μ = ν` and `0`
otherwise, at both colors. -/
lemma tensorBasis_repr_deltaTensor (d : ℕ) (c : Color Kind) (μ : Fin 2 → Fin 1 ⊕ Fin d) :
    ((realLorentz d).tensorBasis ![c.dual, c]).repr ((realLorentz d).deltaTensor c) μ =
      (1 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (μ 0) (μ 1) := by
  rw [Species.tensorBasis_repr_deltaTensor_eq_one]

/-- Lowering or raising a vector in components, `v_ν = η_νν v^ν`: the Minkowski metric is
diagonal. -/
lemma basis_repr_toDual (d : ℕ) (c : Color Kind) (v : (realLorentz d).V c)
    (ν : Fin 1 ⊕ Fin d) :
    ((realLorentz d).basis c.dual).repr ((realLorentz d).toDual c v) ν =
      minkowskiMatrix ν ν * ((realLorentz d).basis c).repr v ν := by
  simp [Species.basis_repr_toDual c v ν, formMatrix_apply,
    minkowskiMatrix.as_diagonal, Matrix.diagonal_apply, mul_comm]

/-- Lowering or raising the index at the slot `i` in components, `T^…_ν… = η_νν T^…ν…`: the
Minkowski metric is diagonal. -/
lemma tensorBasis_repr_toDualAt (d : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    {c c' : ι → Color Kind} (i : ι) (a : Color Kind) (ha : c i = a) (hi : c' i = a.dual)
    (h : ∀ x, x ≠ i → c x = c' x) (t : (realLorentz d).Tensor c) (φ : ι → Fin 1 ⊕ Fin d) :
    ((realLorentz d).tensorBasis c').repr ((realLorentz d).toDualAt i a ha hi h t) φ =
      minkowskiMatrix (φ i) (φ i) * ((realLorentz d).tensorBasis c).repr t φ := by
  subst ha
  simp [Species.tensorBasis_repr_toDualAt i _ rfl hi h, formMatrix_apply,
    minkowskiMatrix.as_diagonal, Matrix.diagonal_apply]

/-- `η^00 = 1` and `η^11 = -1` in `3 + 1` dimensions: the signature is mostly minus. -/
example : ((realLorentz 3).tensorBasis ![up, up]).repr ((realLorentz 3).formTensor up)
      ![.inl 0, .inl 0] = 1 ∧
    ((realLorentz 3).tensorBasis ![up, up]).repr ((realLorentz 3).formTensor up)
      ![.inr 0, .inr 0] = -1 := by
  simp [tensorBasis_repr_formTensor, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]

/-- `η_μν η^μν = d + 1`: contracting both indices of `η_μν` with those of `η^μν` gives the number
of dimensions. -/
example (d : ℕ) : ((realLorentz d).tensorBasis ![]).repr
    {(realLorentz d).formTensor down | μ ν ⊗ (realLorentz d).formTensor up | μ ν}ᵀ
    (fun i => i.elim0) = d + 1 := by
  rw [Species.Tensor.tensorBasis_repr_contr_two_pairs]
  simp only [Species.tensorBasis_repr_reindex, Species.tensorBasis_repr_tmulEquiv,
    tensorBasis_repr_formTensor]
  simp [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply, Fintype.sum_sum_type, add_comm]

/-- `ℝT[3, up, down]` is the space of tensors `T^μ_ν` in four dimensions. -/
example : ℝT[3, up, down] = (realLorentz 3).Tensor ![up, down] := rfl
end realLorentz

/-!

## D. Lorentz vectors and covectors as tensors

-/

namespace realLorentz

open Matrix

/-- A Lorentz vector `v^μ` is a tensor with one upper index, the space of the index. The Lorentz
group acts by `Vector.rep`, `Λ v = Λ *ᵥ v`. -/
noncomputable instance vectorTensorial (d : ℕ) : Tensorial (realLorentz d) ![up] (Vector d) :=
  Tensorial.ofIndexSpace (realLorentz d) up

/-- A Lorentz covector `ω_μ` is a tensor with one lower index, the space of the index. The Lorentz
group acts by `CoVector.rep`, `Λ ω = (Λ⁻¹)ᵀ *ᵥ ω`. -/
noncomputable instance coVectorTensorial (d : ℕ) :
    Tensorial (realLorentz d) ![down] (CoVector d) :=
  Tensorial.ofIndexSpace (realLorentz d) down

/-- The components of the tensor of a vector are its components, `v^μ`. -/
lemma tensorBasis_repr_toTensor_vector (d : ℕ) (v : Vector d) (μ : Fin 1 → Fin 1 ⊕ Fin d) :
    ((realLorentz d).tensorBasis ![up]).repr (Tensorial.toTensor v) μ = v (μ 0) :=
  Tensorial.tensorBasis_repr_toTensor_ofIndexSpace (S := realLorentz d) up v μ

/-- The vector of a tensor `T` with one upper index has the components of `T`, `v^ν = T^ν`. -/
lemma toTensor_symm_vector_apply (d : ℕ) (T : (realLorentz d).Tensor ![up])
    (ν : Fin 1 ⊕ Fin d) :
    (Tensorial.toTensor (M := Vector d)).symm T ν =
      ((realLorentz d).tensorBasis ![up]).repr T fun _ => ν := by
  conv_rhs => rw [← Representation.Equiv.apply_symm_apply (Tensorial.toTensor (M := Vector d)) T]
  rw [tensorBasis_repr_toTensor_vector]

/-- The components of the tensor of a covector are its components, `ω_μ`. -/
lemma tensorBasis_repr_toTensor_coVector (d : ℕ) (ω : CoVector d) (μ : Fin 1 → Fin 1 ⊕ Fin d) :
    ((realLorentz d).tensorBasis ![down]).repr (Tensorial.toTensor ω) μ = ω (μ 0) :=
  Tensorial.tensorBasis_repr_toTensor_ofIndexSpace (S := realLorentz d) down ω μ

/-- The tensor of the basis vector `e_μ` is the basis tensor with label `μ`. -/
lemma toTensor_basis_vector (d : ℕ) (μ : Fin 1 ⊕ Fin d) :
    Tensorial.toTensor (Vector.basis μ) = (realLorentz d).tensorBasis ![up] fun _ => μ :=
  Species.oneSlotEquiv_basis (S := realLorentz d) up fun _ => μ

/-- The tensor of the basis covector `e^μ` is the basis tensor with label `μ`. -/
lemma toTensor_basis_coVector (d : ℕ) (μ : Fin 1 ⊕ Fin d) :
    Tensorial.toTensor (CoVector.basis μ) = (realLorentz d).tensorBasis ![down] fun _ => μ :=
  Species.oneSlotEquiv_basis (S := realLorentz d) down fun _ => μ

/-- The components `F^μν` of the tensor of `F` in `Vector d ⊗ Vector d` are its coordinates in
Mathlib's product basis `Basis.tensorProduct`. -/
lemma tensorBasis_repr_toTensor_vector_tmul (d : ℕ) (F : Vector d ⊗[ℝ] Vector d)
    (μ : Fin 1 ⊕ Fin 1 → Fin 1 ⊕ Fin d) :
    ((realLorentz d).tensorBasis (prodColors ![up] ![up])).repr (Tensorial.toTensor F) μ =
      (Vector.basis.tensorProduct Vector.basis).repr F (μ (.inl 0), μ (.inr 0)) :=
  Tensorial.tensorBasis_repr_toTensor_prod_ofIndexSpace (S := realLorentz d) up up F μ

/-- The component `F^μν` of `F` in `Vector d ⊗ Vector d`, its coordinate at `(μ, ν)` in Mathlib's
product basis `e_μ ⊗ e_ν`. -/
noncomputable def _root_.Lorentz.Vector.tensorComponent {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    Vector d ⊗[ℝ] Vector d →ₗ[ℝ] ℝ :=
  Finsupp.lapply (μ, ν) ∘ₗ (Vector.basis.tensorProduct Vector.basis).repr.toLinearMap

lemma _root_.Lorentz.Vector.tensorComponent_apply {d : ℕ} (μ ν : Fin 1 ⊕ Fin d)
    (F : Vector d ⊗[ℝ] Vector d) :
    Vector.tensorComponent μ ν F = (Vector.basis.tensorProduct Vector.basis).repr F (μ, ν) := rfl

@[simp]
lemma _root_.Lorentz.Vector.tensorComponent_tmul {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) (v w : Vector d) :
    Vector.tensorComponent μ ν (v ⊗ₜ w) = v μ * w ν := by
  simp [Vector.tensorComponent_apply, Module.Basis.tensorProduct_repr_tmul_apply,
    Vector.basis_repr_apply, mul_comm]

/-- Two elements of `Vector d ⊗ Vector d` with the same components are equal. -/
lemma _root_.Lorentz.Vector.tensorComponent_ext {d : ℕ} {F G : Vector d ⊗[ℝ] Vector d}
    (h : ∀ μ ν, Vector.tensorComponent μ ν F = Vector.tensorComponent μ ν G) : F = G :=
  (Vector.basis.tensorProduct Vector.basis).repr.injective (Finsupp.ext fun μν => h μν.1 μν.2)

/-- An element of `Vector d ⊗ Vector d` is the sum `F^μν e_μ ⊗ e_ν` of its components. -/
lemma _root_.Lorentz.Vector.eq_sum_tensorComponent {d : ℕ} (F : Vector d ⊗[ℝ] Vector d) :
    F = ∑ μ, ∑ ν, Vector.tensorComponent μ ν F • Vector.basis μ ⊗ₜ[ℝ] Vector.basis ν := by
  simp only [Vector.tensorComponent_apply, ← Fintype.sum_prod_type']
  exact ((Vector.basis.tensorProduct Vector.basis).sum_repr _).symm.trans
    (Finset.sum_congr rfl fun _ _ => by rw [Module.Basis.tensorProduct_apply])

/-- The components `T_μ^ν` of the tensor of `T` in `CoVector d ⊗ Vector d` are its coordinates in
Mathlib's product basis `Basis.tensorProduct`. -/
lemma tensorBasis_repr_toTensor_coVector_tmul (d : ℕ) (T : CoVector d ⊗[ℝ] Vector d)
    (μ : Fin 1 ⊕ Fin 1 → Fin 1 ⊕ Fin d) :
    ((realLorentz d).tensorBasis (prodColors ![down] ![up])).repr (Tensorial.toTensor T) μ =
      (CoVector.basis.tensorProduct Vector.basis).repr T (μ (.inl 0), μ (.inr 0)) :=
  Tensorial.tensorBasis_repr_toTensor_prod_ofIndexSpace (S := realLorentz d) down up T μ

/-- The contraction `v^μ ω_μ` of a vector with a covector, a tensor with no slots whose one
component is `∑ μ, v^μ ω_μ`. -/
lemma tensorBasis_repr_contr_vector_coVector (d : ℕ) (v : Vector d) (ω : CoVector d) :
    ((realLorentz d).tensorBasis ![]).repr {v | μ ⊗ ω | μ}ᵀ (fun i => i.elim0) =
      ∑ μ, v μ * ω μ := by
  simp [Species.Tensor.tensorBasis_repr_contr_one_pair, Species.tensorBasis_repr_reindex,
    Species.tensorBasis_repr_tmulEquiv, tensorBasis_repr_toTensor_vector,
    tensorBasis_repr_toTensor_coVector]

open scoped Lorentz.Vector in
/-- The Minkowski product is the contraction `η_μν v^μ w^ν`, a tensor with no slots whose one
component is `⟪v, w⟫ₘ`. -/
lemma tensorBasis_repr_formTensor_contr_vector (d : ℕ) (v w : Vector d) :
    ((realLorentz d).tensorBasis ![]).repr
      {(realLorentz d).formTensor down | μ ν ⊗ v | μ ⊗ w | ν}ᵀ (fun i => i.elim0) = ⟪v, w⟫ₘ := by
  tensor_components [tensorBasis_repr_formTensor, tensorBasis_repr_toTensor_vector]
  rw [Vector.minkowskiProduct_toCoord_minkowskiMatrix]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_eq_single μ (fun ν _ h => by simp [minkowskiMatrix.off_diag_zero (Ne.symm h)])
    (by simp)]

/-- The contraction `F_μν G^μν` of `F` and `G` in `Vector d ⊗ Vector d`, with both indices of `F`
lowered, is `∑ η_μμ η_νν F^μν G^μν` in components. -/
lemma tensorBasis_repr_toDualAt_contr_vector_tmul (d : ℕ) (F G : Vector d ⊗[ℝ] Vector d) :
    ((realLorentz d).tensorBasis ![]).repr {F | ↓μ ↓ν ⊗ G | μ ν}ᵀ (fun i => i.elim0) =
      ∑ μ, ∑ ν, minkowskiMatrix μ μ * minkowskiMatrix ν ν * Vector.tensorComponent μ ν F *
        Vector.tensorComponent μ ν G := by
  tensor_components [tensorBasis_repr_toDualAt, tensorBasis_repr_toTensor_vector_tmul,
    ← Vector.tensorComponent_apply]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

/-- The pairing `v^μ ω_μ` of a vector with a covector is Lorentz invariant. -/
lemma contr_vector_coVector_rep (d : ℕ) (Λ : LorentzGroup d) (v : Vector d) (ω : CoVector d) :
    {Tensorial.rep Λ v | μ ⊗ Tensorial.rep Λ ω | μ}ᵀ = {v | μ ⊗ ω | μ}ᵀ := by
  rw [Tensorial.toTensor_rep, Tensorial.toTensor_rep, Species.tmulEquiv_smul,
    Species.intertwiningMap_smul, Species.smul_eq_self_of_isEmpty]

end realLorentz

end Tensors
