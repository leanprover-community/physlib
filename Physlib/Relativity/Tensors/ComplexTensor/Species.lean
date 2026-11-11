/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Schouten
public import Physlib.Mathematics.Tensors.Conjugation
public import Physlib.Relativity.Fermions.Weyl.Metric
public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Pre
/-!

# The species of complex Lorentz tensors

Weyl spinors and complex Lorentz vectors as one conjugate species of `SL(2, ℂ)`, with the invariant
forms `ε` and `η`.

## i. Overview

Complex Lorentz tensors have three kinds of index, the left-handed kind `left`, as in `ψ_α`, and
the right-handed kind `right`, as in `ψ̄_α̇`, with basis labels `Fin 2`, and the vector kind `vec`,
with labels `Fin 1 ⊕ Fin 3`. Conjugation `star` swaps `left` and `right` and fixes `vec`. With
the two variances this gives six colors, `upL`, `downL`, `upR`, `downR`, `up` and `down`. Under
`open scoped Tensor.complexLorentz`, `ℂT[upL, downR]` is the space of the tensors `T^α_β̇`.

The species is built on `Fermion.LeftHandedWeyl`, `Fermion.RightHandedWeyl`, their duals,
`Lorentz.ComplexVector` and `Lorentz.ComplexCoVector`, with their representations and bases. An
index contracts with its dual by the coordinate pairing, which is `SL(2, ℂ)`-invariant.
Conjugation conjugates the components, and a label of a kind is the same label of its
conjugate (`idxBar`), a conjugation of the species (`HasConjugation.ofBasis`). The
right-handed representation is the conjugate of the left-handed one, `M ↦ M̄`, and the vector
representation is real, so this conjugation commutes with `SL(2, ℂ)`
(`IsEquivariantConjugation`).

The invariant form is `ε` at the Weyl colors and `η` at the vector colors. The form `ε` is
antisymmetric and `η` symmetric (`IsAntisymmetricForm`, `IsSymmetricForm`). The form
`ε^αβ` has the matrix `!![0, 1; -1, 0]` and `ε_αβ` the matrix `!![0, -1; 1, 0]`, so `ε^12 = 1` and
`ε_12 = -1`. Lowering contracts the second index of the form, `ψ_α = ε_αβ ψ^β`, as in Wess and
Bagger. The
forms are written `εL`, `εL'`, `εR`, `εR'`, `η` and `η'`, and the deltas `δL`, `δL'`, `δR`, `δR'`,
`δ` and `δ'`. Their components are stated through `tensorBasis`, and the antisymmetry
of `ε` and the symmetry of `η` are stated in index notation.

These spaces are tensors with one slot (`Tensorial`), so a spinor `ψ : LeftHandedWeyl`
enters index notation directly, as in `{ψ | α ⊗ φ | α}ᵀ` for `ψ^α φ_α`.

## ii. Key results

- `complexLorentz` : the species of complex Lorentz tensors.
- the instances `complexLorentz.HasForm κ` : the forms `ε` and `η`, with `IsAntisymmetricForm`
  at the Weyl kinds and `IsSymmetricForm` at the vector kind.
- the instances `complexLorentz.HasConjugation` and `complexLorentz.IsEquivariantConjugation` :
  conjugation swaps left- and right-handed indices and commutes with `SL(2, ℂ)`,
  and `complexLorentz.tensorBasis_repr_conj` : the components of a conjugate tensor are the
  conjugates of the components.
- `complexLorentz.formMatrix_apply` : the components `Species.formMatrix` of the form at any color
  are `complexLorentz.formEntries`, for lowering in components.
- `complexLorentz.tensorBasis_repr_formTensor` : the components of `ε` and `η` at any color, and
  `complexLorentz.tensorBasis_repr_deltaTensor` those of `δ`.
- `complexLorentz.formTensor_upL_antisymm`, `complexLorentz.formTensor_up_symm` : `ε` is
  antisymmetric and `η` symmetric, and `complexLorentz.deltaTensor_swap` : `δ^μ_ν = δ_ν^μ`.
- `complexLorentz.schouten_downL` and `complexLorentz.schouten_downR` : the Schouten identity of
  `ε` in index notation, from `Species.schouten_formTensor_deltaTensor` and
  `Species.schouten_formTensor_deltaTensor_dual`.
- `complexLorentz.leftHandedWeylTensorial` and the other instances of section F : Weyl spinors and
  complex vectors as tensors with one slot.
- `complexLorentz.tensorBasis_repr_toTensor_leftRight` : the components of a tensor in
  `LeftHandedWeyl ⊗ RightHandedWeyl` are the entries of `leftRightToMatrix`.

## iii. Table of contents

- A. The species
- B. The invariant forms
- C. Conjugation
- D. Components of the forms and the deltas
- E. Symmetry of the forms
- F. Weyl spinors and complex vectors as tensors
- G. Examples

## iv. References

- J. Wess and J. Bagger, Supersymmetry and Supergravity, Appendix A.

-/

@[expose] public section

open TensorProduct Fermion Lorentz MatrixGroups

namespace Tensor

/-!

## A. The species

-/

namespace complexLorentz

/-- The kinds of complex Lorentz index. -/
inductive Kind
  /-- The left-handed kind, as the index of `ψ_α`. -/
  | left
  /-- The right-handed kind, as the index of `ψ̄_α̇`. -/
  | right
  /-- The vector kind, its own conjugate. -/
  | vec
deriving DecidableEq

export Kind (left right vec)

/-- Conjugation swaps the left- and right-handed kinds and fixes the vector kind. -/
instance : InvolutiveStar Kind where
  star
    | left => right
    | right => left
    | vec => vec
  star_involutive κ := by cases κ <;> rfl

/-- The basis labels of a kind, `Fin 2` for Weyl spinors and `Fin 1 ⊕ Fin 3` for vectors. -/
abbrev Idx : Kind → Type
  | left | right => Fin 2
  | vec => Fin 1 ⊕ Fin 3

instance : ∀ κ, Fintype (Idx κ)
  | left | right => inferInstanceAs (Fintype (Fin 2))
  | vec => inferInstanceAs (Fintype (Fin 1 ⊕ Fin 3))

instance : ∀ κ, DecidableEq (Idx κ)
  | left | right => inferInstanceAs (DecidableEq (Fin 2))
  | vec => inferInstanceAs (DecidableEq (Fin 1 ⊕ Fin 3))

/-- The vector space of a complex Lorentz index of color `c`. A `def` with its own instances, as
`realLorentz.IndexSpace`. -/
def IndexSpace : Color Kind → Type
  | ⟨left, .up⟩ => LeftHandedWeyl
  | ⟨left, .down⟩ => DualLeftHandedWeyl
  | ⟨right, .up⟩ => RightHandedWeyl
  | ⟨right, .down⟩ => DualRightHandedWeyl
  | ⟨vec, .up⟩ => ComplexVector
  | ⟨vec, .down⟩ => ComplexCoVector

noncomputable instance : ∀ c, AddCommGroup (IndexSpace c)
  | ⟨left, .up⟩ => inferInstanceAs (AddCommGroup LeftHandedWeyl)
  | ⟨left, .down⟩ => inferInstanceAs (AddCommGroup DualLeftHandedWeyl)
  | ⟨right, .up⟩ => inferInstanceAs (AddCommGroup RightHandedWeyl)
  | ⟨right, .down⟩ => inferInstanceAs (AddCommGroup DualRightHandedWeyl)
  | ⟨vec, .up⟩ => inferInstanceAs (AddCommGroup ComplexVector)
  | ⟨vec, .down⟩ => inferInstanceAs (AddCommGroup ComplexCoVector)

noncomputable instance : ∀ c, Module ℂ (IndexSpace c)
  | ⟨left, .up⟩ => inferInstanceAs (Module ℂ LeftHandedWeyl)
  | ⟨left, .down⟩ => inferInstanceAs (Module ℂ DualLeftHandedWeyl)
  | ⟨right, .up⟩ => inferInstanceAs (Module ℂ RightHandedWeyl)
  | ⟨right, .down⟩ => inferInstanceAs (Module ℂ DualRightHandedWeyl)
  | ⟨vec, .up⟩ => inferInstanceAs (Module ℂ ComplexVector)
  | ⟨vec, .down⟩ => inferInstanceAs (Module ℂ ComplexCoVector)

/-- The representation of `SL(2, ℂ)` on the vector space of a color. -/
noncomputable def indexRep : (c : Color Kind) → Representation ℂ SL(2, ℂ) (IndexSpace c)
  | ⟨left, .up⟩ => LeftHandedWeyl.rep
  | ⟨left, .down⟩ => DualLeftHandedWeyl.rep
  | ⟨right, .up⟩ => RightHandedWeyl.rep
  | ⟨right, .down⟩ => DualRightHandedWeyl.rep
  | ⟨vec, .up⟩ => ComplexVector.SL2CRep
  | ⟨vec, .down⟩ => ComplexCoVector.SL2CRep

/-- The basis of the vector space of a color. -/
noncomputable def indexBasis :
    (c : Color Kind) → Module.Basis (Idx c.kind) ℂ (IndexSpace c)
  | ⟨left, .up⟩ => LeftHandedWeyl.basis
  | ⟨left, .down⟩ => DualLeftHandedWeyl.basis
  | ⟨right, .up⟩ => RightHandedWeyl.basis
  | ⟨right, .down⟩ => DualRightHandedWeyl.basis
  | ⟨vec, .up⟩ => ComplexVector.basis
  | ⟨vec, .down⟩ => ComplexCoVector.basis

/-- The coordinate pairing of a color and its dual is invariant under `SL(2, ℂ)`. At a lower color
it is the pairing at the upper color with its factors swapped (`Species.invariant_of_up`). -/
lemma coordPairing_rep : ∀ (c : Color Kind) (g : SL(2, ℂ)) (x : IndexSpace c)
    (y : IndexSpace c.dual),
    (indexBasis c).coordPairing (indexBasis c.dual) (indexRep c g x ⊗ₜ indexRep c.dual g y) =
      (indexBasis c).coordPairing (indexBasis c.dual) (x ⊗ₜ y) :=
  Species.invariant_of_up indexRep indexBasis fun
    | left => Species.invariant_of_contr LeftHandedWeyl.contr fun μ ν =>
      (LeftHandedWeyl.contr_basis μ ν).trans (if_congr Fin.ext_iff.symm rfl rfl)
    | right => Species.invariant_of_contr RightHandedWeyl.contr fun μ ν =>
      (RightHandedWeyl.contr_basis μ ν).trans (if_congr Fin.ext_iff.symm rfl rfl)
    | vec => fun g x y => (coordPairing_complexVector_coVector _ _).trans <|
      (dotProduct_SL2CRep g x y).trans (coordPairing_complexVector_coVector x y).symm

end complexLorentz

open complexLorentz in
/-- Complex Lorentz tensors: Weyl spinors and complex Lorentz vectors with the action of
`SL(2, ℂ)`, on the spaces, representations and bases of `Fermion` and `Lorentz`. -/
noncomputable def complexLorentz : Species ℂ SL(2, ℂ) Kind Idx where
  V := IndexSpace
  rep := indexRep
  basis := indexBasis
  invariant := coordPairing_rep

namespace complexLorentz

/-- An upper left-handed index, `ψ^α`. -/
abbrev upL : Color Kind := ⟨left, .up⟩

/-- A lower left-handed index, `ψ_α`. -/
abbrev downL : Color Kind := ⟨left, .down⟩

/-- An upper right-handed index, `ψ̄^α̇`. -/
abbrev upR : Color Kind := ⟨right, .up⟩

/-- A lower right-handed index, `ψ̄_α̇`. -/
abbrev downR : Color Kind := ⟨right, .down⟩

/-- An upper vector index, `v^μ`. -/
abbrev up : Color Kind := ⟨vec, .up⟩

/-- A lower vector index, `w_μ`. -/
abbrev down : Color Kind := ⟨vec, .down⟩

/-- Conjugation swaps `upL` and `upR` and fixes `up`. -/
example : upL.bar = upR ∧ downR.bar = downL ∧ up.bar = up := ⟨rfl, rfl, rfl⟩

/-- The complex Lorentz tensors with the colors listed, as `ℂT[upL, downR]` for `T^α_β̇`. The colors
are read in the namespace `complexLorentz`. The notation is active under
`open scoped Tensor.complexLorentz`. -/
scoped syntax (name := complexLorentzSyntax) "ℂT[" term,* "]" : term

macro_rules (kind := complexLorentzSyntax)
  | `(ℂT[$cs,*]) => `(Tensor.complexLorentz.Tensor (open Tensor.complexLorentz in ![$cs,*]))

/-- `ℂT[upL, downR]` is the space of tensors `T^α_β̇`. -/
example : ℂT[upL, downR] = complexLorentz.Tensor ![upL, downR] := rfl

end complexLorentz

/-!

## B. The invariant forms

-/

namespace complexLorentz

/-- The invariant form at a color: `ε` at the Weyl colors and `η` at the vector colors. At the Weyl
colors it is the negative of the metric of the Weyl representation, so that `ε^12 = 1`. -/
noncomputable def form : (c : Color Kind) → complexLorentz.V c ⊗[ℂ] complexLorentz.V c
  | ⟨left, .up⟩ => -LeftHandedWeyl.metricVal
  | ⟨left, .down⟩ => -DualLeftHandedWeyl.metricVal
  | ⟨right, .up⟩ => -RightHandedWeyl.metricVal
  | ⟨right, .down⟩ => -DualRightHandedWeyl.metricVal
  | ⟨vec, .up⟩ => ComplexVector.metricVal
  | ⟨vec, .down⟩ => ComplexCoVector.metricVal

/-- The forms are invariant under `SL(2, ℂ)`, each the value at `1` of an intertwining map from
the trivial representation. -/
lemma form_invariant : ∀ (c : Color Kind) (g : SL(2, ℂ)),
    TensorProduct.map (complexLorentz.rep c g) (complexLorentz.rep c g) (form c) = form c
  | ⟨left, .up⟩ => fun g => (map_neg _ _).trans <| congrArg Neg.neg <|
    LeftHandedWeyl.metric.map_one_invariant LeftHandedWeyl.metric_apply_one g
  | ⟨left, .down⟩ => fun g => (map_neg _ _).trans <| congrArg Neg.neg <|
    DualLeftHandedWeyl.metric.map_one_invariant DualLeftHandedWeyl.metric_apply_one g
  | ⟨right, .up⟩ => fun g => (map_neg _ _).trans <| congrArg Neg.neg <|
    RightHandedWeyl.metric.map_one_invariant RightHandedWeyl.metric_apply_one g
  | ⟨right, .down⟩ => fun g => (map_neg _ _).trans <| congrArg Neg.neg <|
    DualRightHandedWeyl.metric.map_one_invariant DualRightHandedWeyl.metric_apply_one g
  | ⟨vec, .up⟩ => ComplexVector.metric.map_one_invariant ComplexVector.metric_apply_one
  | ⟨vec, .down⟩ => ComplexCoVector.metric.map_one_invariant ComplexCoVector.metric_apply_one

/-- The entries of the form at each color, `ε^αβ = !![0, 1; -1, 0]` at the upper Weyl colors,
`ε_αβ = !![0, -1; 1, 0]` at the lower ones, and `η` at the vector colors. -/
noncomputable def formEntries : (c : Color Kind) → Idx c.kind → Idx c.kind → ℂ
  | ⟨left, .up⟩ => metricRaw
  | ⟨left, .down⟩ => -metricRaw
  | ⟨right, .up⟩ => metricRaw
  | ⟨right, .down⟩ => -metricRaw
  | ⟨vec, _⟩ => fun μ ν => minkowskiMatrix μ ν

/-- The coordinates of the form in Mathlib's product basis are `formEntries`: each form is defined
by its matrix. -/
lemma basis_tensorProduct_repr_form : ∀ (c : Color Kind) (μ ν : Idx c.kind),
    ((complexLorentz.basis c).tensorProduct (complexLorentz.basis c)).repr (form c) (μ, ν) =
      formEntries c μ ν
  | ⟨left, .up⟩, μ, ν => (DFunLike.congr_fun (map_neg _ (LeftHandedWeyl.metricVal :
      complexLorentz.V ⟨left, .up⟩ ⊗[ℂ] complexLorentz.V ⟨left, .up⟩)) (μ, ν)).trans <|
    neg_eq_iff_eq_neg.mpr
      (congrFun (congrFun (leftLeftToMatrix.apply_symm_apply (-metricRaw)) μ) ν)
  | ⟨left, .down⟩, μ, ν => (DFunLike.congr_fun (map_neg _ (DualLeftHandedWeyl.metricVal :
      complexLorentz.V ⟨left, .down⟩ ⊗[ℂ] complexLorentz.V ⟨left, .down⟩)) (μ, ν)).trans <|
    neg_eq_iff_eq_neg.mpr
      ((congrFun (congrFun (dualLeftdualLeftToMatrix.apply_symm_apply metricRaw) μ) ν).trans
        (neg_neg _).symm)
  | ⟨right, .up⟩, μ, ν => (DFunLike.congr_fun (map_neg _ (RightHandedWeyl.metricVal :
      complexLorentz.V ⟨right, .up⟩ ⊗[ℂ] complexLorentz.V ⟨right, .up⟩)) (μ, ν)).trans <|
    neg_eq_iff_eq_neg.mpr
      (congrFun (congrFun (rightRightToMatrix.apply_symm_apply (-metricRaw)) μ) ν)
  | ⟨right, .down⟩, μ, ν => (DFunLike.congr_fun (map_neg _ (DualRightHandedWeyl.metricVal :
      complexLorentz.V ⟨right, .down⟩ ⊗[ℂ] complexLorentz.V ⟨right, .down⟩)) (μ, ν)).trans <|
    neg_eq_iff_eq_neg.mpr
      ((congrFun (congrFun (dualRightDualRightToMatrix.apply_symm_apply metricRaw) μ) ν).trans
        (neg_neg _).symm)
  | ⟨vec, .up⟩, μ, ν => congrFun (congrFun (contrContrToMatrix.apply_symm_apply
      ((@minkowskiMatrix 3).map Complex.ofRealHom)) μ) ν
  | ⟨vec, .down⟩, μ, ν => congrFun (congrFun (coCoToMatrix.apply_symm_apply
      ((@minkowskiMatrix 3).map Complex.ofRealHom)) μ) ν

/-- The matrices of the forms at `c.dual` and at `c` are inverse, `(-ε) ε = 1` and `η η = 1`. -/
lemma formEntries_dual_mul : ∀ c : Color Kind,
    Matrix.of (formEntries c.dual) * Matrix.of (formEntries c) = 1
  | ⟨left, .up⟩ | ⟨right, .up⟩ => show -metricRaw * metricRaw = 1 by
    simpa [metricRaw] using Matrix.one_fin_two.symm
  | ⟨left, .down⟩ | ⟨right, .down⟩ => show metricRaw * -metricRaw = 1 by
    simpa [metricRaw] using Matrix.one_fin_two.symm
  | ⟨vec, _⟩ => show (@minkowskiMatrix 3).map Complex.ofRealHom *
      (@minkowskiMatrix 3).map Complex.ofRealHom = 1 by
    rw [← Matrix.map_mul, minkowskiMatrix.sq, Matrix.map_one _ (map_zero _) (map_one _)]

/-- The forms at `c` and at `c.dual` are inverse to each other, since their matrices are. -/
lemma form_inverse (c : Color Kind) :
    complexLorentz.toLin (form c) ∘ₗ complexLorentz.toLin (form c.dual) = LinearMap.id :=
  Module.Basis.coordTensorHomEquiv_comp_of_mul_eq_one _ _ _ _ <| by
    simpa only [basis_tensorProduct_repr_form] using formEntries_dual_mul c

end complexLorentz

/-- The invariant forms, `ε` at the Weyl kinds and `η` at the vector kind. -/
noncomputable instance (κ : complexLorentz.Kind) : complexLorentz.HasForm κ where
  formAt v := complexLorentz.form ⟨κ, v⟩
  formAt_invariant v := complexLorentz.form_invariant ⟨κ, v⟩
  formAt_inverse v := complexLorentz.form_inverse ⟨κ, v⟩

namespace complexLorentz

/-- The form `ε^αβ` on two upper left-handed indices. -/
scoped notation "εL" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.upL

/-- The form `ε_αβ` on two lower left-handed indices. -/
scoped notation "εL'" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.downL

/-- The form `ε^α̇β̇` on two upper right-handed indices. -/
scoped notation "εR" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.upR

/-- The form `ε_α̇β̇` on two lower right-handed indices. -/
scoped notation "εR'" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.downR

/-- The metric `η^μν` on two upper vector indices. -/
scoped notation "η" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.up

/-- The metric `η_μν` on two lower vector indices. -/
scoped notation "η'" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.down

/-- The delta `δ^μ_ν`, on the colors `![up, down]`. -/
scoped notation "δ" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.down

/-- The delta `δ_μ^ν`, on the colors `![down, up]`. -/
scoped notation "δ'" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.up

/-- The delta `δ^α_β`, on the colors `![upL, downL]`. -/
scoped notation "δL" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.downL

/-- The delta `δ_α^β`, on the colors `![downL, upL]`. -/
scoped notation "δL'" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.upL

/-- The delta `δ^α̇_β̇`, on the colors `![upR, downR]`. -/
scoped notation "δR" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.downR

/-- The delta `δ_α̇^β̇`, on the colors `![downR, upR]`. -/
scoped notation "δR'" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.upR

end complexLorentz

/-!

## C. Conjugation

-/

namespace complexLorentz

/-- A label of a kind read as a label of its conjugate `κ'`, the same element of `Fin 2` or of
`Fin 1 ⊕ Fin 3`. -/
def idxBar {κ κ' : Kind} (h : κ' = star κ) : Idx κ ≃ Idx κ' :=
  match κ, κ', h with
  | left, _, rfl | right, _, rfl | vec, _, rfl => Equiv.refl _

/-- Reading a label as a label of the conjugate kind and back gives the label. -/
lemma idxBar_idxBar {κ κ' : Kind} (h : κ' = star κ) (h' : κ = star κ') (μ : Idx κ) :
    idxBar h' (idxBar h μ) = μ := by
  subst h
  cases κ <;> rfl

/-- Conjugation swaps left- and right-handed indices and fixes vector indices, conjugating the
components. -/
noncomputable instance : complexLorentz.HasConjugation :=
  .ofBasis complexLorentz ⟨idxBar, idxBar_idxBar⟩

/-- Conjugation commutes with the action of `SL(2, ℂ)`. The right-handed representation is the
conjugate of the left-handed one, and the vector representation is real. -/
instance : complexLorentz.IsEquivariantConjugation :=
  Species.HasConjugation.isEquivariantConjugation_ofBasis ⟨idxBar, idxBar_idxBar⟩ fun κ g => by
    match κ with
    | left =>
      exact fun μ ν => (RightHandedWeyl.rep_apply_basis_repr g μ ν).trans
        (congrArg star (LeftHandedWeyl.rep_apply_basis_repr g μ ν).symm)
    | right =>
      exact fun μ ν => (LeftHandedWeyl.rep_apply_basis_repr g μ ν).trans <| (star_star _).symm.trans
        (congrArg star (RightHandedWeyl.rep_apply_basis_repr g μ ν).symm)
    | vec =>
      intro μ ν
      change ComplexVector.basis.repr (ComplexVector.SL2CRep g (ComplexVector.basis μ)) ν =
        star (ComplexVector.basis.repr (ComplexVector.SL2CRep g (ComplexVector.basis μ)) ν)
      rw [← LinearMap.toMatrix_apply, ComplexVector.basis_ρ_apply,
        LorentzGroup.star_toComplex_apply]

/-- The components of the conjugate of a tensor are the conjugates of its components, at the same
labels read through `idxBar`. -/
lemma tensorBasis_repr_conj {ι : Type} [Fintype ι] {c c' : ι → Color Kind}
    (h : ∀ i, c' i = (c i).bar) (t : complexLorentz.Tensor c) (μ : Π i, Idx (c' i).kind) :
    (complexLorentz.tensorBasis c').repr (Species.Tensor.conj h t) μ =
      star ((complexLorentz.tensorBasis c).repr t
        fun i => (idxBar (congrArg Color.kind (h i))).symm (μ i)) :=
  Species.Tensor.tensorBasis_repr_conj_of_basis h _
    (fun i => Species.HasConjugation.ofBasis_conjEquiv_basis _ (h i)) t μ

end complexLorentz

/-!

## D. Components of the forms and the deltas

-/

namespace complexLorentz

/-- The components of the form at any color are `formEntries`. -/
lemma formMatrix_apply (c : Color Kind) (μ ν : Idx c.kind) :
    Species.formMatrix complexLorentz c μ ν = formEntries c μ ν :=
  basis_tensorProduct_repr_form c μ ν

/-- The components of the form tensor at any color are `formEntries`, at the pair of labels
`(μ 0, μ 1)`. The labels `μ` form a dependent family, since the basis labels of a slot depend on
its color. -/
lemma tensorBasis_repr_formTensor (c : Color Kind) (μ : Π i, Idx (![c, c] i).kind) :
    (complexLorentz.tensorBasis ![c, c]).repr (complexLorentz.formTensor c) μ =
      formEntries c (μ 0) (μ 1) :=
  (Species.tensorBasis_repr_formTensor c μ).trans (formMatrix_apply c _ _)

/-- The components of `ε^αβ` are the matrix `!![0, 1; -1, 0]`. -/
lemma tensorBasis_repr_formTensor_upL (μ : Π i, Idx (![upL, upL] i).kind) :
    (complexLorentz.tensorBasis ![upL, upL]).repr εL μ = metricRaw (μ 0) (μ 1) :=
  tensorBasis_repr_formTensor upL μ

/-- The components of `ε_αβ` are the matrix `!![0, -1; 1, 0]`. -/
lemma tensorBasis_repr_formTensor_downL (μ : Π i, Idx (![downL, downL] i).kind) :
    (complexLorentz.tensorBasis ![downL, downL]).repr εL' μ = (-metricRaw) (μ 0) (μ 1) :=
  tensorBasis_repr_formTensor downL μ

/-- The components of `ε^α̇β̇` are the matrix `!![0, 1; -1, 0]`. -/
lemma tensorBasis_repr_formTensor_upR (μ : Π i, Idx (![upR, upR] i).kind) :
    (complexLorentz.tensorBasis ![upR, upR]).repr εR μ = metricRaw (μ 0) (μ 1) :=
  tensorBasis_repr_formTensor upR μ

/-- The components of `ε_α̇β̇` are the matrix `!![0, -1; 1, 0]`. -/
lemma tensorBasis_repr_formTensor_downR (μ : Π i, Idx (![downR, downR] i).kind) :
    (complexLorentz.tensorBasis ![downR, downR]).repr εR' μ = (-metricRaw) (μ 0) (μ 1) :=
  tensorBasis_repr_formTensor downR μ

/-- The components of `η^μν` and `η_μν` are the Minkowski matrix `diag(1, -1, -1, -1)`. -/
lemma tensorBasis_repr_formTensor_vec (v : Variance)
    (μ : Π i, Idx (![⟨vec, v⟩, ⟨vec, v⟩] i : Color Kind).kind) :
    (complexLorentz.tensorBasis ![⟨vec, v⟩, ⟨vec, v⟩]).repr (complexLorentz.formTensor ⟨vec, v⟩)
      μ = minkowskiMatrix (μ 0) (μ 1) :=
  tensorBasis_repr_formTensor ⟨vec, v⟩ μ

/-- The components of the delta are those of the identity matrix, `δ^μ_ν = 1` for `μ = ν` and `0`
otherwise, at every color. -/
lemma tensorBasis_repr_deltaTensor (c : Color Kind)
    (μ : Π i, Idx (![c.dual, c] i).kind) :
    (complexLorentz.tensorBasis ![c.dual, c]).repr (complexLorentz.deltaTensor c) μ =
      (1 : Matrix (Idx c.kind) (Idx c.kind) ℂ) (μ 0) (μ 1) := by
  rw [Species.tensorBasis_repr_deltaTensor_eq_one]

/-- `η^00 = 1` and `η^11 = -1`: the signature is mostly minus. -/
example : (complexLorentz.tensorBasis ![up, up]).repr η
      (Fin.cons (Sum.inl 0 : Fin 1 ⊕ Fin 3) (Fin.cons (Sum.inl 0 : Fin 1 ⊕ Fin 3) (·.elim0))) =
        1 ∧
    (complexLorentz.tensorBasis ![up, up]).repr η
      (Fin.cons (Sum.inr 0 : Fin 1 ⊕ Fin 3) (Fin.cons (Sum.inr 0 : Fin 1 ⊕ Fin 3) (·.elim0))) =
        -1 := by
  rw [tensorBasis_repr_formTensor_vec .up, tensorBasis_repr_formTensor_vec .up]
  change ((minkowskiMatrix (Sum.inl 0) (Sum.inl 0) : ℝ) : ℂ) = 1 ∧
    ((minkowskiMatrix (Sum.inr 0) (Sum.inr 0) : ℝ) : ℂ) = -1
  simp

end complexLorentz

/-!

## E. Symmetry of the forms

-/

namespace complexLorentz

/-- The Minkowski metric `η` on the vector kind is symmetric, `η^νμ = η^μν`. -/
instance : complexLorentz.IsSymmetricForm vec where
  comm_form v := (Species.comm_form_eq_smul _ 1 fun μ ν => by
    rw [formMatrix_apply, formMatrix_apply, one_mul]
    exact congrArg Complex.ofReal (congrFun (congrFun minkowskiMatrix.eq_transpose μ) ν)).trans
    (one_smul _ _)

/-- The entries of `ε` are antisymmetric, `ε^βα = -ε^αβ`. -/
lemma formEntries_antisymm : ∀ c : Color Kind, c.kind ≠ vec → ∀ μ ν,
    formEntries c ν μ = -1 * formEntries c μ ν
  | ⟨left, .up⟩, _ | ⟨left, .down⟩, _ | ⟨right, .up⟩, _ | ⟨right, .down⟩, _ => fun μ ν => by
    fin_cases μ <;> fin_cases ν <;> simp [formEntries, metricRaw]
  | ⟨vec, _⟩, h => absurd rfl h

/-- The form `ε` is antisymmetric at the Weyl colors. -/
lemma comm_form_weyl (c : Color Kind) (h : c.kind ≠ vec) :
    TensorProduct.comm ℂ _ _ (Species.form (S := complexLorentz) c) = -Species.form c :=
  (Species.comm_form_eq_smul c (-1) fun μ ν => by
    rw [formMatrix_apply, formMatrix_apply]
    exact formEntries_antisymm c h μ ν).trans (neg_one_smul _ _)

/-- The form `ε` on the left-handed Weyl kind is antisymmetric. -/
instance : complexLorentz.IsAntisymmetricForm left where
  comm_form v := comm_form_weyl ⟨left, v⟩ nofun

/-- The form `ε` on the right-handed Weyl kind is antisymmetric. -/
instance : complexLorentz.IsAntisymmetricForm right where
  comm_form v := comm_form_weyl ⟨right, v⟩ nofun

/-- `ε^αβ` is antisymmetric, `ε^αβ = -ε^βα`. -/
lemma formTensor_upL_antisymm : {εL | α β = -εL | β α}ᵀ := by
  tensor_regroup

/-- `ε_αβ` is antisymmetric, `ε_αβ = -ε_βα`. -/
lemma formTensor_downL_antisymm : {εL' | α β = -εL' | β α}ᵀ := by
  tensor_regroup

/-- `ε^α̇β̇` is antisymmetric, `ε^α̇β̇ = -ε^β̇α̇`. -/
lemma formTensor_upR_antisymm : {εR | α β = -εR | β α}ᵀ := by
  tensor_regroup

/-- `ε_α̇β̇` is antisymmetric, `ε_α̇β̇ = -ε_β̇α̇`. -/
lemma formTensor_downR_antisymm : {εR' | α β = -εR' | β α}ᵀ := by
  tensor_regroup

/-- `η^μν` is symmetric, `η^μν = η^νμ`. -/
lemma formTensor_up_symm : {η | μ ν = η | ν μ}ᵀ := by
  tensor_regroup

/-- `η_μν` is symmetric, `η_μν = η_νμ`. -/
lemma formTensor_down_symm : {η' | μ ν = η' | ν μ}ᵀ := by
  tensor_regroup

/-- The Schouten identity for left-handed indices, `ε_γρ δ^α_α' = ε_α'ρ δ_γ^α - ε_α'γ δ_ρ^α`. The
free lower index `α'` is the first index of each `ε`, the one that lowering contracts. -/
lemma schouten_downL :
    {εL' | γ ρ ⊗ δL | α α' = εL' | α' ρ ⊗ δL' | γ α + -{εL' | α' γ ⊗ δL' | ρ α}ᵀ | α' γ ρ α}ᵀ := by
  tensor_regroup using Species.schouten_formTensor_deltaTensor (S := complexLorentz) downL
    (Fintype.card_fin 2)

/-- The Schouten identity for right-handed indices,
`ε_γ̇ρ̇ δ_α̇^α̇' = ε_α̇ρ̇ δ_γ̇^α̇' - ε_α̇γ̇ δ_ρ̇^α̇'`. The free lower index `α̇` is the first
index of each `ε`. -/
lemma schouten_downR :
    {εR' | γ ρ ⊗ δR' | α α' = εR' | α ρ ⊗ δR' | γ α' + -{εR' | α γ ⊗ δR' | ρ α'}ᵀ | α γ ρ α'}ᵀ := by
  tensor_regroup using Species.schouten_formTensor_deltaTensor_dual (S := complexLorentz) downR
    (Fintype.card_fin 2)

/-- Swapping the indices of the delta at `c` gives the delta at `c.dual`, as `δ^μ_ν = δ_ν^μ`. -/
lemma deltaTensor_swap (c : Color Kind) :
    {complexLorentz.deltaTensor c | μ ν = complexLorentz.deltaTensor c.dual | ν μ}ᵀ := by
  tensor_regroup

end complexLorentz

/-!

## F. Weyl spinors and complex vectors as tensors

-/

namespace complexLorentz

/-- A left-handed Weyl spinor `ψ^α` is a tensor with one upper left-handed index. -/
noncomputable instance leftHandedWeylTensorial : Tensorial complexLorentz ![upL] LeftHandedWeyl :=
  Tensorial.ofIndexSpace complexLorentz upL

/-- A dual left-handed Weyl spinor `ψ_α` is a tensor with one lower left-handed index. -/
noncomputable instance dualLeftHandedWeylTensorial :
    Tensorial complexLorentz ![downL] DualLeftHandedWeyl :=
  Tensorial.ofIndexSpace complexLorentz downL

/-- A right-handed Weyl spinor `ψ̄^α̇` is a tensor with one upper right-handed index. -/
noncomputable instance rightHandedWeylTensorial :
    Tensorial complexLorentz ![upR] RightHandedWeyl :=
  Tensorial.ofIndexSpace complexLorentz upR

/-- A dual right-handed Weyl spinor `ψ̄_α̇` is a tensor with one lower right-handed index. -/
noncomputable instance dualRightHandedWeylTensorial :
    Tensorial complexLorentz ![downR] DualRightHandedWeyl :=
  Tensorial.ofIndexSpace complexLorentz downR

/-- A complex Lorentz vector `v^μ` is a tensor with one upper vector index. -/
noncomputable instance complexVectorTensorial : Tensorial complexLorentz ![up] ComplexVector :=
  Tensorial.ofIndexSpace complexLorentz up

/-- A complex Lorentz covector `w_μ` is a tensor with one lower vector index. -/
noncomputable instance complexCoVectorTensorial :
    Tensorial complexLorentz ![down] ComplexCoVector :=
  Tensorial.ofIndexSpace complexLorentz down

/-- The action on a left-handed Weyl spinor is `LeftHandedWeyl.rep`. -/
example (g : SL(2, ℂ)) (ψ : LeftHandedWeyl) : Tensorial.rep g ψ = LeftHandedWeyl.rep g ψ := rfl

/-- The components of the tensor of `ψ^α` are its components in `LeftHandedWeyl.basis`. -/
example (ψ : LeftHandedWeyl) (μ : Π i, Idx (![upL] i).kind) :
    (complexLorentz.tensorBasis ![upL]).repr (Tensorial.toTensor ψ) μ =
      LeftHandedWeyl.basis.repr ψ (μ 0) := by
  exact Tensorial.tensorBasis_repr_toTensor_ofIndexSpace (S := complexLorentz) upL ψ μ

/-- The components `T^αβ̇` of the tensor of `T` in `LeftHandedWeyl ⊗ RightHandedWeyl` are the
entries of the matrix `leftRightToMatrix T`. -/
lemma tensorBasis_repr_toTensor_leftRight (T : LeftHandedWeyl ⊗[ℂ] RightHandedWeyl)
    (μ : Π i, Idx (prodColors ![upL] ![upR] i).kind) :
    (complexLorentz.tensorBasis _).repr (Tensorial.toTensor T) μ =
      leftRightToMatrix T (μ (.inl 0)) (μ (.inr 0)) :=
  Tensorial.tensorBasis_repr_toTensor_prod_ofIndexSpace (S := complexLorentz) upL upR T μ

/-- The pairing `ψ^α φ_α` of a spinor with a dual spinor is invariant. -/
example (g : SL(2, ℂ)) (ψ : LeftHandedWeyl) (φ : DualLeftHandedWeyl) :
    {Tensorial.rep g ψ | α ⊗ Tensorial.rep g φ | α}ᵀ = {ψ | α ⊗ φ | α}ᵀ := by
  rw [Tensorial.toTensor_rep, Tensorial.toTensor_rep, Species.tmulEquiv_smul,
    Species.intertwiningMap_smul, Species.smul_eq_self_of_isEmpty]

end complexLorentz

/-!

## G. Examples

-/

namespace complexLorentz

/-- `ε^αβ ε_βγ = δ^α_γ`, by `tensor_regroup` through `contr_formTensor_formTensor`. -/
example : {εL | α β ⊗ εL' | β γ = δL | α γ}ᵀ := by
  tensor_regroup

/-- `g^αβ g_βγ = δ^α_γ` at every color: `ε`, `ε'` and `η` with their duals. -/
example (c : Color Kind) : {complexLorentz.formTensor c | α β ⊗
    complexLorentz.formTensor c.dual | β γ = complexLorentz.deltaTensor c.dual | α γ}ᵀ := by
  tensor_regroup

/-- The components of `ε^αβ ⊗ ε^α̇β̇` are the products of the components of `εL` and `εR`. -/
lemma tensorBasis_repr_formTensor_upL_tmul_upR
    (μ : Π i, Idx (![upL, upL, upR, upR] i).kind) :
    (complexLorentz.tensorBasis _).repr {εL | α β ⊗ εR | α' β'}ᵀ μ =
      metricRaw (μ 0) (μ 1) * metricRaw (μ 2) (μ 3) := by
  rw [Species.tensorBasis_repr_reindex, Species.tensorBasis_repr_tmulEquiv,
    tensorBasis_repr_formTensor_upL, tensorBasis_repr_formTensor_upR]
  rfl

/-- `(ε^αβ ε_βγ)` at `α = γ = 0` is `1`, from the components of `εL` and `εL'`. -/
example : (complexLorentz.tensorBasis _).repr {εL | α β ⊗ εL' | β γ}ᵀ
    (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) fun i => i.elim0)) = 1 := by
  rw [Species.Tensor.tensorBasis_repr_contr_one_pair]
  simp only [Species.tensorBasis_repr_reindex, Species.tensorBasis_repr_tmulEquiv,
    tensorBasis_repr_formTensor_upL, tensorBasis_repr_formTensor downL]
  change ∑ β : Fin 2, metricRaw 0 β * (-metricRaw) β 0 = 1
  simp [metricRaw, Fin.sum_univ_two]

/-- The conjugate of `ε^αβ` is `ε^α̇β̇`. The conjugate lands on `![upR, upR]` directly. -/
example : Species.Tensor.conj (fun i => by fin_cases i <;> rfl) εL = εR := by
  refine (complexLorentz.tensorBasis _).repr.injective (Finsupp.ext fun μ => ?_)
  rw [tensorBasis_repr_conj, tensorBasis_repr_formTensor_upL, tensorBasis_repr_formTensor_upR]
  -- The labels are `idxBar` along `rfl` of `μ 0` and `μ 1`, the identity.
  have h (a b : Fin 2) : star (metricRaw a b) = metricRaw a b := by
    fin_cases a <;> fin_cases b <;> simp [metricRaw]
  exact h _ _

end complexLorentz

end Tensor
