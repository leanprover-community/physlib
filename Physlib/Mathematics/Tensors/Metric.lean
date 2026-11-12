/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.ForMathlib.Schouten
public import Physlib.Mathematics.ForMathlib.SesquilinearForm
public import Physlib.Mathematics.Tensors.LinearMap
/-!

# Invariant forms, metrics, and lowering and raising indices

An invariant form takes an index to its dual color, lowering an upper index and raising a lower
one.

## i. Overview

For Lorentz tensors the invariant form is the Minkowski metric `η_μν` with inverse `η^μν`. It
lowers `v_ν = η_νμ v^μ`, raises `w^ν = η^νμ w_μ`, and the two are inverse,
`v^μ η_μν η^νρ = v^ρ`.

The class `S.HasForm κ` is a chosen invariant form on the kind `κ`, `g^μν` at the upper color and
`g_μν` at the lower one, with the forms at `c` and `c.dual` inverse to each other. Not every kind
has one, as the SU(3) triplet has none. The inverse is stored with the form. Symmetry, as for
`η`, and antisymmetry, as for the Weyl `ε`, are the optional classes `S.IsSymmetricForm κ` and
`S.IsAntisymmetricForm κ`.

`S.toDual c` contracts a vector with the second index of the form at `c.dual`, lowering an upper
index, `v_ν = g_νμ v^μ`, and raising a lower one, `w^ν = g^νμ w_μ`, and `S.toDualAt i` does so at
the index `i` of a tensor. `S.toDual c` is `Module.Basis.coordToDual` for the bases of `c` and
`c.dual`. For the antisymmetric `ε`, where the order of the indices matters,
lowering gives `ψ_α = ε_αβ ψ^β`, the convention of Wess and Bagger and of Dreiner, Haber and
Martin.

## ii. Key results

- `Species.HasForm` is an invariant form on a kind with its inverse, `g_μν` and `g^μν`, with
  `Species.form`, `Species.form_invariant` and `Species.form_inverse`.
- `Species.IsSymmetricForm` and `Species.IsAntisymmetricForm` say that the form is symmetric or
  antisymmetric, `Species.form_symm` and `Species.form_antisymm`, in components
  `Species.formMatrix_symm` and `Species.formMatrix_antisymm`, and `Species.comm_form_eq_smul`
  gives either from the components of the form.
- `Species.formBilin` reads the form as a Mathlib bilinear form, symmetric by
  `Species.isSymm_formBilin` and alternating by `Species.isAlt_formBilin`.
- `Species.toDual` lowers an upper index and raises a lower one, and `Species.toDual_toDual` that
  raising undoes lowering.
- `Species.formTensor` is the form as a tensor on two indices.
- `Species.toDualAt` lowers or raises one index of a tensor, with
  `Species.toDualAt_toDualAt`, `Species.toDualAt_eq_mapAt` and, in components,
  `Species.tensorBasis_repr_toDualAt`.
- `Species.toDualAt_eq_contr` proves that lowering is contracting with the form,
  `T^…_ν… = g_νμ T^…μ…`.
- `Species.formMatrix_schouten` is the Schouten identity for an antisymmetric form on a kind with
  two labels in components, `g^γρ δ^α_α' = g^γα' δ^α_ρ - g^ρα' δ^α_γ`,
  `LinearMap.IsAlt.schouten_basis` for `formBilin`.

## iii. Table of contents

- A. Invariant forms and metrics
- B. Lowering and raising vectors
- C. The form as a tensor
- D. Lowering and raising at one index
- E. Forms on a kind with two labels

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensor

namespace Species

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-!

## A. Invariant forms and metrics

-/

variable (S : Species k G K basisIdx) in
/-- A chosen invariant invertible bilinear form on the kind `κ`. At both colors of `κ` it gives an
invariant element `g` of `V c ⊗ V c`, `g^μν` at the upper color and `g_μν` at the lower one, with
the two forms inverse to each other. It need not be symmetric, so it covers both `η` and the Weyl
`ε`. -/
class HasForm (κ : K) where
  /-- The form at the color `⟨κ, v⟩`, an element of `V ⟨κ, v⟩ ⊗ V ⟨κ, v⟩`. -/
  formAt : (v : Variance) → S.V ⟨κ, v⟩ ⊗[k] S.V ⟨κ, v⟩
  /-- The form is invariant, `Λ g = g` for every `Λ : G`. -/
  formAt_invariant : ∀ v (Λ : G),
    TensorProduct.map (S.rep ⟨κ, v⟩ Λ) (S.rep ⟨κ, v⟩ Λ) (formAt v) = formAt v
  /-- The forms at the two variances are inverse as linear maps, `v^μ g_μν g^νρ = v^ρ`. The
  vector is contracted with the first index of each form. -/
  formAt_inverse : ∀ v, S.toLin (formAt v) ∘ₗ S.toLin (formAt v.dual) = LinearMap.id

variable {S : Species k G K basisIdx}

/-- The form at the color `c`, `g^μν` at an upper color and `g_μν` at a lower one. -/
noncomputable def form (c : Color K) [S.HasForm c.kind] : S.V c ⊗[k] S.V c :=
  HasForm.formAt c.variance

/-- The form is invariant, `Λ g = g` for every `Λ : G`. -/
lemma form_invariant (c : Color K) [S.HasForm c.kind] (Λ : G) :
    TensorProduct.map (S.rep c Λ) (S.rep c Λ) (form c) = form c :=
  HasForm.formAt_invariant c.variance Λ

/-- The forms at `c` and at `c.dual` are inverse as linear maps, `v^μ g_μν g^νρ = v^ρ` at an
upper color `c`. -/
lemma form_inverse (c : Color K) [S.HasForm c.kind] :
    S.toLin (form c) ∘ₗ S.toLin (form c.dual) = LinearMap.id :=
  HasForm.formAt_inverse c.variance

/-- The linear map of the form at `c` is bijective. -/
lemma toLin_form_bijective (c : Color K) [S.HasForm c.kind] :
    Function.Bijective (S.toLin (form c)) :=
  Function.bijective_iff_has_inverse.mpr ⟨S.toLin (form c.dual),
    LinearMap.congr_fun (form_inverse c.dual), LinearMap.congr_fun (form_inverse c)⟩

variable (S) in
/-- The form at `c` read as a bilinear form on `V c.dual`, `(u, v) ↦ u_μ g^μν v_ν`, with the first
argument contracted with the first index of the form. -/
noncomputable def formBilin (c : Color K) [S.HasForm c.kind] :
    LinearMap.BilinForm k (S.V c.dual) :=
  (TensorProduct.curry (S.contr c.dual).toLinearMap).flip ∘ₗ S.toLin (form c)

lemma formBilin_apply (c : Color K) [S.HasForm c.kind] (u v : S.V c.dual) :
    S.formBilin c u v = S.contr c.dual (v ⊗ₜ S.toLin (form c) u) :=
  rfl

variable (S) in
/-- The components of the form at `c`, `g^μν` at an upper color and `g_μν` at a lower one, its
coordinates in Mathlib's product basis. Component lemmas of a species are stated on it, so that
`simp` finds them at a literal color. -/
noncomputable def formMatrix (c : Color K) [S.HasForm c.kind] :
    Matrix (basisIdx c.kind) (basisIdx c.kind) k :=
  fun μ ν => ((S.basis c).tensorProduct (S.basis c)).repr (form c) (μ, ν)

/-- The components of the form are Mathlib's matrix of `formBilin c` in the basis of `c.dual`,
`g^μν = g(e^μ, e^ν)`. -/
lemma formMatrix_eq_toMatrix (c : Color K) [S.HasForm c.kind] :
    S.formMatrix c = LinearMap.BilinForm.toMatrix (S.basis c.dual) (S.formBilin c) := by
  ext μ ν
  rw [LinearMap.BilinForm.toMatrix_apply, formBilin_apply, contr_tmul_eq_sum_basis]
  simp only [Module.Basis.repr_self, Finsupp.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  refine ((Module.Basis.repr_coordTensorHomEquiv (S.basis c) (S.basis c.dual) (S.basis c) (form c)
    _ ν).trans ?_).symm
  simp [Finsupp.single_apply, formMatrix]

/-- The form on two basis vectors is a component of the form, `g(e^μ, e^ν) = g^μν`. -/
lemma formBilin_basis (c : Color K) [S.HasForm c.kind] (μ ν : basisIdx c.kind) :
    S.formBilin c (S.basis c.dual μ) (S.basis c.dual ν) = S.formMatrix c μ ν := by
  rw [formMatrix_eq_toMatrix, LinearMap.BilinForm.toMatrix_apply]

variable (S) in
/-- The form on the kind `κ` is symmetric, `g_μν = g_νμ`, as `η`. A metric is a symmetric form. -/
class IsSymmetricForm (κ : K) [S.HasForm κ] : Prop where
  /-- Swapping the two indices of the form gives the form. -/
  comm_form : ∀ v, TensorProduct.comm k _ _ (form (S := S) ⟨κ, v⟩) = form ⟨κ, v⟩

variable (S) in
/-- The form on the kind `κ` is antisymmetric, `g_μν = -g_νμ`, as the Weyl `ε`. -/
class IsAntisymmetricForm (κ : K) [S.HasForm κ] : Prop where
  /-- Swapping the two indices of the form gives minus the form. -/
  comm_form : ∀ v, TensorProduct.comm k _ _ (form (S := S) ⟨κ, v⟩) = -form ⟨κ, v⟩

/-- A symmetric form, `g_μν = g_νμ`. -/
lemma form_symm (c : Color K) [S.HasForm c.kind] [S.IsSymmetricForm c.kind] :
    TensorProduct.comm k (S.V c) (S.V c) (form c) = form c :=
  IsSymmetricForm.comm_form c.variance

/-- The components of a symmetric form are symmetric, `g^νμ = g^μν`. -/
lemma formMatrix_symm (c : Color K) [S.HasForm c.kind] [S.IsSymmetricForm c.kind]
    (μ ν : basisIdx c.kind) : S.formMatrix c ν μ = S.formMatrix c μ ν :=
  (((S.basis c).comm_eq_smul_iff _ 1).1 ((form_symm c).trans (one_smul k _).symm) μ ν).trans
    (one_mul _)

/-- A symmetric form is symmetric as a bilinear form, Mathlib's `LinearMap.BilinForm.IsSymm`. -/
lemma isSymm_formBilin (c : Color K) [S.HasForm c.kind] [S.IsSymmetricForm c.kind] :
    (S.formBilin c).IsSymm :=
  (S.basis c).isSymm_coordTensorHomEquiv_of_comm_eq (S.basis c.dual) (form_symm c)

/-- An antisymmetric form, `g_μν = -g_νμ`. -/
lemma form_antisymm (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind] :
    TensorProduct.comm k (S.V c) (S.V c) (form c) = -form c :=
  IsAntisymmetricForm.comm_form c.variance

/-- The components of an antisymmetric form are antisymmetric, `g^νμ = -g^μν`. -/
lemma formMatrix_antisymm (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind]
    (μ ν : basisIdx c.kind) : S.formMatrix c ν μ = -S.formMatrix c μ ν :=
  (((S.basis c).comm_eq_smul_iff _ (-1)).1
    ((form_antisymm c).trans (neg_one_smul k _).symm) μ ν).trans (neg_one_mul _)

/-- Swapping the two indices of the form scales it by `r` when its components do,
`g^νμ = r g^μν`. With `r = 1` it gives `IsSymmetricForm`, with `r = -1` `IsAntisymmetricForm`. -/
lemma comm_form_eq_smul (c : Color K) [S.HasForm c.kind] (r : k)
    (h : ∀ μ ν, S.formMatrix c ν μ = r * S.formMatrix c μ ν) :
    TensorProduct.comm k (S.V c) (S.V c) (form c) = r • form c :=
  ((S.basis c).comm_eq_smul_iff _ r).2 h

/-- An antisymmetric form is alternating as a bilinear form, `g(u, u) = 0`, Mathlib's
`LinearMap.IsAlt`. It uses that `k` has characteristic zero. -/
lemma isAlt_formBilin (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind] :
    LinearMap.IsAlt (S.formBilin c) :=
  (S.basis c).isAlt_coordTensorHomEquiv_of_comm_eq_neg (S.basis c.dual) (form_antisymm c)

/-!

## B. Lowering and raising vectors

-/

variable (S) in
/-- The vector `v` of color `c` contracted with the second index of the form at `c.dual`. It
lowers an upper index, `v^μ ↦ g_νμ v^μ`, and raises a lower one, `w_μ ↦ g^νμ w_μ`. -/
noncomputable def toDual (c : Color K) [S.HasForm c.kind] : (S.rep c).Equiv (S.rep c.dual) :=
  .mk ((S.basis c).coordToDual (S.basis c.dual) _ _ (form_inverse c) (form_inverse c.dual))
    fun g => LinearMap.ext <|
      ((S.isIntertwiningMap_toLin_iff (a := c.dual) (b := c.dual) _).2 fun g => by
        rw [TensorProduct.map_comm, form_invariant]).isIntertwining g

/-- Raising undoes lowering, `(v_ν)^ν = v^ν`. -/
@[simp]
lemma toDual_toDual (c : Color K) [S.HasForm c.kind] (v : S.V c) :
    S.toDual c.dual (S.toDual c v) = v :=
  (S.toDual c).toLinearEquiv.symm_apply_apply v

/-- Lowering or raising a vector in components, `v_ν = g_νμ v^μ`. -/
lemma basis_repr_toDual (c : Color K) [S.HasForm c.kind] (v : S.V c) (ν : basisIdx c.kind) :
    (S.basis c.dual).repr (S.toDual c v) ν = ∑ μ, (S.basis c).repr v μ *
      S.formMatrix c.dual ν μ :=
  Module.Basis.repr_coordToDual _ _ _ _ (form_inverse c) (form_inverse c.dual) v ν

/-!

## C. The form as a tensor

-/

variable (S) in
/-- The form at `c` as a tensor with colors `![c, c]`, `g^μν` at an upper color and `g_μν` at a
lower one. -/
noncomputable def formTensor (c : Color K) [S.HasForm c.kind] : Tensor S ![c, c] :=
  S.twoIndexEquiv c c (form c)

/-- The form is an invariant tensor. Every group element fixes it, as every Lorentz
transformation fixes the Minkowski metric `η`. -/
lemma formTensor_invariant (c : Color K) [S.HasForm c.kind] (Λ : G) :
    Λ • S.formTensor c = S.formTensor c :=
  (S.twoIndexEquiv c c).toIntertwiningMap.map_invariant (form_invariant c Λ)

/-- The components of the form tensor are those of the form, `g_μν` at the pair of labels
`(μ 0, μ 1)`. -/
lemma tensorBasis_repr_formTensor (c : Color K) [S.HasForm c.kind]
    (μ : Π j, basisIdx (![c, c] j).kind) :
    (S.tensorBasis ![c, c]).repr (S.formTensor c) μ = S.formMatrix c (μ 0) (μ 1) :=
  tensorBasis_repr_twoIndexEquiv _ _ _ μ

/-- A symmetric form is symmetric under the index swap as a tensor, `g^μν = g^νμ`. -/
lemma formTensor_symm (c : Color K) [S.HasForm c.kind] [S.IsSymmetricForm c.kind] :
    S.reindex (ColorEquiv.swapTwo c c) (S.formTensor c) = S.formTensor c := by
  rw [formTensor, reindex_swapTwo_twoIndexEquiv, form_symm]

/-- An antisymmetric form is antisymmetric under the index swap as a tensor,
`g^μν = -g^νμ`. -/
lemma formTensor_antisymm (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind] :
    S.reindex (ColorEquiv.swapTwo c c) (S.formTensor c) = -S.formTensor c := by
  rw [formTensor, reindex_swapTwo_twoIndexEquiv, form_antisymm, map_neg]

/-!

## D. Lowering and raising at one index

-/

variable {ι : Type} [DecidableEq ι]

variable (S) in
/-- `S.toDual` at the index `i` of a tensor and the identity at the other indices, as in
`T^μν ↦ T^μ_ν` for `i` the second index. The index has the color `a` by `ha`, and the form is the
one at the kind of `a`. The colors `c'` of the result have the dual color at `i` by `hi` and agree
with `c` elsewhere by `h`. It is `congrAt` of `toDual`. -/
noncomputable def toDualAt {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) :
    (S.tensorRep c).Equiv (S.tensorRep c') :=
  S.congrAt i (((S.cast ha).trans (S.toDual a)).trans (S.cast hi.symm)) h

/-- Raising at an index undoes lowering at that index, `(T^μ_ν)^ν = T^μν`. -/
lemma toDualAt_toDualAt {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) :
    S.toDualAt i a.dual hi ha (fun x hx => (h x hx).symm) (S.toDualAt i a ha hi h t) = t := by
  rw [toDualAt, toDualAt, show ((S.cast hi).trans (S.toDual a.dual)).trans (S.cast ha.symm) =
    (((S.cast ha).trans (S.toDual a)).trans (S.cast hi.symm)).symm from rfl, ← congrAt_symm]
  exact (S.congrAt i _ h).symm_apply_apply t

/-- Lowering or raising at an index is `toDual` at that index, read as a linear map. Chains of
lowerings and raisings at several indices compose index by index through `mapIndices_mapIndices`. -/
lemma toDualAt_eq_mapAt {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) :
    S.toDualAt i a ha hi h t =
      S.mapAt i (((S.cast ha).trans (S.toDual a)).trans (S.cast hi.symm)).toLinearMap h t :=
  congrAt_eq_mapAt i _ h t

/-- Lowering or raising the index `i` in components, `T^…_ν… = g_νμ T^…μ…`. The
labels `φ` of the result are cast to labels of `t`, and the label at `i` is replaced by the summed
`μ`. For concrete colors the casts are along `rfl`. -/
lemma tensorBasis_repr_toDualAt [Fintype ι] {c c' : ι → Color K} (i : ι) (a : Color K)
    (ha : c i = a) [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x)
    (t : Tensor S c) (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (S.toDualAt i a ha hi h t) φ =
      ∑ μ, S.formMatrix a.dual (cast (congrArg (basisIdx ∘ Color.kind) hi) (φ i)) μ *
        (S.tensorBasis c).repr t (Function.update (fun x => cast (by
          by_cases hx : x = i
          · subst hx; rw [hi, ha]
          · rw [h x hx]) (φ x)) i (cast (congrArg (basisIdx ∘ Color.kind) ha.symm) μ)) := by
  subst ha
  rw [toDualAt_eq_mapAt]
  refine (tensorBasis_repr_mapAt i _ h t φ _ fun _ _ => rfl).trans
    (Finset.sum_congr rfl fun μ _ => congrArg (· * _) ?_)
  rw [LinearMap.toMatrix_apply]
  change (S.basis (c' i)).repr (S.cast hi.symm (S.toDual (c i) (S.basis (c i) μ))) (φ i) = _
  rw [basis_repr_cast, basis_repr_toDual]
  simp [Finsupp.single_apply]

/-- Lowering or raising at the index `i` is contracting that index with the second index of the
form, `T^…_ν… = g_νμ T^…μ…`. -/
lemma toDualAt_eq_contr {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) :
    S.toDualAt i a ha hi h t = Tensor.contr (ColorEquiv.matMulAt i a a.dual ha hi h)
      (S.tmulEquiv c ![a.dual, a.dual]
        (t ⊗ₜ S.reindex (ColorEquiv.swapTwo a.dual a.dual) (S.formTensor a.dual))) := by
  rw [formTensor, reindex_swapTwo_twoIndexEquiv, Tensor.contr_matMulAt, toDualAt, congrAt_eq_mapAt]
  rfl

/-!

## E. Forms on a kind with two labels

-/

/-- The Schouten identity in components, `g^γρ δ^α_α' = g^γα' δ^α_ρ - g^ρα' δ^α_γ`, for an
antisymmetric form on a kind with two labels, such as the Weyl `ε`. -/
lemma formMatrix_schouten (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind]
    (h2 : Fintype.card (basisIdx c.kind) = 2) (γ ρ α' α : basisIdx c.kind) :
    S.formMatrix c γ ρ * (if α = α' then 1 else 0) =
      S.formMatrix c γ α' * (if ρ = α then 1 else 0) -
        S.formMatrix c ρ α' * (if γ = α then 1 else 0) := by
  simpa only [formBilin_basis] using
    (isAlt_formBilin (S := S) c).schouten_basis (S.basis c.dual) h2 γ ρ α' α

end Species

end Tensor
