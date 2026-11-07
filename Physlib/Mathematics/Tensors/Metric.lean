/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Contraction
/-!

# Invariant forms, metrics, and lowering and raising indices

An invariant form takes an index to its dual color, lowering an upper index and raising a lower
one.

## i. Overview

An invariant form lowers and raises indices. For Lorentz tensors it is the Minkowski metric,
`η_μν` in `(ℝ⁴)* ⊗ (ℝ⁴)*`, with inverse `η^μν` in `ℝ⁴ ⊗ ℝ⁴`. It lowers `v_ν = v^μ η_μν`, raises
`w^ν = w_μ η^μν`, and the two are inverse, `v^μ η_μν η^νρ = v^ρ`.

An invariant form on a kind `κ`, the class `S.HasForm κ`, is a chosen invariant invertible
bilinear form. It gives an element `form c` of `V c ⊗ V c` at both colors of the kind, written
`g^μν` at the upper color and `g_μν` at the lower one. It is invariant under the group, and the
forms at `c` and at `c.dual` are inverse to each other. Not every kind needs a form. The SU(3)
species has one on the adjoint and none on the triplet, so it has a `HasForm` instance at the
adjoint only and lowering a triplet index does not typecheck. The form is a choice, since `-η`
serves as well as `η`. The class stores the inverse, checked by the law `form_inverse`, since over
a commutative ring `k` a non-degenerate form need not have an inverse.

Symmetry is an optional property of the chosen form. The class `S.IsSymmetricForm κ` says that
`g_μν = g_νμ`, as for `η`, and a metric is a symmetric form. The class `S.IsAntisymmetricForm κ`
says that `g_μν = -g_νμ`, as for the Weyl `ε`. A form on a kind that is a sum of two kinds may be
neither, and lowering and raising never ask for either property.

`S.toDual c : V c ≃ V c.dual` contracts a vector with the first index of the form at `c.dual`. At
an upper color it lowers the index, `v^μ ↦ v^μ g_μν`, and at a lower color it raises it,
`w_μ ↦ w_μ g^μν`. Its inverse is `S.toDual c.dual`, by `rfl`. For a symmetric metric such as `η`
the first index gives the textbook `v_ν = η_νμ v^μ`. For the antisymmetric `ε` it gives
`ψ_β = ψ^α ε_αβ = -ε_βα ψ^α`. With `ε^12 = ε_21 = 1` this is minus the convention
`ψ_α = ε_αβ ψ^β`, so a Weyl species following that convention stores `-ε`.

`S.toDualAt i a ha hi h` lowers or raises the index at the slot `i` of a tensor and keeps the
others, as in `T^μν ↦ T^μ_ν` for `i` the second slot. It is `congrAt` of `toDual`. The caller
names the color `a` of the slot, with `ha : c i = a`, so that the form is found at the kind of `a`.
Lowering and raising at that slot can then use the same instance without moving it, as in
`toDualAt_toDualAt`. The caller also states the colors `c'` of the result, such as
`![⟨vec, up⟩, ⟨vec, down⟩]`. The hypothesis `hi` says that `c'` has the dual color `a.dual` at `i`,
and `h` that it agrees with the colors `c` of the tensor elsewhere.

`S.formTensor c` is the form as a tensor on two slots, `η^μν` at `⟨vec, up⟩` and `η_μν` at
`⟨vec, down⟩`. Lowering an index is contracting it with the form tensor, `M^μν g_νρ = M^μ_ρ`.

## ii. Key results

- `Species.HasForm` is an invariant form on a kind with its inverse, `g_μν` and `g^μν`, and
  `Species.form` is the form at a color of that kind, with `Species.form_invariant` and
  `Species.form_inverse`.
- `Species.formMatrix` gives the components `g_μν` of the form, on which each species states its
  component lemma.
- `Species.IsSymmetricForm` and `Species.IsAntisymmetricForm` say that the form is symmetric or
  antisymmetric, with `Species.form_symm` and `Species.form_antisymm`.
- `Species.toDual` is `S.V c ≃ S.V c.dual`, lowering an upper index and raising a lower one.
- `Species.toDual_symm` proves that raising is the inverse of lowering.
- `Species.toDual_rep` and `Species.toDualAt_smul` prove `(Λv)_ν = Λ(v_ν)`, for a vector and at
  one index of a tensor.
- `Species.toDualAt` lowers or raises the index at one slot of a tensor.
- `Species.toDualAt_toDualAt` proves that raising at a slot undoes lowering there, and
  `Species.toDualAt_comm` that lowering at two different slots commute.
- `Species.tensorBasis_repr_toDualAt` gives lowering at a slot in components,
  `T^…_ν… = T^…μ… g_μν`.
- `Species.toDualAt_twoSlotEquiv` proves that lowering the second index of a tensor on two slots,
  `M^μν ↦ M^μ_ν`, is `toDual` on the second factor.
- `Species.toDualAt_eq_contr` proves that lowering at any slot is contracting with the form,
  `T^…_ν… = T^…μ… g_μν`, and `Species.toDualAt_eq_contr_formTensor` gives the same at the second
  slot of a tensor on two slots, `M^μν g_νρ = M^μ_ρ`.
- `Species.formTensor` is the form as a tensor on two slots, and `Species.formTensor_invariant`
  proves that it is invariant.
- `Species.tensorBasis_repr_formTensor` gives the components of the form tensor.
- `Species.formTensor_symm` and `Species.formTensor_antisymm` prove `g^μν = g^νμ` and
  `g^μν = -g^νμ` as tensors for a symmetric or antisymmetric form.

## iii. Table of contents

- A. Invariant forms and metrics
- B. Lowering and raising vectors
- C. Lowering and raising at one index
- D. The form as a tensor

## iv. References

None.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensors

namespace Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-!

## A. Invariant forms and metrics

-/

variable (S : Species k G K basisIdx) in
/-- A chosen invariant invertible bilinear form on the kind `κ`. At both colors of `κ` it gives an
invariant element `g` of `V c ⊗ V c`, `g^μν` at the upper color and `g_μν` at the lower one, with
the two forms inverse to each other. It need not be symmetric, so it covers both `η` and the Weyl
`ε`. The invariance at the lower color follows from that at the upper one and `formAt_inverse`,
but a field for both variances cannot state only half. -/
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

variable (S) in
/-- The components of the form at `c`, `g^μν` at an upper color and `g_μν` at a lower one, its
coordinates in Mathlib's product basis. Component lemmas of a species are stated on it, so that
`simp` finds them at a literal color. -/
noncomputable def formMatrix (c : Color K) [S.HasForm c.kind] :
    Matrix (basisIdx c.kind) (basisIdx c.kind) k :=
  fun μ ν => ((S.basis c).tensorProduct (S.basis c)).repr (form c) (μ, ν)

/-- The form is invariant, `Λ g = g` for every `Λ : G`. -/
lemma form_invariant (c : Color K) [S.HasForm c.kind] (Λ : G) :
    TensorProduct.map (S.rep c Λ) (S.rep c Λ) (form c) = form c :=
  HasForm.formAt_invariant c.variance Λ

/-- The forms at `c` and at `c.dual` are inverse as linear maps, `v^μ g_μν g^νρ = v^ρ` at an
upper color `c`. -/
lemma form_inverse (c : Color K) [S.HasForm c.kind] :
    S.toLin (form c) ∘ₗ S.toLin (form c.dual) = LinearMap.id :=
  HasForm.formAt_inverse c.variance

variable (S) in
/-- The form on the kind `κ` is symmetric, `g_μν = g_νμ`, as `η`. A metric is a symmetric form. -/
class IsSymmetricForm (κ : K) [S.HasForm κ] : Prop where
  /-- Swapping the two indices of the form gives the form. -/
  comm_form : ∀ v, TensorProduct.comm k _ _ (form (S := S) ⟨κ, v⟩) = form ⟨κ, v⟩

variable (S) in
/-- The form on the kind `κ` is antisymmetric, `g_μν = -g_νμ`, as the Weyl `ε`. Antisymmetric is
not alternating: when `2 = 0` in `k` the form `[1]` on `k` is antisymmetric with `g(1, 1) = 1`. -/
class IsAntisymmetricForm (κ : K) [S.HasForm κ] : Prop where
  /-- Swapping the two indices of the form gives minus the form. -/
  comm_form : ∀ v, TensorProduct.comm k _ _ (form (S := S) ⟨κ, v⟩) = -form ⟨κ, v⟩

/-- A symmetric form, `g_μν = g_νμ`. -/
lemma form_symm (c : Color K) [S.HasForm c.kind] [S.IsSymmetricForm c.kind] :
    TensorProduct.comm k (S.V c) (S.V c) (form c) = form c :=
  IsSymmetricForm.comm_form c.variance

/-- An antisymmetric form, `g_μν = -g_νμ`. -/
lemma form_antisymm (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind] :
    TensorProduct.comm k (S.V c) (S.V c) (form c) = -form c :=
  IsAntisymmetricForm.comm_form c.variance

/-!

## B. Lowering and raising vectors

-/

variable (S) in
/-- The vector `v` of color `c` contracted with the first index of the form at `c.dual`. It lowers
an upper index, `v^μ ↦ v^μ g_μν`, and raises a lower one, `w_μ ↦ w_μ g^μν`. -/
noncomputable def toDual (c : Color K) [S.HasForm c.kind] : S.V c ≃ₗ[k] S.V c.dual :=
  LinearEquiv.ofLinearMap (S.toLin (form c.dual)) (S.toLin (form c)) (form_inverse c.dual)
    (form_inverse c)

/-- `toDual` contracts `v` with the first index of the form at `c.dual`. -/
lemma toDual_apply (c : Color K) [S.HasForm c.kind] (v : S.V c) :
    S.toDual c v = S.toLin (form c.dual) v := rfl

/-- Raising is the inverse of lowering. The inverse of `S.toDual c` is `S.toDual c.dual`. -/
lemma toDual_symm (c : Color K) [S.HasForm c.kind] : (S.toDual c).symm = S.toDual c.dual := rfl

/-- Lowering and raising commute with the group action, `(Λv)_ν = Λ(v_ν)`. -/
lemma toDual_rep (c : Color K) [S.HasForm c.kind] (g : G) (v : S.V c) :
    S.toDual c (S.rep c g v) = S.rep c.dual g (S.toDual c v) := by
  rw [toDual_apply, toDual_apply, ← S.toLin_map, form_invariant]

/-- Lowering or raising a vector in components, `v_ν = v^μ g_μν`. -/
lemma basis_repr_toDual (c : Color K) [S.HasForm c.kind] (v : S.V c) (ν : basisIdx c.kind) :
    (S.basis c.dual).repr (S.toDual c v) ν = ∑ μ, (S.basis c).repr v μ *
      S.formMatrix c.dual μ ν := by
  rw [toDual_apply, basis_repr_toLin]
  rfl

/-!

## C. Lowering and raising at one index

-/

variable {ι : Type} [DecidableEq ι]

variable (S) in
/-- `S.toDual` at the slot `i` of a tensor and the identity at the other slots, as in
`T^μν ↦ T^μ_ν` for `i` the second slot. The slot has the color `a` by `ha`, and the form is the one
at the kind of `a`. The colors `c'` of the result have the dual color at `i` by `hi` and agree
with `c` elsewhere by `h`. It is `congrAt` of `toDual`. -/
noncomputable def toDualAt {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) :
    S.Tensor c ≃ₗ[k] S.Tensor c' :=
  S.congrAt i (S.cast ha ≪≫ₗ S.toDual a ≪≫ₗ S.cast hi.symm) h

/-- Lowering or raising at a slot commutes with the group action, `(ΛT)^μ_ν = Λ(T^μ_ν)`. -/
lemma toDualAt_smul {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) (g : G)
    (t : S.Tensor c) : S.toDualAt i a ha hi h (g • t) = g • S.toDualAt i a ha hi h t :=
  congrAt_smul i _ h (fun g x => by simp only [LinearEquiv.trans_apply, toDual_rep, cast_rep])
    g t

/-- On a pure tensor, `toDualAt` applies `toDual` to the vector at `i` and keeps the others. The
result `q` is explicit, so that for concrete colors `hqi` and `hq` hold by `rfl`. -/
lemma toDualAt_pure {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x)
    (p : Π x, S.V (c x)) (q : Π x, S.V (c' x))
    (hqi : q i = S.cast hi.symm (S.toDual a (S.cast ha (p i))))
    (hq : ∀ x (hx : x ≠ i), q x = S.cast (h x hx) (p x)) :
    S.toDualAt i a ha hi h (S.pure p) = S.pure q :=
  congrAt_pure i _ h p q hqi hq

/-- Raising at a slot undoes lowering at that slot, `(T^μ_ν)^ν = T^μν`. -/
lemma toDualAt_toDualAt {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) (t : S.Tensor c) :
    S.toDualAt i a.dual hi ha (fun x hx => (h x hx).symm) (S.toDualAt i a ha hi h t) = t := by
  rw [toDualAt, toDualAt, show S.cast hi ≪≫ₗ S.toDual a.dual ≪≫ₗ S.cast ha.symm =
    (S.cast ha ≪≫ₗ S.toDual a ≪≫ₗ S.cast hi.symm).symm from rfl, ← congrAt_symm]
  exact (S.congrAt i _ h).symm_apply_apply t

/-- Lowering or raising at two different slots commute, `(T_μ)_ν = (T_ν)_μ`. The colors `c₁` and
`c₂` are those after the first step in either order. On literal slots the hypotheses `h₂` and
`h₂'` are found automatically, as the index notation finds them. -/
lemma toDualAt_comm {c c₁ c₂ c' : ι → Color K} {i j : ι} (hij : i ≠ j) (a b : Color K)
    [S.HasForm a.kind] [S.HasForm b.kind]
    {ha : c i = a} {hi : c₁ i = a.dual} {h : ∀ x, x ≠ i → c x = c₁ x}
    {hb : c₁ j = b} {hj : c' j = b.dual} {h' : ∀ x, x ≠ j → c₁ x = c' x}
    (hb₂ : c j = b) (hj₂ : c₂ j = b.dual) (ha₂ : c₂ i = a) (hi₂ : c' i = a.dual)
    (h₂ : ∀ x, x ≠ j → c x = c₂ x := by
      intro x hx; fin_cases x <;> first | rfl | exact absurd rfl hx)
    (h₂': ∀ x, x ≠ i → c₂ x = c' x := by
      intro x hx; fin_cases x <;> first | rfl | exact absurd rfl hx) (t : S.Tensor c) :
    S.toDualAt j b hb hj h' (S.toDualAt i a ha hi h t) =
      S.toDualAt i a ha₂ hi₂ h₂' (S.toDualAt j b hb₂ hj₂ h₂ t) :=
  congrAt_comm hij _ _ _ _ _ _ _ _
    (fun v => by simp only [LinearEquiv.trans_apply, LinearEquiv.cast_apply, cast_cast])
    (fun v => by simp only [LinearEquiv.trans_apply, LinearEquiv.cast_apply, cast_cast]) t

/-- Lowering or raising the second index of a tensor on two slots, `M^μν ↦ M^μ_ν`, is `toDual` on
the second factor of `M ∈ V a ⊗ V c`. -/
lemma toDualAt_twoSlotEquiv (a c : Color K) [S.HasForm c.kind] (M : S.V a ⊗[k] S.V c) :
    S.toDualAt (c := ![a, c]) (c' := ![a, c.dual]) 1 c rfl rfl
      (fun x hx => by fin_cases x <;> simp_all) (S.twoSlotEquiv a c M) =
      S.twoSlotEquiv a c.dual ((S.toDual c).toLinearMap.lTensor _ M) := by
  induction M using TensorProduct.inductionOn with
  | add M M' hM hM' => simp only [map_add, hM, hM']
  | tmul x y =>
    rw [twoSlotEquiv_tmul, LinearMap.lTensor_tmul, twoSlotEquiv_tmul]
    exact toDualAt_pure _ _ _ _ _ _ _ rfl
      (fun x hx => by fin_cases x <;> first | rfl | exact absurd rfl hx)

/-- Lowering or raising the index at the slot `i` in components, `T^…_ν… = T^…μ… g_μν`. The
labels `φ` of the result are cast to labels of `t`, and the label at `i` is replaced by the summed
`μ`. For concrete colors the casts are along `rfl`. -/
lemma tensorBasis_repr_toDualAt [Fintype ι] {c c' : ι → Color K} (i : ι) (a : Color K)
    (ha : c i = a) [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x)
    (t : S.Tensor c) (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (S.toDualAt i a ha hi h t) φ =
      ∑ μ, S.formMatrix a.dual μ (cast (congrArg (basisIdx ∘ Color.kind) hi) (φ i)) *
        (S.tensorBasis c).repr t (Function.update (fun x => cast (by
          by_cases hx : x = i
          · subst hx; rw [hi, ha]
          · rw [h x hx]) (φ x)) i (cast (congrArg (basisIdx ∘ Color.kind) ha.symm) μ)) := by
  subst ha
  induction t using inductionOn_pure with
  | hsmul r t ht =>
    simp only [map_smul, Finsupp.smul_apply, ht, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  | hadd t t' ht ht' =>
    simp only [map_add, Finsupp.add_apply, ht, ht', mul_add, Finset.sum_add_distrib]
  | h p =>
    rw [toDualAt_pure i _ rfl hi h p (fun x => if hx : x = i then hx ▸
        S.cast hi.symm (S.toDual (c i) (p i)) else S.cast (h x hx) (p x))
        (dite_eq_left rfl) (fun x hx => dite_eq_right hx), tensorBasis_repr_pure,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), dite_eq_left rfl, basis_repr_cast,
      basis_repr_toDual, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [tensorBasis_repr_pure, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      Function.update_self, mul_left_comm, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx := Finset.ne_of_mem_erase hx
    rw [dite_eq_right hx, basis_repr_cast, Function.update_of_ne hx]

/-!

## D. The form as a tensor

-/

variable (S) in
/-- The form at `c` as a tensor with colors `![c, c]`, `g^μν` at an upper color and `g_μν` at a
lower one. -/
noncomputable def formTensor (c : Color K) [S.HasForm c.kind] : S.Tensor ![c, c] :=
  S.twoSlotEquiv c c (form c)

/-- The form is an invariant tensor. Every group element fixes it, as every Lorentz
transformation fixes the Minkowski metric `η`. -/
lemma formTensor_invariant (c : Color K) [S.HasForm c.kind] (Λ : G) :
    Λ • S.formTensor c = S.formTensor c := by
  rw [formTensor, ← twoSlotEquiv_map_rep, form_invariant]

/-- The components of the form tensor are those of the form, `g_μν` at the pair of labels
`(μ 0, μ 1)`. -/
lemma tensorBasis_repr_formTensor (c : Color K) [S.HasForm c.kind]
    (μ : Π j, basisIdx (![c, c] j).kind) :
    (S.tensorBasis ![c, c]).repr (S.formTensor c) μ = S.formMatrix c (μ 0) (μ 1) :=
  tensorBasis_repr_twoSlotEquiv _ _ _ μ

/-- A symmetric form is symmetric under the slot swap `σ` as a tensor, `g^μν = g^νμ`. -/
lemma formTensor_symm (c : Color K) [S.HasForm c.kind] [S.IsSymmetricForm c.kind]
    {σ : ColorEquiv ![c, c] ![c, c]} (hσ : σ.toEquiv = Equiv.swap 0 1) :
    S.formTensor c = S.reindex σ (S.formTensor c) := by
  rw [formTensor, reindex_twoSlotEquiv hσ, form_symm]

/-- An antisymmetric form is antisymmetric under the slot swap `σ` as a tensor,
`g^μν = -g^νμ`. -/
lemma formTensor_antisymm (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind]
    {σ : ColorEquiv ![c, c] ![c, c]} (hσ : σ.toEquiv = Equiv.swap 0 1) :
    S.formTensor c = S.reindex σ (-S.formTensor c) := by
  rw [formTensor, ← map_neg, reindex_twoSlotEquiv hσ, map_neg, form_antisymm, neg_neg]

/-- Lowering or raising at the slot `i` is contracting that slot with the first index of the form,
`T^…_ν… = T^…μ… g_μν`. -/
lemma toDualAt_eq_contr {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) (t : S.Tensor c) :
    S.toDualAt i a ha hi h t = Tensor.contr (ColorEquiv.matMulAt i a a.dual ha hi h)
      (S.tmulEquiv c ![a.dual, a.dual] (t ⊗ₜ S.formTensor a.dual)) := by
  induction t using inductionOn_pure with
  | hsmul r t ht => rw [map_smul, ht, ← smul_tmul', map_smul, map_smul]
  | hadd t t' ht ht' => rw [map_add, ht, ht', add_tmul, map_add, map_add]
  | h p =>
    let q : Π x, S.V (c' x) := fun x => if hx : x = i then 0 else S.cast (h x hx) (p x)
    rw [toDualAt_pure i a ha hi h p (Function.update q i _) (Function.update_self _ _ _)
      (fun x hx => by simp [q, hx]), toDual_apply, formTensor,
      Tensor.contr_matMulAt_pure i a a.dual ha hi h _ p q (fun x hx => by simp [q, hx])]

/-- Lowering the second index is contracting it with the form, `M^μν g_νρ = M^μ_ρ` at an upper
color `c`, along `ColorEquiv.matMul`. It is `toDualAt_eq_contr` for a tensor on two slots, in the
form of a product of matrices. -/
lemma toDualAt_eq_contr_formTensor (a c : Color K) [S.HasForm c.kind] (M : S.V a ⊗[k] S.V c) :
    S.toDualAt (c := ![a, c]) (c' := ![a, c.dual]) 1 c rfl rfl
      (fun x hx => by fin_cases x <;> simp_all) (S.twoSlotEquiv a c M) =
      Tensor.contr (ColorEquiv.matMul a c c.dual)
        (S.tmulEquiv _ _ (S.twoSlotEquiv a c M ⊗ₜ S.formTensor c.dual)) := by
  rw [toDualAt_twoSlotEquiv, formTensor, Tensor.contr_matMul]
  rfl

end Species

end Tensors
