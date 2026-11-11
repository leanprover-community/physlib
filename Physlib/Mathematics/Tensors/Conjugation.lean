/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.ForMathlib.SemilinearMaps
public import Physlib.Mathematics.Tensors.Contraction
/-!

# Conjugation of tensors

The conjugate of a tensor conjugates its components and moves each index to the conjugate color.

## i. Overview

Conjugation conjugates the components of a tensor and moves each index to the conjugate kind,
keeping its variance. A left-handed spinor `ψ_α` becomes a right-handed spinor `ψ̄_α̇`, and a
vector index is its own conjugate.

The kinds of a species carry Mathlib's `InvolutiveStar`, whose `star` gives the conjugate kind, and
the conjugate color is `c.bar = ⟨star c.kind, c.variance⟩`. The species gives the conjugation maps
`S.conjEquiv h : V c ≃ V c'` as data (`Species.HasConjugation`), with the target color given by an
equation `h : c' = c.bar` that holds by `rfl` at concrete colors. Conjugating twice gives back the
vector and conjugation preserves the contraction. Commuting with the group action is the separate
property `Species.IsEquivariantConjugation`.

Most species conjugate componentwise, `(v̄)^μ = (v^μ)*`, and get their conjugation from
`Species.HasConjugation.ofBasis` and a map `ConjLabels` from the labels of each kind to those of
its conjugate. The conjugate `Tensor.conj h T` of a tensor conjugates every index.

## ii. Key results

- `Color.bar` is the conjugate color, with `Color.bar_bar`.
- `Species.HasConjugation` gives the conjugation of a species with its two conditions, and
  `Species.conjEquiv` is the conjugate of a vector, with its properties
  `Species.conjEquiv_conjEquiv`, `Species.star_contr_conjEquiv` and `Species.conjEquiv_rep`.
- `Species.IsEquivariantConjugation` says that the conjugation commutes with the group action, and
  `Species.rep_dual_of_star_contr` that equivariance at a color gives it at the dual color.
- `Species.HasConjugation.ofBasis` builds a componentwise conjugation from `ConjLabels`, and
  `Species.HasConjugation.isEquivariantConjugation_ofBasis` gives its equivariance from the
  matrices of the group.
- `Tensor.conj` is the conjugate of a tensor, with `Tensor.conj_conj`,
  `Tensor.conj_smul` and `Tensor.conj_contr`.
- `Tensor.tensorBasis_repr_conj_of_basis` proves that the components of the conjugate are
  the conjugates of the components.

## iii. Table of contents

- A. Conjugate colors
- B. Species with a conjugation
- C. Componentwise conjugation
- D. Conjugation of tensors
  - D.1. The group action and contraction
  - D.2. Components

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensor

/-!

## A. Conjugate colors

-/

variable {K : Type} [InvolutiveStar K]

/-- The conjugate color, with the conjugate kind `star κ` and the same variance, as in
`ψ_α ↦ ψ̄_α̇`. -/
abbrev Color.bar (c : Color K) : Color K := ⟨star c.kind, c.variance⟩

/-- Conjugating twice gives back the color. -/
lemma Color.bar_bar (c : Color K) : c.bar.bar = c := by
  simp [Color.bar]

/-- If `b` is the conjugate of `a`, then `a.dual` is the conjugate of `b.dual`. This is the color
equation of the inverse of a form in `V a ⊗ V b`. -/
lemma Color.dual_eq_bar_dual {a b : Color K} (hb : b = a.bar) : a.dual = b.dual.bar := by
  subst hb
  simp [Color.bar]

/-- The pairs `σ` of `T`, as pairs of its conjugate `T̄`, with the same bijection of indices. -/
def ColorEquiv.barContr {ι κ J : Type} {c : ι → Color K} {b : κ → Color K} {a : J → Color K}
    (σ : ColorEquiv c (contrColors b a)) :
    ColorEquiv (fun i => (c i).bar) (contrColors (fun x => (b x).bar) fun j => (a j).bar) :=
  ⟨σ.toEquiv, fun j => by rcases j with _ | _ | _ <;> exact congrArg Color.bar (σ.color_eq _)⟩

/-!

## B. Species with a conjugation

-/

/-- A map reading the labels of a kind `κ` as labels of its conjugate kind `κ'`, given with an
equation `h : κ' = star κ`, that gives back the label when applied twice. -/
structure ConjLabels (basisIdx : K → Type) where
  /-- The labels of `κ` read as labels of its conjugate `κ'`. -/
  equiv {κ κ' : K} (h : κ' = star κ) : basisIdx κ ≃ basisIdx κ'
  /-- Reading a label as a label of the conjugate kind and back gives the label. -/
  equiv_equiv {κ κ' : K} (h : κ' = star κ) (h' : κ = star κ') (μ : basisIdx κ) :
    equiv h' (equiv h μ) = μ

variable {k : Type} [RCLike k] {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]
    {S : Species k G K basisIdx} {c c' : Color K}

namespace Species

variable (S) in
/-- A conjugation of the species, a conjugate-linear equivalence `v ↦ v̄` from each color `c` to
its conjugate `c'`, given with an equation `h : c' = c.bar` so that none of its conditions moves a
vector along `c.bar.bar = c`. -/
class HasConjugation where
  /-- The conjugate of a vector of color `c`, a vector of the conjugate color `c'`. -/
  conj {c c' : Color K} (h : c' = c.bar) : S.V c ≃ₗ⋆[k] S.V c'
  /-- Conjugating twice gives back the vector, `v̄̄ = v`. -/
  conj_conj {c c' : Color K} (h : c' = c.bar) (h' : c = c'.bar) (v : S.V c) :
    conj h' (conj h v) = v
  /-- Conjugation preserves the contraction, `(u^μ α_μ)* = ū^μ ᾱ_μ`. -/
  star_contr_conj {c c' : Color K} (h : c' = c.bar) (u : S.V c) (α : S.V c.dual) :
    star (S.contr c (u ⊗ₜ[k] α)) = S.contr c' (conj h u ⊗ₜ[k] conj (congrArg Color.dual h) α)

variable (S) in
/-- The conjugation commutes with the group action, `(Λv)‾ = Λ v̄`, so the representation at
`c.bar` is the conjugate of the one at `c`. -/
class IsEquivariantConjugation [S.HasConjugation] : Prop where
  /-- Conjugation commutes with the group action, `(Λv)‾ = Λ v̄`. -/
  conj_rep {c c' : Color K} (h : c' = c.bar) (g : G) (v : S.V c) :
    HasConjugation.conj h (S.rep c g v) = S.rep c' g (HasConjugation.conj h v)

section

variable [S.HasConjugation]

variable (S) in
/-- The conjugate `v̄` of a vector `v` of color `c`, a vector of color `c'`, the conjugate of `c`
by `h`, which holds by `rfl` at concrete colors. It is conjugate-linear. -/
def conjEquiv (h : c' = c.bar) : S.V c ≃ₗ⋆[k] S.V c' :=
  HasConjugation.conj h

/-- Conjugating twice gives back the vector, `v̄̄ = v`. -/
@[simp]
lemma conjEquiv_conjEquiv (h : c' = c.bar) (h' : c = c'.bar) (v : S.V c) :
    S.conjEquiv h' (S.conjEquiv h v) = v :=
  HasConjugation.conj_conj h h' v

/-- Conjugation preserves the contraction, `(u^μ α_μ)* = ū^μ ᾱ_μ`, for `u` of color `c` and `α` of
color `c.dual`. -/
lemma star_contr_conjEquiv (h : c' = c.bar) (u : S.V c) (α : S.V c.dual) :
    star (S.contr c (u ⊗ₜ[k] α)) =
      S.contr c' (S.conjEquiv h u ⊗ₜ[k] S.conjEquiv (congrArg Color.dual h) α) :=
  HasConjugation.star_contr_conj h u α

/-- Conjugation commutes with the group action, `(Λv)‾ = Λ v̄`. -/
lemma conjEquiv_rep [S.IsEquivariantConjugation] (h : c' = c.bar) (g : G) (v : S.V c) :
    S.conjEquiv h (S.rep c g v) = S.rep c' g (S.conjEquiv h v) :=
  IsEquivariantConjugation.conj_rep h g v

/-- Moving the conjugate along an equality of colors conjugates to the new color. -/
lemma cast_conjEquiv {c'' : Color K} (q : c' = c'') (h : c' = c.bar) (x : S.V c) :
    S.cast q (S.conjEquiv h x) = S.conjEquiv (q.symm.trans h) x := by
  subst q
  rfl

/-- Conjugating a vector moved along an equality of colors conjugates the vector. -/
lemma conjEquiv_cast {b b' : Color K} (p : b = b') (h : c' = b'.bar) (x : S.V b) :
    S.conjEquiv h (S.cast p x) = S.conjEquiv (h.trans (congrArg Color.bar p.symm)) x := by
  subst p
  rfl

end

omit [InvolutiveStar K] in
/-- If conjugate-linear maps `f` at `c` and `f'` at `c.dual` preserve the contraction and `f`
commutes with the group action, then so does `f'`. Equivariance at a dual color follows from
equivariance at the color. -/
lemma rep_dual_of_star_contr (f : S.V c ≃ₗ⋆[k] S.V c') (f' : S.V c.dual ≃ₗ⋆[k] S.V c'.dual)
    (hf' : ∀ u α, star (S.contr c (u ⊗ₜ α)) = S.contr c' (f u ⊗ₜ f' α))
    (hf : ∀ g v, f (S.rep c g v) = S.rep c' g (f v)) (g : G) (α : S.V c.dual) :
    f' (S.rep c.dual g α) = S.rep c'.dual g (f' α) :=
  ext_contr fun u' => by
    obtain ⟨u, rfl⟩ := f.surjective u'
    rw [← hf', contr_tmul_rep, contr_tmul_rep, ← hf, hf']

/-!

## C. Componentwise conjugation

-/

variable (S) in
/-- The componentwise conjugation, `(v̄)^{e μ} = (v^μ)*`, which sends the basis vector `e_μ` of
`c` to the basis vector `e_{e μ}` of the conjugate color, with the labels read by `e`. -/
@[instance_reducible]
noncomputable def HasConjugation.ofBasis (e : ConjLabels basisIdx) :
    S.HasConjugation where
  conj h := (S.basis _).starEquiv (S.basis _) (e.equiv (congrArg Color.kind h))
  conj_conj _ _ v := Module.Basis.starEquiv_starEquiv _ _ _ _ (e.equiv_equiv _ _) v
  star_contr_conj _ u α := Module.Basis.star_coordPairing_starEquiv _ _ _ _ _ u α

/-- The componentwise conjugation commutes with the group action when the matrix of each `g : G`
at `c.bar` is the conjugate of its matrix at `c`, `(Λ̄)^μ_ν = (Λ^μ_ν)*`. The hypothesis is needed at
the upper colors only, since it follows at the lower ones (`rep_dual_of_star_contr`). -/
lemma HasConjugation.isEquivariantConjugation_ofBasis (e : ConjLabels basisIdx)
    (rep_basis : ∀ (κ : K) (g : G) (μ ν : basisIdx κ),
      (S.basis ⟨star κ, .up⟩).repr
          (S.rep ⟨star κ, .up⟩ g (S.basis ⟨star κ, .up⟩ (e.equiv rfl μ))) (e.equiv rfl ν) =
        star ((S.basis ⟨κ, .up⟩).repr (S.rep ⟨κ, .up⟩ g (S.basis ⟨κ, .up⟩ μ)) ν)) :
    letI := ofBasis S e
    S.IsEquivariantConjugation := by
  let := ofBasis S e
  refine ⟨fun {c _} h g v => ?_⟩
  subst h
  obtain ⟨κ, ⟨_ | _, _ | _, hv⟩⟩ := c <;> try exact absurd rfl hv
  · -- A lower color is the dual of `⟨κ, up⟩`, where `rep_basis` gives equivariance.
    exact rep_dual_of_star_contr (c := ⟨κ, .up⟩) (c' := ⟨star κ, .up⟩) _ _
      (fun u α => Module.Basis.star_coordPairing_starEquiv _ _ _ _ _ u α)
      (fun g => Module.Basis.starEquiv_map_of_repr _ _ _ _ _ (rep_basis κ g)) g v
  · exact Module.Basis.starEquiv_map_of_repr _ _ _ _ _ (rep_basis κ g) v

/-- The componentwise conjugate of the basis vector `e_μ` is the basis vector `e_{e μ}`. -/
lemma HasConjugation.ofBasis_conjEquiv_basis (e : ConjLabels basisIdx)
    (h : c' = c.bar) (μ : basisIdx c.kind) :
    letI := ofBasis S e
    S.conjEquiv h (S.basis c μ) = S.basis c' (e.equiv (congrArg Color.kind h) μ) :=
  Module.Basis.starEquiv_apply_self _ _ _ μ

/-- The components of the conjugate are the conjugates of the components,
`(v̄)^μ = (v^{e⁻¹ μ})*`, when conjugation sends each basis vector `e_μ` of `c` to the basis vector
`e_{e μ}` of `c'`. -/
lemma basis_repr_conjEquiv_of_basis [S.HasConjugation] (h : c' = c.bar)
    (e : basisIdx c.kind ≃ basisIdx c'.kind)
    (he : ∀ μ, S.conjEquiv h (S.basis c μ) = S.basis c' (e μ)) (v : S.V c)
    (μ : basisIdx c'.kind) :
    (S.basis c').repr (S.conjEquiv h v) μ = star ((S.basis c).repr v (e.symm μ)) := by
  rw [Module.Basis.eq_starEquiv _ _ e (S.conjEquiv h) he v, Module.Basis.repr_starEquiv]

/-!

## D. Conjugation of tensors

-/

end Species

open Species

variable [S.HasConjugation] {ι : Type} {c c' : ι → Color K}

/-- The conjugate `T̄` of a tensor `T`, with every index conjugated and moved to the conjugate
color. The colors `c'` of the result are the conjugates of `c` by `h`. For concrete colors `h` holds
by `rfl` index by index, `fun i => by fin_cases i <;> rfl`. It is conjugate-linear. -/
noncomputable def conj (h : ∀ i, c' i = (c i).bar) : Tensor S c ≃ₗ⋆[k] Tensor S c' :=
  (S.toPiTensor c).trans <| (PiTensorProduct.congrₛₗ fun i => S.conjEquiv (h i)).trans
    (S.toPiTensor c').symm

/-- The conjugate of a pure tensor conjugates each factor, `(u ⊗ α)‾ = ū ⊗ ᾱ`. -/
@[simp]
lemma conj_pure (h : ∀ i, c' i = (c i).bar) (f : Π i, S.V (c i)) :
    conj h (S.pure f) = S.pure fun i => S.conjEquiv (h i) (f i) :=
  congrₛₗ_tprod _ f

/-- Conjugating twice gives back the tensor. -/
lemma conj_conj (h : ∀ i, c' i = (c i).bar) (h' : ∀ i, c i = (c' i).bar) (t : Tensor S c) :
    conj h' (conj h t) = t := by
  induction t using inductionOn_pure with
  | h f => simp
  | hsmul r t ht => rw [LinearEquiv.map_smulₛₗ, LinearEquiv.map_smulₛₗ, ht, starRingEnd_self_apply]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-!

### D.1. The group action and contraction

-/

/-- Conjugation commutes with the action `Λ` of `g : G`, `(ΛT)‾ = Λ T̄`. -/
lemma conj_smul [S.IsEquivariantConjugation] (h : ∀ i, c' i = (c i).bar) (g : G)
    (t : Tensor S c) :
    conj h (g • t) = g • conj h t :=
  map_smul_of_pure (conj h) g (fun f => by simp [conjEquiv_rep]) t

variable {κ J : Type} [Fintype J] {b : κ → Color K} {a : J → Color K}

/-- Conjugating a contraction is contracting the conjugate along the same pairs of indices,
`(T^ρμ_μ)‾ = T̄^ρμ_μ`. -/
lemma conj_contr (σ : ColorEquiv c (contrColors b a)) (t : Tensor S c) :
    conj (fun _ => rfl) (contr σ t) = contr σ.barContr (conj (fun _ => rfl) t) := by
  induction t using inductionOn_pure with
  | hsmul r t ht => rw [map_smul, LinearEquiv.map_smulₛₗ, ht, LinearEquiv.map_smulₛₗ, map_smul]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | h f =>
    simp only [contr_pure, conj_pure, LinearEquiv.map_smulₛₗ, starRingEnd_apply, star_prod,
      star_contr_conjEquiv rfl, conjEquiv_cast, cast_conjEquiv]
    rfl

/-!

### D.2. Components

-/

/-- The components of the conjugate are the conjugates of the components,
`(T̄)^μν = (T^{e⁻¹ μ, e⁻¹ ν})*`, when conjugation sends each basis vector `e_μ` at the index `i` to
the basis vector `e_{e i μ}`. -/
lemma tensorBasis_repr_conj_of_basis [Fintype ι] (h : ∀ i, c' i = (c i).bar)
    (e : ∀ i, basisIdx (c i).kind ≃ basisIdx (c' i).kind)
    (he : ∀ i μ, S.conjEquiv (h i) (S.basis (c i) μ) = S.basis (c' i) (e i μ)) (t : Tensor S c)
    (μ : Π i, basisIdx (c' i).kind) :
    (S.tensorBasis c').repr (conj h t) μ =
      star ((S.tensorBasis c).repr t fun i => (e i).symm (μ i)) := by
  rw [Module.Basis.eq_starEquiv (S.tensorBasis c) (S.tensorBasis c') (Equiv.piCongrRight e)
    (conj h) (fun ν => by simp [tensorBasis_apply, he]) t, Module.Basis.repr_starEquiv]
  rfl

end Tensor
