/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.LocalCovFieldAlgebra.Generators
/-!
# The mass-weight grading of the covariant field algebra

The grading of the covariant field algebra by mass weight, its components and its filtration.

## i. Overview

The mass weight of a covariant expression is twice its mass dimension. It is recorded by an
algebra map `P` from the covariant field algebra to the polynomials over it, the element `b`
of weight `w` going to `b X ^ w`. The statement `IsMassWeightPoly P` says that `P` gives every
covariant generator its mass weight: `4 + 2 |l|` for the field-strength tower `∇_l F_μν`, and
`c + 2 n` for the tower of `n` covariant derivatives of a species of mass weight `c`.

The weight-`n` piece `massWeightSubmodule P n` is the set of elements `x` with `P x = x X ^ n`.
Products add weights. Under `IsMassWeightPoly P` the weight-`n` piece is spanned by the products
of generators of total weight `n`. The weight-`k` component `massWeightComponent P k x` of an
element is the coefficient of `X ^ k` in `P x`. It lies in the weight-`k` piece, and every element
is the sum of its components.

The gauge and Lorentz groups carry each generator into a combination of generators of the same
weight, so they preserve every weight piece and commute with taking components. The components
of an invariant element are therefore invariant. The filtration `massWeightSubmoduleLE P w` is the
join of the pieces of weight at most `w`, and an element of it is the sum of its components of
weight at most `w`.

When every species has positive mass weight, the weight-zero piece is the constants. When the
fermionic species have odd mass weight and the bosonic species even mass weight, elements of
weights `v` and `w` exchange up to the sign `(-1) ^ (v * w)`.

## ii. Key results

- `GaugeFieldData.LocalCovFieldAlgebra.IsMassWeightPoly` : `P` gives every generator its mass
  weight, with the constructor `isMassWeightPoly_of` from the towers.
- `GaugeFieldData.LocalCovFieldAlgebra.massWeightSubmodule`,
  `GaugeFieldData.LocalCovFieldAlgebra.massWeightSubmoduleLE` : the weight pieces and the
  filtration.
- `GaugeFieldData.LocalCovFieldAlgebra.massWeightComponent` : the projection onto a weight.
- `GaugeFieldData.LocalCovFieldAlgebra.massWeightSubmodule_eq_span` : the weight-`n` piece is
  spanned by the products of generators of weight `n`.
- `GaugeFieldData.LocalCovFieldAlgebra.massWeightComponent_mem_invariants_repValue` and its
  Lorentz companion : the components of an invariant are invariant.
- `GaugeFieldData.LocalCovFieldAlgebra.sum_massWeightComponent_of_mem_massWeightSubmoduleLE` :
  an element of the filtration is the sum of its low-weight components.
- `GaugeFieldData.LocalCovFieldAlgebra.massWeightSubmodule_zero` : the weight-zero piece is the
  constants.
- `GaugeFieldData.LocalCovFieldAlgebra.mul_eq_smul_mul_of_mem_massWeightSubmodule` : elements of
  given weights supercommute.

## iii. Table of contents

- A. Mass-weight polynomials
- B. The weight pieces
  - B.1. Products of generators are homogeneous
- C. The weight components
  - C.1. The weight pieces as spans of products
- D. Stability under the gauge and Lorentz groups
  - D.1. The components of invariants
- E. The mass-weight filtration
- F. The weight-zero piece
- G. Supercommutativity of homogeneous elements

## iv. References

* None.

-/

@[expose] public section

open MatrixGroups

namespace GaugeFieldData

namespace LocalCovFieldAlgebra

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} {T : GaugeFieldData G}
  (P : T.LocalCovFieldAlgebra →ₐ[ℂ] Polynomial T.LocalCovFieldAlgebra)

/-!

## A. Mass-weight polynomials

-/

/-- An algebra map `P` from the covariant field algebra to the polynomials over it is a
  mass-weight polynomial when every covariant generator of mass weight `w` is homogeneous of
  weight `w`, `P b = b X ^ w`. -/
def IsMassWeightPoly : Prop :=
  ∀ k w, ∀ b ∈ T.weightedGenerators k w, P b = Polynomial.monomial w b

/-- `P` is a mass-weight polynomial when the field-strength tower `∇_l F_μν` has weight
  `4 + 2 |l|` and the towers of `n` covariant derivatives of a species of mass weight `c`, and of
  its conjugate, have weight `c + 2 n`. -/
lemma isMassWeightPoly_of
    (hF : ∀ (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra),
      P (covFieldStrength T l μ ν φ)
        = Polynomial.monomial (4 + 2 * l.length) (covFieldStrength T l μ ν φ))
    (hψ : ∀ (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (T.FermionValue i)),
      P (covFermion T i l φ)
        = Polynomial.monomial ((T.fermion i).massWeight + 2 * n) (covFermion T i l φ))
    (hψc : ∀ (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))),
      P (covConjFermion T i l φ)
        = Polynomial.monomial ((T.fermion i).massWeight + 2 * n) (covConjFermion T i l φ))
    (hφ : ∀ (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (T.BosonValue j)),
      P (covBoson T j l φ)
        = Polynomial.monomial ((T.boson j).massWeight + 2 * n) (covBoson T j l φ))
    (hφc : ∀ (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))),
      P (covConjBoson T j l φ)
        = Polynomial.monomial ((T.boson j).massWeight + 2 * n) (covConjBoson T j l φ)) :
    IsMassWeightPoly P := by
  intro k w b hb
  cases k with
  | gauge =>
    simp only [weightedGenerators, Set.mem_iUnion, Set.mem_range] at hb
    obtain ⟨l, rfl, μ, ν, φ, rfl⟩ := hb
    exact hF l μ ν φ
  | scalar =>
    simp only [weightedGenerators, Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
    obtain ⟨j, n, rfl, l, ⟨φ, rfl⟩ | ⟨φ, rfl⟩⟩ := hb
    · exact hφ j l φ
    · exact hφc j l φ
  | fermion =>
    simp only [weightedGenerators, Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
    obtain ⟨i, n, rfl, l, ⟨φ, rfl⟩ | ⟨φ, rfl⟩⟩ := hb
    · exact hψ i l φ
    · exact hψc i l φ

/-!

## B. The weight pieces

-/

/-- The weight-`n` piece of the covariant field algebra, the elements `x` with
  `P x = x X ^ n`. -/
noncomputable def massWeightSubmodule (n : ℕ) : Submodule ℂ T.LocalCovFieldAlgebra :=
  LinearMap.ker (P.toLinearMap - (Polynomial.monomial n :
    T.LocalCovFieldAlgebra →ₗ[T.LocalCovFieldAlgebra]
      Polynomial T.LocalCovFieldAlgebra).restrictScalars ℂ)

variable {P}

lemma mem_massWeightSubmodule_iff {n : ℕ} {x : T.LocalCovFieldAlgebra} :
    x ∈ massWeightSubmodule P n ↔ P x = Polynomial.monomial n x := by
  simp only [massWeightSubmodule, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, sub_eq_zero]

/-- The weight pieces are multiplicative, since weights add under multiplication. -/
lemma mul_mem_massWeightSubmodule {v w : ℕ} {x y : T.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule P v) (hy : y ∈ massWeightSubmodule P w) :
    x * y ∈ massWeightSubmodule P (v + w) := by
  rw [mem_massWeightSubmodule_iff] at hx hy ⊢
  rw [map_mul, hx, hy, Polynomial.monomial_mul_monomial]

variable (P) in
/-- The unit has weight zero. -/
lemma one_mem_massWeightSubmodule_zero :
    (1 : T.LocalCovFieldAlgebra) ∈ massWeightSubmodule P 0 := by
  rw [mem_massWeightSubmodule_iff, map_one, Polynomial.monomial_zero_one]

/-!

### B.1. Products of generators are homogeneous

-/

/-- Under `IsMassWeightPoly P`, a generator of mass weight `w` lies in the weight-`w` piece. -/
lemma mem_massWeightSubmodule_of_mem_weightedGenerators (hP : IsMassWeightPoly P) {k : FieldKind}
    {w : ℕ} {b : T.LocalCovFieldAlgebra} (hb : b ∈ T.weightedGenerators k w) :
    b ∈ massWeightSubmodule P w :=
  mem_massWeightSubmodule_iff.2 (hP k w b hb)

/-- Under `IsMassWeightPoly P`, a product of generators of total mass weight `w` lies in the
  weight-`w` piece. -/
lemma mem_massWeightSubmodule_of_mem_weightedMonomials (hP : IsMassWeightPoly P)
    {A : Finset FieldKind} {w : ℕ} {x : T.LocalCovFieldAlgebra}
    (hx : x ∈ T.weightedMonomials A w) : x ∈ massWeightSubmodule P w := by
  obtain ⟨L, hL, -, rfl, rfl⟩ := hx
  induction L with
  | nil => simpa using one_mem_massWeightSubmodule_zero P
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact mul_mem_massWeightSubmodule
      (mem_massWeightSubmodule_of_mem_weightedGenerators hP (hL p (List.mem_cons.2 (Or.inl rfl))))
      (ih fun q hq => hL q (List.mem_cons.2 (Or.inr hq)))

/-- Under `IsMassWeightPoly P`, the combinations of products of generators of weight `w` lie in
  the weight-`w` piece. -/
lemma span_weightedMonomials_le_massWeightSubmodule (hP : IsMassWeightPoly P) (w : ℕ) :
    Submodule.span ℂ (⋃ A, T.weightedMonomials A w) ≤ massWeightSubmodule P w :=
  Submodule.span_le.2 (Set.iUnion_subset fun _ _ hx =>
    mem_massWeightSubmodule_of_mem_weightedMonomials hP hx)

/-!

## C. The weight components

-/

variable (P) in
/-- The weight-`k` component of an element of the covariant field algebra, the coefficient of
  `X ^ k` in its image under `P`. -/
noncomputable def massWeightComponent (k : ℕ) :
    T.LocalCovFieldAlgebra →ₗ[ℂ] T.LocalCovFieldAlgebra where
  toFun x := (P x).coeff k
  -- `P.toRingHom.map_add` and `P.toLinearMap.map_smul` instead of the generic `map_add` and
  -- `map_smul`: instance search for `AddHomClass` on `P` times out
  map_add' x y := by
    show (P.toRingHom (x + y)).coeff k = _
    rw [RingHom.map_add, Polynomial.coeff_add]
    rfl
  map_smul' c x := by
    show (P.toLinearMap (c • x)).coeff k = _
    rw [LinearMap.map_smul, AddMonoidAlgebra.coeff_smul_apply, RingHom.id_apply]
    rfl

@[simp]
lemma massWeightComponent_apply (k : ℕ) (x : T.LocalCovFieldAlgebra) :
    massWeightComponent P k x = (P x).coeff k := rfl

/-- The weight-`k` component of an element of the weight-`w` piece is the element itself when
  `w = k`, and zero otherwise. -/
lemma massWeightComponent_of_mem {w : ℕ} {x : T.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule P w) (k : ℕ) :
    massWeightComponent P k x = if w = k then x else 0 := by
  rw [massWeightComponent_apply, mem_massWeightSubmodule_iff.1 hx, Polynomial.coeff_monomial_apply]

lemma massWeightComponent_self {w : ℕ} {x : T.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule P w) : massWeightComponent P w x = x := by
  rw [massWeightComponent_of_mem hx, ite_eq_left rfl]

/-- Under `IsMassWeightPoly P`, the weight-`k` component of any element is a combination of
  products of generators of weight `k`. On a product of generators the component is the product
  or zero, and both sides are linear. -/
lemma massWeightComponent_mem_span (hP : IsMassWeightPoly P) (k : ℕ)
    (x : T.LocalCovFieldAlgebra) :
    massWeightComponent P k x ∈ Submodule.span ℂ (⋃ A, T.weightedMonomials A k) := by
  have hx := mem_span_weightedMonomials x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨A, hy⟩ := Set.mem_iUnion.1 hy
    obtain ⟨w, hy⟩ := Set.mem_iUnion.1 hy
    rw [massWeightComponent_of_mem (mem_massWeightSubmodule_of_mem_weightedMonomials hP hy)]
    split_ifs with h
    · subst h
      exact Submodule.subset_span (Set.mem_iUnion.2 ⟨A, hy⟩)
    · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

/-- Under `IsMassWeightPoly P`, the weight-`k` component lies in the weight-`k` piece. -/
lemma massWeightComponent_mem_massWeightSubmodule (hP : IsMassWeightPoly P) (k : ℕ)
    (x : T.LocalCovFieldAlgebra) : massWeightComponent P k x ∈ massWeightSubmodule P k :=
  span_weightedMonomials_le_massWeightSubmodule hP k (massWeightComponent_mem_span hP k x)

/-- Under `IsMassWeightPoly P`, every element of the covariant field algebra is the sum of its
  weight components, the coefficients of its image under `P`. It holds on the products of
  generators, which are homogeneous, and both sides are linear. -/
lemma eq_sum_coeff (hP : IsMassWeightPoly P) (x : T.LocalCovFieldAlgebra) :
    x = (P x).sum fun _ a => a := by
  have hx := mem_span_weightedMonomials x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨A, hy⟩ := Set.mem_iUnion.1 hy
    obtain ⟨w, hy⟩ := Set.mem_iUnion.1 hy
    rw [mem_massWeightSubmodule_iff.1 (mem_massWeightSubmodule_of_mem_weightedMonomials hP hy),
      Polynomial.sum_monomial_index _ _ rfl]
  | zero => simp
  | add a b _ _ iha ihb =>
    rw [show P (a + b) = P a + P b from P.toRingHom.map_add a b,
      Polynomial.sum_add_index _ _ _ (fun _ => rfl) (fun _ _ _ => rfl), ← iha, ← ihb]
  | smul c a _ iha =>
    rw [Polynomial.sum_def] at iha
    rw [show P (c • a) = c • P a from P.toLinearMap.map_smul c a,
      Polynomial.sum_smul_index' (P a) c (fun _ a => a) (fun _ => rfl), Polynomial.sum_def,
      ← Finset.smul_sum, ← iha]

/-!

### C.1. The weight pieces as spans of products

-/

/-- Under `IsMassWeightPoly P`, the weight-`w` piece is exactly the span of the products of
  generators of total weight `w`. -/
lemma massWeightSubmodule_eq_span (hP : IsMassWeightPoly P) (w : ℕ) :
    massWeightSubmodule P w = Submodule.span ℂ (⋃ A, T.weightedMonomials A w) := by
  refine le_antisymm (fun x hx => ?_) (span_weightedMonomials_le_massWeightSubmodule hP w)
  rw [← massWeightComponent_self hx]
  exact massWeightComponent_mem_span hP w x

/-- Under `IsMassWeightPoly P`, a linear map preserving every weight piece commutes with taking
  weight components. -/
lemma map_massWeightComponent (hP : IsMassWeightPoly P)
    {f : T.LocalCovFieldAlgebra →ₗ[ℂ] T.LocalCovFieldAlgebra}
    (hf : ∀ w y, y ∈ massWeightSubmodule P w → f y ∈ massWeightSubmodule P w) (k : ℕ)
    (x : T.LocalCovFieldAlgebra) :
    f (massWeightComponent P k x) = massWeightComponent P k (f x) := by
  have hx := mem_span_weightedMonomials x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨A, hy⟩ := Set.mem_iUnion.1 hy
    obtain ⟨w, hy⟩ := Set.mem_iUnion.1 hy
    have hy' := mem_massWeightSubmodule_of_mem_weightedMonomials hP hy
    rw [massWeightComponent_of_mem hy', massWeightComponent_of_mem (hf w y hy')]
    split_ifs
    · rfl
    · exact map_zero f
  | zero => simp only [map_zero]
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | smul c y _ hy => simp only [map_smul, hy]

/-!

## D. Stability under the gauge and Lorentz groups

-/

/-- A map preserving the span of the products of every given kinds and weight preserves every
  weight piece. -/
lemma map_mem_massWeightSubmodule (hP : IsMassWeightPoly P)
    {f : T.LocalCovFieldAlgebra →ₗ[ℂ] T.LocalCovFieldAlgebra}
    (hf : ∀ (A : Finset FieldKind) (w : ℕ) (x : T.LocalCovFieldAlgebra),
      x ∈ Submodule.span ℂ (T.weightedMonomials A w) →
        f x ∈ Submodule.span ℂ (T.weightedMonomials A w))
    {w : ℕ} {x : T.LocalCovFieldAlgebra} (hx : x ∈ massWeightSubmodule P w) :
    f x ∈ massWeightSubmodule P w := by
  rw [massWeightSubmodule_eq_span hP] at hx ⊢
  refine (Submodule.span_le (p := (Submodule.span ℂ (⋃ A, T.weightedMonomials A w)).comap f)).2
    (fun y hy => ?_) hx
  obtain ⟨A, hy⟩ := Set.mem_iUnion.1 hy
  exact Submodule.span_mono (Set.subset_iUnion (fun A => T.weightedMonomials A w) A)
    (hf A w y (Submodule.subset_span hy))

/-- The jet gauge group preserves every weight piece. -/
lemma repJet_mem_massWeightSubmodule (hP : IsMassWeightPoly P) (U : G.gaugeJetGroup) {w : ℕ}
    {x : T.LocalCovFieldAlgebra} (hx : x ∈ massWeightSubmodule P w) :
    repJet T U x ∈ massWeightSubmodule P w :=
  map_mem_massWeightSubmodule hP (fun _ _ _ h => repJet_mem_span_weightedMonomials U h) hx

/-- The ordinary gauge group preserves every weight piece. -/
lemma repValue_mem_massWeightSubmodule (hP : IsMassWeightPoly P) (g : G.group) {w : ℕ}
    {x : T.LocalCovFieldAlgebra} (hx : x ∈ massWeightSubmodule P w) :
    repValue T g x ∈ massWeightSubmodule P w :=
  repJet_mem_massWeightSubmodule hP (G.gaugeJetOfConstant g) hx

/-- The Lorentz group preserves every weight piece. -/
lemma repLorentzGroup_mem_massWeightSubmodule (hP : IsMassWeightPoly P)
    (hGL : T.GaugeLorentzCompatible) (Λ : SL(2,ℂ)) {w : ℕ} {x : T.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule P w) : repLorentzGroup T hGL Λ x ∈ massWeightSubmodule P w :=
  map_mem_massWeightSubmodule hP
    (fun _ _ _ h => repLorentzGroup_mem_span_weightedMonomials hGL Λ h) hx

/-- Taking a weight component commutes with the ordinary gauge group. -/
lemma massWeightComponent_repValue (hP : IsMassWeightPoly P) (g : G.group) (k : ℕ)
    (x : T.LocalCovFieldAlgebra) :
    massWeightComponent P k (repValue T g x) = repValue T g (massWeightComponent P k x) :=
  (map_massWeightComponent hP (fun _ _ hy => repValue_mem_massWeightSubmodule hP g hy) k x).symm

/-- Taking a weight component commutes with the Lorentz group. -/
lemma massWeightComponent_repLorentzGroup (hP : IsMassWeightPoly P)
    (hGL : T.GaugeLorentzCompatible) (Λ : SL(2,ℂ)) (k : ℕ) (x : T.LocalCovFieldAlgebra) :
    massWeightComponent P k (repLorentzGroup T hGL Λ x)
      = repLorentzGroup T hGL Λ (massWeightComponent P k x) :=
  (map_massWeightComponent hP
    (fun _ _ hy => repLorentzGroup_mem_massWeightSubmodule hP hGL Λ hy) k x).symm

/-!

### D.1. The components of invariants

-/

/-- The weight components of a gauge invariant are gauge invariant. -/
lemma massWeightComponent_mem_invariants_repValue (hP : IsMassWeightPoly P) (k : ℕ)
    {x : T.LocalCovFieldAlgebra} (hx : x ∈ Representation.invariants (repValue T)) :
    massWeightComponent P k x ∈ Representation.invariants (repValue T) := by
  rw [Representation.mem_invariants] at hx ⊢
  intro g
  rw [← massWeightComponent_repValue hP, hx g]

/-- The weight components of a Lorentz invariant are Lorentz invariant. -/
lemma massWeightComponent_mem_invariants_repLorentzGroup (hP : IsMassWeightPoly P)
    (hGL : T.GaugeLorentzCompatible) (k : ℕ) {x : T.LocalCovFieldAlgebra}
    (hx : x ∈ Representation.invariants (repLorentzGroup T hGL)) :
    massWeightComponent P k x ∈ Representation.invariants (repLorentzGroup T hGL) := by
  rw [Representation.mem_invariants] at hx ⊢
  intro Λ
  rw [← massWeightComponent_repLorentzGroup hP, hx Λ]

/-!

## E. The mass-weight filtration

-/

variable (P) in
/-- The mass-weight filtration, the join of the weight pieces of weight at most `w`. A
  Lagrangian of mass dimension at most `w / 2` lies in it. -/
noncomputable def massWeightSubmoduleLE (w : ℕ) : Submodule ℂ T.LocalCovFieldAlgebra :=
  ⨆ k ∈ Finset.range (w + 1), massWeightSubmodule P k

/-- Each weight piece of weight at most `w` sits inside the filtration at `w`. -/
lemma massWeightSubmodule_le_massWeightSubmoduleLE {k w : ℕ} (hk : k ≤ w) :
    massWeightSubmodule P k ≤ massWeightSubmoduleLE P w :=
  le_iSup₂_of_le k (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) le_rfl

lemma mem_massWeightSubmoduleLE {k w : ℕ} (hk : k ≤ w) {x : T.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule P k) : x ∈ massWeightSubmoduleLE P w :=
  massWeightSubmodule_le_massWeightSubmoduleLE hk hx

/-- A submodule containing every weight piece of weight at most `w` contains the filtration
  at `w`. -/
lemma massWeightSubmoduleLE_le {w : ℕ} {V : Submodule ℂ T.LocalCovFieldAlgebra}
    (hV : ∀ k ≤ w, massWeightSubmodule P k ≤ V) : massWeightSubmoduleLE P w ≤ V :=
  iSup₂_le fun k hk => hV k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

/-- The filtration as a join over a finite index type. -/
lemma massWeightSubmoduleLE_eq_iSup (w : ℕ) :
    massWeightSubmoduleLE P w = ⨆ k : Fin (w + 1), massWeightSubmodule P (k : ℕ) :=
  le_antisymm
    (massWeightSubmoduleLE_le fun k hk => le_iSup_of_le ⟨k, Nat.lt_succ_of_le hk⟩ le_rfl)
    (iSup_le fun k => massWeightSubmodule_le_massWeightSubmoduleLE (Nat.lt_succ_iff.1 k.isLt))

/-- Under `IsMassWeightPoly P`, the weight-`k` component of any element lies in the filtration
  at every `w ≥ k`. -/
lemma massWeightComponent_mem_massWeightSubmoduleLE (hP : IsMassWeightPoly P) {k w : ℕ}
    (hk : k ≤ w) (x : T.LocalCovFieldAlgebra) :
    massWeightComponent P k x ∈ massWeightSubmoduleLE P w :=
  mem_massWeightSubmoduleLE hk (massWeightComponent_mem_massWeightSubmodule hP k x)

/-- The filtration at `w` is fixed by the sum of the weight components of weight at most `w`. -/
lemma massWeightSubmoduleLE_le_eqLocus (w : ℕ) :
    massWeightSubmoduleLE P w ≤ LinearMap.eqLocus
      (∑ k ∈ Finset.range (w + 1), massWeightComponent P k) LinearMap.id :=
  massWeightSubmoduleLE_le fun k hk x hx => by
    rw [LinearMap.mem_eqLocus, LinearMap.sum_apply, LinearMap.id_apply]
    simp only [massWeightComponent_of_mem hx]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.2 (Nat.lt_succ_of_le hk))]

/-- An element of the filtration at `w` is the sum of its weight components of weight at
  most `w`. No hypothesis on `P` is needed, since each weight piece has a single component. -/
lemma sum_massWeightComponent_of_mem_massWeightSubmoduleLE {w : ℕ} {x : T.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmoduleLE P w) :
    ∑ k ∈ Finset.range (w + 1), massWeightComponent P k x = x := by
  have h := massWeightSubmoduleLE_le_eqLocus w hx
  rw [LinearMap.mem_eqLocus, LinearMap.sum_apply, LinearMap.id_apply] at h
  exact h

/-- A map preserving every weight piece preserves the filtration. -/
lemma map_mem_massWeightSubmoduleLE {f : T.LocalCovFieldAlgebra →ₗ[ℂ] T.LocalCovFieldAlgebra}
    (hf : ∀ k y, y ∈ massWeightSubmodule P k → f y ∈ massWeightSubmodule P k) {w : ℕ}
    {x : T.LocalCovFieldAlgebra} (hx : x ∈ massWeightSubmoduleLE P w) :
    f x ∈ massWeightSubmoduleLE P w :=
  (massWeightSubmoduleLE_le (V := (massWeightSubmoduleLE P w).comap f)
    fun k hk y hy => massWeightSubmodule_le_massWeightSubmoduleLE hk (hf k y hy)) hx

/-- The ordinary gauge group preserves the filtration. -/
lemma repValue_mem_massWeightSubmoduleLE (hP : IsMassWeightPoly P) (g : G.group) {w : ℕ}
    {x : T.LocalCovFieldAlgebra} (hx : x ∈ massWeightSubmoduleLE P w) :
    repValue T g x ∈ massWeightSubmoduleLE P w :=
  map_mem_massWeightSubmoduleLE (fun _ _ hy => repValue_mem_massWeightSubmodule hP g hy) hx

/-- The Lorentz group preserves the filtration. -/
lemma repLorentzGroup_mem_massWeightSubmoduleLE (hP : IsMassWeightPoly P)
    (hGL : T.GaugeLorentzCompatible) (Λ : SL(2,ℂ)) {w : ℕ} {x : T.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmoduleLE P w) : repLorentzGroup T hGL Λ x ∈ massWeightSubmoduleLE P w :=
  map_mem_massWeightSubmoduleLE
    (fun _ _ hy => repLorentzGroup_mem_massWeightSubmodule hP hGL Λ hy) hx

/-!

## F. The weight-zero piece

-/

/-- When every species has positive mass weight, the weight-zero piece is the constants. The
  only product of generators of weight zero is the empty one, whose value is the unit. This is
  the constant term of a Lagrangian, the cosmological term. -/
lemma massWeightSubmodule_zero (hP : IsMassWeightPoly P) (hpos : T.HasPositiveMassWeights) :
    massWeightSubmodule P 0 = 1 := by
  rw [massWeightSubmodule_eq_span hP, Submodule.one_eq_span]
  congr 1
  ext x
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  constructor
  · rintro ⟨A, hx⟩
    exact eq_one_of_mem_weightedMonomials_zero hpos hx
  · rintro rfl
    exact ⟨∅, one_mem_weightedMonomials T⟩

/-!

## G. Supercommutativity of homogeneous elements

-/

/-- When the fermionic species have odd mass weight and the bosonic species even mass weight,
  elements of weights `v` and `w` exchange up to the sign `(-1) ^ (v * w)`, since the fermion
  parity is the parity of the mass weight. -/
lemma mul_eq_smul_mul_of_mem_massWeightSubmodule (hP : IsMassWeightPoly P)
    (hpar : T.HasMassWeightParity) {v w : ℕ} {x y : T.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule P v) (hy : y ∈ massWeightSubmodule P w) :
    x * y = ((-1 : ℂ) ^ (v * w)) • (y * x) := by
  rw [massWeightSubmodule_eq_span hP] at hx hy
  exact mul_eq_smul_mul_of_mem_span_weightedMonomials hpar hx hy

end LocalCovFieldAlgebra

end GaugeFieldData
