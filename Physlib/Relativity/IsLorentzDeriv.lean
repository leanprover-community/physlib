/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.WeightGrading
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Class IsLorentzDeriv

A family of operators indexed by the four spacetime directions is a Lorentz derivative
when the representation of `SL(2,ℂ)` intertwines it through the columns of the Lorentz
matrix, as the jet derivatives on a jet algebra do. The iterated operator along a multiset
of directions then transforms by one column of the Lorentz matrix per slot
(`rep_iteratedD_ofFn`), which is the law `IsLorentzDerivTransforms` and its covariant form
`IsLorentzCovDerivTransforms` record for a family of derivative symbols.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups TensorProduct
open scoped Pointwise

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The dual of the trivial representation acts trivially. -/
@[simp] lemma _root_.Representation.trivial_dual_apply {k G V : Type*} [CommSemiring k]
    [Group G] [AddCommMonoid V] [Module k V] (g : G) (φ : Module.Dual k V) :
    (Representation.trivial k G V).dual g φ = φ := by
  ext v
  simp [Representation.dual_apply, Module.Dual.transpose_apply]


/-- The iterated operator `D_s = D_{ν₁} ⋯ D_{νₙ}` of a pairwise-commuting family of
  endomorphisms along a multiset `s` of indices. Commutativity is what makes the
  operator well-defined on a multiset, i.e. independent of any ordering of `s`. -/
def iteratedD {ι : Type*} (D : ι → A →ₗ[ℂ] A)
    (hD : ∀ i j, (D i).comp (D j) = (D j).comp (D i)) (s : Multiset ι) : A →ₗ[ℂ] A :=
  letI : LeftCommutative (fun (ν : ι) (L : A →ₗ[ℂ] A) => (D ν).comp L) :=
    ⟨fun i j L => by rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, hD]⟩
  s.foldr (fun ν L => (D ν).comp L) LinearMap.id

lemma iteratedD_zero {ι : Type*} (D : ι → A →ₗ[ℂ] A)
    (hD : ∀ i j, (D i).comp (D j) = (D j).comp (D i)) :
    iteratedD D hD (0 : Multiset ι) = LinearMap.id := by
  simp only [iteratedD, Multiset.foldr_zero]

lemma iteratedD_cons {ι : Type*} (D : ι → A →ₗ[ℂ] A)
    (hD : ∀ i j, (D i).comp (D j) = (D j).comp (D i)) (κ : ι) (s : Multiset ι) :
    iteratedD D hD (κ ::ₘ s) = (D κ).comp (iteratedD D hD s) := by
  simp only [iteratedD, Multiset.foldr_cons]

/-- The iterated operator of a singleton is the operator itself. -/
lemma iteratedD_singleton {ι : Type*} (D : ι → A →ₗ[ℂ] A)
    (hD : ∀ i j, (D i).comp (D j) = (D j).comp (D i)) (κ : ι) :
    iteratedD D hD {κ} = D κ := by
  rw [show ({κ} : Multiset ι) = κ ::ₘ 0 from rfl, iteratedD_cons, iteratedD_zero,
    LinearMap.comp_id]

/-- The iterated operator is additive in the multiset of directions: applying along
  `s + t` is applying along `t` and then along `s`. -/
lemma iteratedD_add {ι : Type*} (D : ι → A →ₗ[ℂ] A)
    (hD : ∀ i j, (D i).comp (D j) = (D j).comp (D i)) (s t : Multiset ι) :
    iteratedD D hD (s + t) = (iteratedD D hD s).comp (iteratedD D hD t) := by
  induction s using Multiset.induction_on with
  | empty => rw [zero_add, iteratedD_zero, LinearMap.id_comp]
  | cons κ s ih =>
      rw [Multiset.cons_add, iteratedD_cons, iteratedD_cons, ih, LinearMap.comp_assoc]

/-- The companion of `iteratedD_cons`, peeling the new operator on the inside: for a
  commuting family the extra operator may equally be applied first. -/
lemma iteratedD_cons' {ι : Type*} (D : ι → A →ₗ[ℂ] A)
    (hD : ∀ i j, (D i).comp (D j) = (D j).comp (D i)) (κ : ι) (s : Multiset ι) :
    iteratedD D hD (κ ::ₘ s) = (iteratedD D hD s).comp (D κ) := by
  rw [show (κ ::ₘ s) = s + {κ} from by rw [← Multiset.singleton_add, add_comm],
    iteratedD_add, iteratedD_singleton]

lemma iteratedD_mul (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A)
    (D_comm : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ))
    (D_mul : ∀ (μ : Fin 1 ⊕ Fin 3) (b₁ b₂ : A),
      D μ (b₁ * b₂) = D μ b₁ * b₂ + b₁ * D μ b₂)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (b₁ b₂ : A) :
    Lorentz.iteratedD D D_comm s (b₁ * b₂) =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm p.1 b₁ * Lorentz.iteratedD D D_comm p.2 b₂).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Lorentz.iteratedD_zero]
  | cons κ s ih =>
      have hterm : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
          D κ (Lorentz.iteratedD D D_comm p.1 b₁ * Lorentz.iteratedD D D_comm p.2 b₂) =
            Lorentz.iteratedD D D_comm (κ ::ₘ p.1) b₁ * Lorentz.iteratedD D D_comm p.2 b₂ +
              Lorentz.iteratedD D D_comm p.1 b₁ *
                Lorentz.iteratedD D D_comm (κ ::ₘ p.2) b₂ := by
        intro p
        rw [D_mul, Lorentz.iteratedD_cons, Lorentz.iteratedD_cons,
          LinearMap.comp_apply, LinearMap.comp_apply]
      rw [Lorentz.iteratedD_cons, LinearMap.comp_apply, ih, map_multiset_sum,
        Multiset.map_map]
      simp only [Function.comp_def]
      rw [Multiset.map_congr rfl fun p _ => hterm p, Multiset.sum_map_add,
        Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
        Multiset.map_map]
      simp only [Function.comp_def, Prod.map, id_eq]
      abel


/-- A family of operators indexed by the spacetime directions is a **Lorentz derivative**
  when the representation of `SL(2,ℂ)` intertwines it through the columns of the Lorentz
  matrix. The class needs only the module structure, so it applies uniformly to any
  representation space. -/
class IsLorentzDeriv {M : Type} [AddCommMonoid M] [Module ℂ M]
    (rep : Representation ℂ SL(2,ℂ) M) (D : (Fin 1 ⊕ Fin 3) → M →ₗ[ℂ] M) where
  rep_deriv {Λ μ x} : rep Λ (D μ x) =
    ∑ a, (((SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) • D a (rep Λ x)

/-- A family of derivative symbols `F : s ↦ [∂_s ψ^φ]`, indexed by the dual of a value
  space `V` carrying a representation of `SL(2,ℂ)`, **transforms as the derivative
  symbols of a Lorentz-covariant field**: each ordered symbol mixes into all tuples of
  directions by the per-slot columns of the Lorentz matrix, while the value index
  transforms by the contragredient action `rep.dual` on the dual of `V`. This is the
  general form of the Lorentz law `GaugeAlgebraRealization.lorentz_apply`, for a field valued in an
  arbitrary Lorentz representation — the trivial representation for scalars, the Weyl
  representations for fermions, and their conjugates for the barred fields. At `n = 0`
  it reduces to the homogeneous law `Λ • F₀^φ = F₀^{Λ^{-⊤} φ}`. -/
def IsLorentzDerivTransforms {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    [Module k A]
    (repLorentz : Representation ℂ SL(2,ℂ) A) (rep : Representation k SL(2,ℂ) V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual k V →ₗ[k] A) : Prop :=
  ∀ (Λ : SL(2,ℂ)) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual k V),
    repLorentz Λ (F (List.ofFn l) φ) =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
        (∏ i, (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
          F (List.ofFn p) (rep.dual Λ φ)

/-- A family of *covariant*-derivative symbols, indexed by ordered tuples of
  directions (covariant derivatives do not commute) and by the dual of a Lorentz
  representation `V`, **transforms as the covariant derivatives of a
  Lorentz-covariant field**: each derivative slot mixes by the columns of the Lorentz
  matrix, while the value index transforms by the contragredient action `rep.dual` on
  the dual of `V` — the ordered-tuple analogue of `IsLorentzDerivTransforms`. -/
def IsLorentzCovDerivTransforms {k V : Type*} [CommRing k] [AddCommGroup V]
    [Module k V] [Module k A] (repLorentz : Representation ℂ SL(2,ℂ) A)
    (rep : Representation k SL(2,ℂ) V)
    (F : {n : ℕ} → (Fin n → (Fin 1 ⊕ Fin 3)) → Module.Dual k V →ₗ[k] A) : Prop :=
  ∀ (Λ : SL(2,ℂ)) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual k V),
    repLorentz Λ (F l φ) =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
        (∏ i, (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
          F p (rep.dual Λ φ)

namespace IsLorentzDeriv

variable {rep : Representation ℂ SL(2,ℂ) A} {D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A}

/-- The scalar action of a real parameter, in the form the weight condition presents it. -/
private lemma algebraMap_real_complex (t : ℝ) : (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) := rfl

/-- **The Lorentz transformation of iterated derivatives**: for a Lorentz derivative the
  ordered derivative symbol `D_{l 0} ⋯ D_{l (n-1)} x` mixes into all tuples of
  directions, with one Lorentz matrix factor per slot. -/
lemma rep_iteratedD_ofFn [IsLorentzDeriv rep D]
    (D_comm : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ))
    (Λ : SL(2,ℂ)) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (x : A) :
    rep Λ (iteratedD D D_comm (List.ofFn l) x) =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
        (∏ i, (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
          iteratedD D D_comm (List.ofFn p) (rep Λ x) := by
  induction n with
  | zero =>
      rw [List.ofFn_zero,
        show ((([] : List (Fin 1 ⊕ Fin 3)) : Multiset (Fin 1 ⊕ Fin 3)) = 0) from rfl,
        iteratedD_zero, Fintype.sum_unique]
      simp [List.ofFn_zero, iteratedD_zero]
  | succ n ih =>
      have hstep : ∀ (a : Fin 1 ⊕ Fin 3) (p : Fin n → (Fin 1 ⊕ Fin 3)),
          ((List.ofFn (Fin.cons a p) : List (Fin 1 ⊕ Fin 3)) :
              Multiset (Fin 1 ⊕ Fin 3)) =
            a ::ₘ ((List.ofFn p : List (Fin 1 ⊕ Fin 3)) : Multiset (Fin 1 ⊕ Fin 3)) := by
        intro a p
        rw [List.ofFn_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rfl
      calc rep Λ (iteratedD D D_comm (List.ofFn l) x)
          = ∑ a, (((SL2C.toLorentzGroup Λ).1 a (l 0) : ℝ) : ℂ) •
              D a (rep Λ (iteratedD D D_comm
                (List.ofFn fun i : Fin n => l i.succ) x)) := by
            rw [show ((List.ofFn l : List (Fin 1 ⊕ Fin 3)) : Multiset (Fin 1 ⊕ Fin 3)) =
                l 0 ::ₘ ((List.ofFn fun i : Fin n => l i.succ : List (Fin 1 ⊕ Fin 3)) :
                  Multiset (Fin 1 ⊕ Fin 3)) from by rw [List.ofFn_succ]; rfl,
              iteratedD_cons, LinearMap.comp_apply, rep_deriv]
        _ = ∑ a, ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
              ((((SL2C.toLorentzGroup Λ).1 a (l 0) : ℝ) : ℂ) *
                ∏ i, (((SL2C.toLorentzGroup Λ).1 (p i) (l i.succ) : ℝ) : ℂ)) •
              iteratedD D D_comm (a ::ₘ ((List.ofFn p : List (Fin 1 ⊕ Fin 3)) :
                Multiset (Fin 1 ⊕ Fin 3))) (rep Λ x) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [ih (fun i => l i.succ), map_sum, Finset.smul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [map_smul, smul_smul, iteratedD_cons, LinearMap.comp_apply]
        _ = ∑ p : Fin (n + 1) → (Fin 1 ⊕ Fin 3),
              (∏ i, (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
              iteratedD D D_comm (List.ofFn p) (rep Λ x) := by
            rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => (Fin 1 ⊕ Fin 3))
                (fun p : Fin (n + 1) → (Fin 1 ⊕ Fin 3) =>
                  (∏ i, (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
                  iteratedD D D_comm (List.ofFn p) (rep Λ x)),
              Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
            show ((((SL2C.toLorentzGroup Λ).1 a (l 0) : ℝ) : ℂ) *
                ∏ i, (((SL2C.toLorentzGroup Λ).1 (p i) (l i.succ) : ℝ) : ℂ)) •
              iteratedD D D_comm (a ::ₘ ((List.ofFn p : List (Fin 1 ⊕ Fin 3)) :
                Multiset (Fin 1 ⊕ Fin 3))) (rep Λ x) =
              (∏ i, (((SL2C.toLorentzGroup Λ).1
                  ((Fin.cons a p : Fin (n + 1) → (Fin 1 ⊕ Fin 3)) i) (l i) : ℝ) : ℂ)) •
              iteratedD D D_comm
                (List.ofFn (Fin.cons a p : Fin (n + 1) → (Fin 1 ⊕ Fin 3))) (rep Λ x)
            rw [Fin.prod_univ_succ, hstep a p]
            simp only [Fin.cons_zero, Fin.cons_succ]

end IsLorentzDeriv

end Lorentz

end
