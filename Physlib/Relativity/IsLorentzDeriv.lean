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

A family of operators indexed by the four spacetime directions is a **Lorentz derivative**
when the representation of `SL(2,ℂ)` intertwines it through the columns of the Lorentz
matrix, as the jet derivatives on a jet algebra do.

Along the `i`-th spatial axis the four operators regroup into the two light-cone
combinations `lightConePlus D i = D_0 - D_i` and `lightConeMinus D i = D_0 + D_i`, which
shift every boost weight by `+2` and `-2` respectively, and the two transverse operators,
which preserve it. Consequently the weight-`k` part of the span of all derivative images of
a submodule redistributes onto the shifted weight projections
(`boostProj_map_submodule_x/y/z`).

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
  general form of the `lorentz_apply` field of `IsGaugeField`, for a field valued in an
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

/-!

## A. Light cone derivatives

-/

/-- The light-cone combination `D_0 - D_i`, raising every boost weight along the `i`-th
  axis by two (`lightConePlus_mem`). -/
def lightConePlus (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) (i : Fin 3) : A →ₗ[ℂ] A :=
  D (Sum.inl 0) - D (Sum.inr i)

/-- The light-cone combination `D_0 + D_i`, lowering every boost weight along the `i`-th
  axis by two (`lightConeMinus_mem`). -/
def lightConeMinus (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) (i : Fin 3) : A →ₗ[ℂ] A :=
  D (Sum.inl 0) + D (Sum.inr i)

/-!

## B. Relationship to boost weights

-/

section

/-- A transverse Lorentz derivative leaves the boost weight along the `i`-th axis alone. -/
lemma transverse_mem [IsLorentzDeriv rep D] {i j : Fin 3} (hij : j ≠ i) {k : ℤ} {x : A}
    (hx : x ∈ BoostWeight.boostWeightSubmodule rep i k) :
    D (Sum.inr j) x ∈ BoostWeight.boostWeightSubmodule rep i k := by
  intro t ht
  rw [rep_deriv, hx t ht, algebraMap_real_complex]
  rw [show Lorentz.SL2C.toLorentzGroup (Lorentz.SL2C.boostAxis i t ht) =
    LorentzGroup.boostAxis i t ht from rfl]
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | simp [LorentzGroup.boostAxis_apply]

/-- The light-cone combination `D_0 - D_i` raises the boost weight along the `i`-th axis
  by two. -/
lemma lightConePlus_mem [IsLorentzDeriv rep D] {i : Fin 3} {k : ℤ} {x : A}
    (hx : x ∈ BoostWeight.boostWeightSubmodule rep i k) :
    lightConePlus D i x ∈ BoostWeight.boostWeightSubmodule rep i (k + 2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  simp only [lightConePlus, LinearMap.sub_apply]
  rw [map_sub, rep_deriv, rep_deriv, hx t ht]
  rw [algebraMap_real_complex, zpow_add₀ ht']
  rw [show Lorentz.SL2C.toLorentzGroup (Lorentz.SL2C.boostAxis i t ht) =
    LorentzGroup.boostAxis i t ht from rfl]
  fin_cases i
  all_goals
    simp [LorentzGroup.boostAxis_apply, Fintype.sum_sum_type, Fin.sum_univ_three]
    match_scalars <;> (field_simp [ht']; noncomm_ring)

/-- The light-cone combination `D_0 + D_i` lowers the boost weight along the `i`-th axis
  by two. -/
lemma lightConeMinus_mem [IsLorentzDeriv rep D] {i : Fin 3} {k : ℤ} {x : A}
    (hx : x ∈ BoostWeight.boostWeightSubmodule rep i k) :
    lightConeMinus D i x ∈ BoostWeight.boostWeightSubmodule rep i (k - 2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  simp only [lightConeMinus, LinearMap.add_apply]
  rw [map_add, rep_deriv, rep_deriv, hx t ht]
  rw [algebraMap_real_complex, zpow_sub₀ ht']
  rw [show Lorentz.SL2C.toLorentzGroup (Lorentz.SL2C.boostAxis i t ht) =
    LorentzGroup.boostAxis i t ht from rfl]
  fin_cases i
  all_goals
    simp [LorentzGroup.boostAxis_apply, Fintype.sum_sum_type, Fin.sum_univ_three]
    match_scalars <;> (field_simp [ht']; noncomm_ring)

end

/-!

## The boost projections of the span of the derivative images

-/

/-- Two composites agreeing on a submodule have the same double image. -/
private lemma map_map_eq_of_forall_mem {f g f' g' : A →ₗ[ℂ] A}
    {V : Submodule ℂ A} (h : ∀ x ∈ V, g (f x) = g' (f' x)) :
    (V.map f).map g = (V.map f').map g' := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨f' v, ⟨v, hv, rfl⟩, (h v hv).symm⟩
  · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨f v, ⟨v, hv, rfl⟩, h v hv⟩

/-- The images under `D_0` and `D_i` span the same submodule as the images under the two
  light-cone combinations. -/
lemma map_pair_eq_lightCone (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) (i : Fin 3)
    (V : Submodule ℂ A) :
    V.map (D (Sum.inl 0)) + V.map (D (Sum.inr i)) =
      V.map (lightConePlus D i) + V.map (lightConeMinus D i) := by
  rw [Submodule.add_eq_sup, Submodule.add_eq_sup]
  refine le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)
  · rintro _ ⟨v, hv, rfl⟩
    rw [show D (Sum.inl 0) v =
        (2⁻¹ : ℂ) • lightConePlus D i v + (2⁻¹ : ℂ) • lightConeMinus D i v from by
      simp only [lightConePlus, lightConeMinus, LinearMap.sub_apply, LinearMap.add_apply]
      module]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.mem_sup_left ⟨v, hv, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right ⟨v, hv, rfl⟩))
  · rintro _ ⟨v, hv, rfl⟩
    rw [show D (Sum.inr i) v =
        (-2⁻¹ : ℂ) • lightConePlus D i v + (2⁻¹ : ℂ) • lightConeMinus D i v from by
      simp only [lightConePlus, lightConeMinus, LinearMap.sub_apply, LinearMap.add_apply]
      module]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.mem_sup_left ⟨v, hv, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right ⟨v, hv, rfl⟩))
  · rintro _ ⟨v, hv, rfl⟩
    simp only [lightConePlus, LinearMap.sub_apply]
    exact sub_mem (Submodule.mem_sup_left ⟨v, hv, rfl⟩)
      (Submodule.mem_sup_right ⟨v, hv, rfl⟩)
  · rintro _ ⟨v, hv, rfl⟩
    simp only [lightConeMinus, LinearMap.add_apply]
    exact add_mem (Submodule.mem_sup_left ⟨v, hv, rfl⟩)
      (Submodule.mem_sup_right ⟨v, hv, rfl⟩)

/-- The engine behind the three axis lemmas: the projection of the four derivative images
  redistributes onto the shifted projections of `V`. -/
private lemma boostProj_map_submodule_aux [BoostWeight.IsBoostGraded rep]
    [IsLorentzDeriv rep D] {i t₁ t₂ : Fin 3} (ht₁ : t₁ ≠ i) (ht₂ : t₂ ≠ i) (k : ℤ)
    (V : Submodule ℂ A) :
    (V.map (D (Sum.inl 0)) + V.map (D (Sum.inr i)) + V.map (D (Sum.inr t₁)) +
        V.map (D (Sum.inr t₂))).map (BoostWeight.boostProj rep i k) =
      (V.map (BoostWeight.boostProj rep i (k - 2))).map (lightConePlus D i) +
      (V.map (BoostWeight.boostProj rep i (k + 2))).map (lightConeMinus D i) +
      (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr t₁)) +
      (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr t₂)) := by
  have hlcp : (V.map (lightConePlus D i)).map (BoostWeight.boostProj rep i k) =
      (V.map (BoostWeight.boostProj rep i (k - 2))).map (lightConePlus D i) := by
    refine map_map_eq_of_forall_mem fun v _ => ?_
    refine BoostWeight.boostProj_comm rep k (k - 2) (fun {w} {y} hyw => ?_) v
    rw [show w + k - (k - 2) = w + 2 from by ring]
    exact lightConePlus_mem hyw
  have hlcn : (V.map (lightConeMinus D i)).map (BoostWeight.boostProj rep i k) =
      (V.map (BoostWeight.boostProj rep i (k + 2))).map (lightConeMinus D i) := by
    refine map_map_eq_of_forall_mem fun v _ => ?_
    refine BoostWeight.boostProj_comm rep k (k + 2) (fun {w} {y} hyw => ?_) v
    rw [show w + k - (k + 2) = w - 2 from by ring]
    exact lightConeMinus_mem hyw
  have hd₁ : (V.map (D (Sum.inr t₁))).map (BoostWeight.boostProj rep i k) =
      (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr t₁)) := by
    refine map_map_eq_of_forall_mem fun v _ => ?_
    refine BoostWeight.boostProj_comm rep k k (fun {w} {y} hyw => ?_) v
    rw [show w + k - k = w from by ring]
    exact transverse_mem ht₁ hyw
  have hd₂ : (V.map (D (Sum.inr t₂))).map (BoostWeight.boostProj rep i k) =
      (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr t₂)) := by
    refine map_map_eq_of_forall_mem fun v _ => ?_
    refine BoostWeight.boostProj_comm rep k k (fun {w} {y} hyw => ?_) v
    rw [show w + k - k = w from by ring]
    exact transverse_mem ht₂ hyw
  rw [map_pair_eq_lightCone]
  simp only [Submodule.add_eq_sup, Submodule.map_sup, hlcp, hlcn, hd₁, hd₂]

/-- **The boost projections of the span of Lorentz derivatives, along any axis.** The
  weight-`k` part of the span of the four derivative images of `V` is spanned by the
  light-cone combinations applied to the weight-`(k ∓ 2)` parts of `V` together with the two
  transverse derivatives, at directions `i + 1` and `i + 2`, of its weight-`k` part. -/
lemma boostProj_map_deriv_map_submodule [BoostWeight.IsBoostGraded rep]
    [IsLorentzDeriv rep D] (k : ℤ) (V : Submodule ℂ A) (i : Fin 3) :
    (∑ α, V.map (D α)).map (BoostWeight.boostProj rep i k) =
    (V.map (BoostWeight.boostProj rep i (k - 2))).map (lightConePlus D i)
    + (V.map (BoostWeight.boostProj rep i (k + 2))).map (lightConeMinus D i)
    + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 1)))
    + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 2))) := by
  have hsum : (∑ α, V.map (D α)) =
      V.map (D (Sum.inl 0)) + V.map (D (Sum.inr i)) + V.map (D (Sum.inr (i + 1))) +
        V.map (D (Sum.inr (i + 2))) := by
    rw [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three]
    fin_cases i <;>
      (simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceAdd]; abel)
  rw [hsum]
  exact boostProj_map_submodule_aux (by fin_cases i <;> decide) (by fin_cases i <;> decide) k V

/-- **Two derivative layers.** The weight-`k` part of the span of all second derivative
  images of `V` redistributes onto the weight `k - 4, …, k + 4` parts of `V`, hit by the
  light-cone and transverse operators twice over: `boostProj_map_deriv_map_submodule`
  applied at the outer layer and then to each of the three inner projected spans. -/
lemma boostProj_map_deriv_map_deriv_map [BoostWeight.IsBoostGraded rep] [IsLorentzDeriv rep D]
    (k : ℤ) (V : Submodule ℂ A) (i : Fin 3) :
    (∑ β, (∑ α, V.map (D α)).map (D β)).map (BoostWeight.boostProj rep i k) =
    ((V.map (BoostWeight.boostProj rep i (k - 4))).map (lightConePlus D i)
      + (V.map (BoostWeight.boostProj rep i k)).map (lightConeMinus D i)
      + (V.map (BoostWeight.boostProj rep i (k - 2))).map (D (Sum.inr (i + 1)))
      + (V.map (BoostWeight.boostProj rep i (k - 2))).map (D (Sum.inr (i + 2)))).map
        (lightConePlus D i)
    + ((V.map (BoostWeight.boostProj rep i k)).map (lightConePlus D i)
      + (V.map (BoostWeight.boostProj rep i (k + 4))).map (lightConeMinus D i)
      + (V.map (BoostWeight.boostProj rep i (k + 2))).map (D (Sum.inr (i + 1)))
      + (V.map (BoostWeight.boostProj rep i (k + 2))).map (D (Sum.inr (i + 2)))).map
        (lightConeMinus D i)
    + ((V.map (BoostWeight.boostProj rep i (k - 2))).map (lightConePlus D i)
      + (V.map (BoostWeight.boostProj rep i (k + 2))).map (lightConeMinus D i)
      + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 1)))
      + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 2)))).map
        (D (Sum.inr (i + 1)))
    + ((V.map (BoostWeight.boostProj rep i (k - 2))).map (lightConePlus D i)
      + (V.map (BoostWeight.boostProj rep i (k + 2))).map (lightConeMinus D i)
      + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 1)))
      + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 2)))).map
        (D (Sum.inr (i + 2))) := by
  rw [boostProj_map_deriv_map_submodule k _ i, boostProj_map_deriv_map_submodule (k - 2) V i,
    boostProj_map_deriv_map_submodule (k + 2) V i, boostProj_map_deriv_map_submodule k V i,
    show k - 2 - 2 = k - 4 from by ring, show k - 2 + 2 = k from by ring,
    show k + 2 - 2 = k from by ring, show k + 2 + 2 = k + 4 from by ring]

/-- The span of the derivative images of a weight-decomposed submodule is weight decomposed:
  the projections stay inside it and the support widens by the light-cone shifts `±2`. -/
noncomputable def _root_.Lorentz.BoostWeight.WeightDecomposition.deriv
    [BoostWeight.IsBoostGraded rep] {i : Fin 3} {V : Submodule ℂ A}
    (d : BoostWeight.WeightDecomposition rep i V)
    (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) [IsLorentzDeriv rep D] :
    BoostWeight.WeightDecomposition rep i (∑ α, V.map (D α)) := by
  classical
  have hV : ∀ μ, V.map (D μ) ≤ ∑ α, V.map (D α) := fun μ =>
    Finset.single_le_sum (f := fun α => V.map (D α))
      (fun _ _ => by rw [Submodule.zero_eq_bot]; exact bot_le) (Finset.mem_univ μ)
  have hsub : ∀ f g : A →ₗ[ℂ] A, V.map (f - g) ≤ V.map f ⊔ V.map g := by
    rintro f g _ ⟨v, hv, rfl⟩
    rw [LinearMap.sub_apply]
    exact sub_mem (Submodule.mem_sup_left ⟨v, hv, rfl⟩)
      (Submodule.mem_sup_right ⟨v, hv, rfl⟩)
  have hadd : ∀ f g : A →ₗ[ℂ] A, V.map (f + g) ≤ V.map f ⊔ V.map g := by
    rintro f g _ ⟨v, hv, rfl⟩
    rw [LinearMap.add_apply]
    exact add_mem (Submodule.mem_sup_left ⟨v, hv, rfl⟩)
      (Submodule.mem_sup_right ⟨v, hv, rfl⟩)
  refine BoostWeight.WeightDecomposition.ofMapClosed rep (d.supp + ({-2, 0, 2} : Finset ℤ))
    (fun k => ?_) (fun k hk => ?_)
  · rw [boostProj_map_deriv_map_submodule k V i]
    simp only [Submodule.add_eq_sup]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact (Submodule.map_mono (d.map_boostProj_le _)).trans
        ((hsub _ _).trans (sup_le (hV _) (hV _)))
    · exact (Submodule.map_mono (d.map_boostProj_le _)).trans
        ((hadd _ _).trans (sup_le (hV _) (hV _)))
    · exact (Submodule.map_mono (d.map_boostProj_le _)).trans (hV _)
    · exact (Submodule.map_mono (d.map_boostProj_le _)).trans (hV _)
  · have h₁ : k - 2 ∉ d.supp := fun h => hk (by
      simpa using Finset.add_mem_add h (show (2 : ℤ) ∈ ({-2, 0, 2} : Finset ℤ) by decide))
    have h₂ : k + 2 ∉ d.supp := fun h => hk (by
      simpa using Finset.add_mem_add h (show (-2 : ℤ) ∈ ({-2, 0, 2} : Finset ℤ) by decide))
    have h₀ : k ∉ d.supp := fun h => hk (by
      simpa using Finset.add_mem_add h (show (0 : ℤ) ∈ ({-2, 0, 2} : Finset ℤ) by decide))
    rw [boostProj_map_deriv_map_submodule k V i, d.map_boostProj_of_notMem h₁,
      d.map_boostProj_of_notMem h₂, d.map_boostProj_of_notMem h₀]
    simp

end IsLorentzDeriv

end Lorentz

end
