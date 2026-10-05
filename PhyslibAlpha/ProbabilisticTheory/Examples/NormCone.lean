/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean
public import PhyslibAlpha.ProbabilisticTheory.State.Separation
public import PhyslibAlpha.Mathematics.Analysis.Normed.HolderDual
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Order-unit spaces built from a normed vector space

The order-unit space `ℝ × V` ordered by the norm cone of `V`, and its states as the dual ball.

## i. Overview

Any real normed vector space `V` carries a natural order-unit structure on `ℝ × V`: order unit
`(1, 0)`, and positive cone the "ice-cream" cone `{(r, x) | ‖x‖ ≤ r}` built from `V`'s norm. States
of this order-unit space correspond exactly to the closed unit ball of the continuous dual of `V`.

The qubit is the norm cone over Euclidean `ℝ³` and the generalized bit the norm cone over `ℝ³`
with the sup norm: same dimension, different norm, different state space.

## ii. Key results

- `NormCone V` : the order-unit space `ℝ × V`, ordered by the ice-cream cone built from `V`'s norm.
- `NormCone.instArchimedeanOrderUnitSpace` : `NormCone V` is an Archimedean order-unit space.
- `NormCone.mem_effect_iff` : an explicit description of `Effect (NormCone V)`.
- `NormCone.stateEquiv` : states of `NormCone V` correspond exactly to the closed unit ball of the
  continuous dual of `V`.
- `NormCone.lpStateEquiv`, `NormCone.supStateEquiv` : the states of an `ℓp` norm cone are the closed
  `ℓq` ball, those of the sup-normed cone the `ℓ1` ball.

## iii. Table of contents

- A. The ice-cream cone order
- B. `NormCone V` is an Archimedean order-unit space
- C. Effects
- D. States correspond to the closed unit ball of the dual
- E. States, expanded against a basis
- F. Purity and extreme points of the dual ball
- G. States of `ℓp` and sup norm cones

## iv. References

- J. Barrett, *Information processing in generalized probabilistic theories*, Phys. Rev. A 75,
  032304 (2007).
- P. Janotta and H. Lal, *Generalized probabilistic theories without the no-restriction
  hypothesis*, Phys. Rev. A 87, 052131 (2013).

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. The ice-cream cone order

-/

/-- The order-unit space `ℝ × V` built from a real normed vector space `V`, ordered by the
ice-cream cone `{(r, x) | ‖x‖ ≤ r}`, as a type synonym so its order does not clash with the
product order on `ℝ × V`. -/
@[nolint unusedArguments]
def NormCone (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] := ℝ × V

namespace NormCone

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The linear equivalence to the underlying product, forgetting the order. -/
def toProd : NormCone V ≃ ℝ × V := Equiv.refl _

instance : AddCommGroup (NormCone V) := inferInstanceAs (AddCommGroup (ℝ × V))
instance : Module ℝ (NormCone V) := inferInstanceAs (Module ℝ (ℝ × V))
instance : One (NormCone V) := ⟨(1, 0)⟩
instance : Nontrivial (NormCone V) := inferInstanceAs (Nontrivial (ℝ × V))

/-- `NormCone V` is finite-dimensional when `V` is. -/
instance [FiniteDimensional ℝ V] : Module.Finite ℝ (NormCone V) :=
  inferInstanceAs (Module.Finite ℝ (ℝ × V))

@[simp] lemma toProd_zero : toProd (0 : NormCone V) = 0 := rfl
@[simp] lemma toProd_add (x y : NormCone V) : toProd (x + y) = toProd x + toProd y := rfl
@[simp] lemma toProd_neg (x : NormCone V) : toProd (-x) = -toProd x := rfl
@[simp] lemma toProd_sub (x y : NormCone V) : toProd (x - y) = toProd x - toProd y := rfl
@[simp] lemma toProd_smul (c : ℝ) (x : NormCone V) : toProd (c • x) = c • toProd x := rfl
@[simp] lemma toProd_one : toProd (1 : NormCone V) = (1, 0) := rfl

/-- The order unit `1 : NormCone V` scaled by a real number, in coordinates. -/
lemma toProd_smul_one (r : ℝ) : toProd (r • (1 : NormCone V)) = (r, 0) := by
  rw [toProd_smul, toProd_one, Prod.smul_mk, smul_eq_mul, mul_one, smul_zero]

/-- Build an element of `NormCone V` from its coordinates. -/
def mk (r : ℝ) (v : V) : NormCone V := toProd.symm (r, v)

@[simp] lemma toProd_mk (r : ℝ) (v : V) : toProd (mk r v) = (r, v) := rfl

/-- The ice-cream cone: `(r, x)` is nonnegative when `‖x‖ ≤ r`. -/
def NonnegCone (z : NormCone V) : Prop := ‖(toProd z).2‖ ≤ (toProd z).1

instance : LE (NormCone V) := ⟨fun x y => NonnegCone (y - x)⟩
instance : LT (NormCone V) := ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩

lemma le_iff {x y : NormCone V} :
    x ≤ y ↔ ‖(toProd y).2 - (toProd x).2‖ ≤ (toProd y).1 - (toProd x).1 :=
  Iff.rfl

lemma mk_le_mk_iff {r₁ r₂ : ℝ} {v₁ v₂ : V} :
    mk r₁ v₁ ≤ mk r₂ v₂ ↔ ‖v₂ - v₁‖ ≤ r₂ - r₁ := by
  rw [le_iff, toProd_mk, toProd_mk]

instance : PartialOrder (NormCone V) where
  le_refl x := by rw [le_iff]; simp
  le_trans x y z hxy hyz := by
    rw [le_iff] at *
    linarith [norm_sub_le_norm_sub_add_norm_sub (toProd z).2 (toProd y).2 (toProd x).2]
  le_antisymm x y hxy hyx := by
    rw [le_iff] at hxy hyx
    rw [← norm_neg, neg_sub] at hyx
    have hn := norm_nonneg ((toProd y).2 - (toProd x).2)
    have h2 : (toProd y).2 - (toProd x).2 = 0 := norm_eq_zero.1 (by linarith)
    exact toProd.injective (Prod.ext (by linarith) (sub_eq_zero.1 h2).symm)
  lt_iff_le_not_ge _ _ := Iff.rfl

instance : IsOrderedAddMonoid (NormCone V) where
  add_le_add_left x y hxy z := by
    rw [le_iff] at hxy ⊢
    simpa using hxy

instance : PosSMulMono ℝ (NormCone V) where
  smul_le_smul_of_nonneg_left c hc x y hxy := by
    rw [le_iff] at hxy ⊢
    have hc' : (0 : ℝ) ≤ c := hc
    have hfst : (toProd (c • y)).1 - (toProd (c • x)).1 = c * ((toProd y).1 - (toProd x).1) := by
      rw [toProd_smul, toProd_smul, Prod.smul_fst, Prod.smul_fst, smul_eq_mul, smul_eq_mul]; ring
    have hsnd : (toProd (c • y)).2 - (toProd (c • x)).2 = c • ((toProd y).2 - (toProd x).2) := by
      rw [toProd_smul, toProd_smul, Prod.smul_snd, Prod.smul_snd, smul_sub]
    rw [hfst, hsnd, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc']
    exact mul_le_mul_of_nonneg_left hxy hc'

/-!

## B. `NormCone V` is an Archimedean order-unit space

-/

instance instOrderUnitSpace : OrderUnitSpace (NormCone V) where
  one_nonneg := by show NonnegCone (1 - 0); simp [NonnegCone]
  exists_nsmul_one_le x := by
    obtain ⟨n, hn⟩ := exists_nat_ge ((toProd x).1 + ‖(toProd x).2‖)
    refine ⟨n, ?_⟩
    rw [le_iff, ← Nat.cast_smul_eq_nsmul ℝ n (1 : NormCone V), toProd_smul, toProd_one,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one, smul_zero, zero_sub, norm_neg]
    linarith

instance instArchimedeanOrderUnitSpace : ArchimedeanOrderUnitSpace (NormCone V) where
  le_zero_of_forall_pos_smul_one_le x hx := by
    rw [le_iff]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := hx ε hε
    rw [le_iff] at this
    simp only [toProd_zero, Prod.fst_zero, Prod.snd_zero, zero_sub, norm_neg, toProd_smul_one]
      at this ⊢
    linarith

/-!

## C. Effects

-/

/-- The effects of `NormCone V` are the pairs `(r, v)` with `‖v‖ ≤ r` and `‖v‖ ≤ 1 - r`. -/
lemma mem_effect_iff {z : NormCone V} :
    z ∈ (Effect (NormCone V) : Set (NormCone V)) ↔
      ‖(toProd z).2‖ ≤ (toProd z).1 ∧ ‖(toProd z).2‖ ≤ 1 - (toProd z).1 := by
  simp [Set.mem_Icc, le_iff]

/-!

## D. States correspond to the closed unit ball of the dual

-/

@[simp] lemma mk_add (r₁ r₂ : ℝ) (v₁ v₂ : V) : mk r₁ v₁ + mk r₂ v₂ = mk (r₁ + r₂) (v₁ + v₂) :=
  toProd.injective (by simp)

@[simp] lemma mk_smul (c : ℝ) (r : ℝ) (v : V) : c • mk r v = mk (c * r) (c • v) :=
  toProd.injective (by simp)

@[simp] lemma mk_neg (r : ℝ) (v : V) : -mk r v = mk (-r) (-v) :=
  toProd.injective (by simp)

@[simp] lemma smul_one_eq_mk (r : ℝ) : r • (1 : NormCone V) = mk r 0 :=
  toProd.injective (by rw [toProd_smul_one, toProd_mk])

@[simp] lemma mk_toProd (z : NormCone V) : mk (toProd z).1 (toProd z).2 = z := rfl

lemma neg_smul_one_le_mk_zero_iff {r : ℝ} {v : V} : -(r • (1 : NormCone V)) ≤ mk 0 v ↔ ‖v‖ ≤ r := by
  rw [le_iff, toProd_neg, toProd_smul_one, toProd_mk]
  simp

lemma mk_zero_le_smul_one_iff {r : ℝ} {v : V} : mk 0 v ≤ r • (1 : NormCone V) ↔ ‖v‖ ≤ r := by
  rw [le_iff, toProd_smul_one, toProd_mk]
  simp [norm_neg]

open ArchimedeanOrderUnitSpace in
/-- The order-unit norm of a purely spatial coordinate `(0, v)` is exactly the norm of `v`: the
order-unit norm restricted to this slice is the norm it was built from. -/
lemma orderUnitNorm_mk_zero (v : V) : orderUnitNorm (mk 0 v) = ‖v‖ := by
  apply le_antisymm
  · exact orderUnitNorm_le
      ⟨norm_nonneg v, neg_smul_one_le_mk_zero_iff.mpr le_rfl, mk_zero_le_smul_one_iff.mpr le_rfl⟩
  · exact mk_zero_le_smul_one_iff.mp (orderUnitNorm_mem_orderUnitBounds (mk 0 v)).2.2

/-- The linear map `v ↦ (0, v)` from `V` into `NormCone V`. -/
def mkZeroLinear : V →ₗ[ℝ] NormCone V where
  toFun v := mk 0 v
  map_add' _ _ := by rw [mk_add, add_zero]
  map_smul' c v := by rw [mk_smul, mul_zero]; rfl

@[simp] lemma mkZeroLinear_apply (v : V) : mkZeroLinear v = mk 0 v := rfl

/-- Every state is a "radius plus a bounded linear functional of the spatial part". -/
lemma apply_mk_eq (ω : 𝓢[ℝ, NormCone V]) (r : ℝ) (v : V) :
    ω (mk r v) = r + ω (mkZeroLinear v) := by
  have hmk : mk r v = r • (1 : NormCone V) + mkZeroLinear v := by
    rw [smul_one_eq_mk, mkZeroLinear_apply, mk_add, zero_add, add_zero]
  rw [hmk, map_add, map_smul, map_one, smul_eq_mul, mul_one]

/-- The functional a state induces on `V`, `v ↦ ω (0, v)`, is `1`-Lipschitz. -/
lemma abs_apply_mkZeroLinear_le (ω : 𝓢[ℝ, NormCone V]) (v : V) :
    |ω (mkZeroLinear v)| ≤ ‖v‖ := by
  have hbdd : |ω (mkZeroLinear v)| ≤ ArchimedeanOrderUnitSpace.orderUnitNorm (mkZeroLinear v) :=
    UnitalPositiveLinearMap.abs_apply_le_orderUnitNorm ω _
  rwa [mkZeroLinear_apply, orderUnitNorm_mk_zero] at hbdd

/-- The linear functional `v ↦ ω (0, v)` induced by a state. -/
def dualOfLinear (ω : 𝓢[ℝ, NormCone V]) : V →ₗ[ℝ] ℝ where
  toFun v := ω (mkZeroLinear v)
  map_add' _ _ := by rw [mkZeroLinear.map_add, map_add]
  map_smul' _ _ := by rw [mkZeroLinear.map_smul, map_smul]; rfl

@[simp] lemma dualOfLinear_apply (ω : 𝓢[ℝ, NormCone V]) (v : V) :
    dualOfLinear ω v = ω (mkZeroLinear v) := rfl

/-- The bounded linear functional on `V` induced by a state of `NormCone V`. -/
noncomputable def dualOf (ω : 𝓢[ℝ, NormCone V]) : V →L[ℝ] ℝ :=
  (dualOfLinear ω).mkContinuous 1 (fun v => by simpa using abs_apply_mkZeroLinear_le ω v)

@[simp] lemma dualOf_apply (ω : 𝓢[ℝ, NormCone V]) (v : V) : dualOf ω v = ω (mkZeroLinear v) := by
  rw [dualOf, LinearMap.mkContinuous_apply, dualOfLinear_apply]

lemma norm_dualOf_le (ω : 𝓢[ℝ, NormCone V]) : ‖dualOf ω‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Build a state of `NormCone V` from a bounded linear functional `f` of norm at most `1`:
`ω (r, x) = r + f x`. -/
noncomputable def stateOfDual (f : V →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) : 𝓢[ℝ, NormCone V] :=
  UnitalPositiveLinearMap.ofLinearMap
    { toFun := fun z => (toProd z).1 + f (toProd z).2
      map_add' := fun x y => by simp [map_add]; ring
      map_smul' := fun c x => by simp [map_smul]; ring }
    (fun z hz => by
      have hz' : ‖(toProd z).2‖ ≤ (toProd z).1 := by simpa [le_iff] using hz
      have := neg_le_of_abs_le ((f.le_opNorm (toProd z).2).trans
        (mul_le_of_le_one_left (norm_nonneg _) hf))
      change 0 ≤ (toProd z).1 + f (toProd z).2
      linarith)
    (by simp)

@[simp] lemma stateOfDual_apply (f : V →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) (z : NormCone V) :
    stateOfDual f hf z = (toProd z).1 + f (toProd z).2 := rfl

/-- States of `NormCone V` correspond exactly to the closed unit ball of the continuous dual
of `V`. -/
noncomputable def stateEquiv : 𝓢[ℝ, NormCone V] ≃ {f : V →L[ℝ] ℝ // ‖f‖ ≤ 1} where
  toFun ω := ⟨dualOf ω, norm_dualOf_le ω⟩
  invFun f := stateOfDual f.1 f.2
  left_inv ω := by
    apply UnitalPositiveLinearMap.ext
    intro z
    rw [← mk_toProd z, stateOfDual_apply, toProd_mk, apply_mk_eq, dualOf_apply]
  right_inv f := by
    apply Subtype.ext
    ext v
    rw [dualOf_apply, stateOfDual_apply, mkZeroLinear_apply, toProd_mk]
    simp

/-!

## E. States, expanded against a basis

-/

variable {ι : Type*} [Fintype ι]

/-- A state is determined by its values on a basis. -/
lemma apply_mk_basis (b : Module.Basis ι ℝ V) (ω : 𝓢[ℝ, NormCone V]) (r : ℝ) (v : V) :
    ω (mk r v) = r + ∑ i, b.repr v i * ω (mk 0 (b i)) := by
  rw [apply_mk_eq]
  congr 1
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, mkZeroLinear_apply, smul_eq_mul]

/-!

## F. Purity and extreme points of the dual ball

-/

/-- `dualOf` sends mixtures to convex combinations. -/
lemma dualOf_mix (φ ψ : 𝓢[ℝ, NormCone V]) (t : unitInterval) :
    dualOf (UnitalPositiveLinearMap.mix φ ψ t) =
      (t : ℝ) • dualOf φ + (1 - (t : ℝ)) • dualOf ψ := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [dualOf_apply, UnitalPositiveLinearMap.mix_apply, add_apply, smul_apply,
    smul_eq_mul]

/-- `dualOf` is injective. -/
lemma dualOf_injective : Function.Injective (dualOf (V := V)) := by
  intro φ ψ h
  exact stateEquiv.injective (Subtype.ext h)

/-- `dualOf` undoes `stateOfDual`. -/
@[simp] lemma dualOf_stateOfDual (f : V →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) :
    dualOf (stateOfDual f hf) = f :=
  congrArg Subtype.val (stateEquiv.apply_symm_apply (⟨f, hf⟩ : {g : V →L[ℝ] ℝ // ‖g‖ ≤ 1}))

lemma range_dualOf : Set.range (dualOf (V := V)) = {g | ‖g‖ ≤ 1} :=
  (Set.range_subset_iff.2 norm_dualOf_le).antisymm fun f hf =>
    ⟨stateOfDual f hf, dualOf_stateOfDual f hf⟩

/-- A state is pure exactly when its functional is an extreme point of the unit ball of the
dual. -/
lemma isPure_stateOfDual_iff {f : V →L[ℝ] ℝ} (hf : ‖f‖ ≤ 1) :
    (stateOfDual f hf).IsPure ↔ f ∈ Set.extremePoints ℝ {g : V →L[ℝ] ℝ | ‖g‖ ≤ 1} := by
  rw [UnitalPositiveLinearMap.isPure_iff_mem_extremePoints dualOf_injective dualOf_mix,
    dualOf_stateOfDual, range_dualOf]

/-!

## G. States of `ℓp` and sup norm cones

-/

section Lp

open HolderDual

variable {n : ℕ} (b : Module.Basis (Fin n) ℝ V) {p q : ℝ}

include b in
/-- The states of an `ℓp` norm cone are the closed `ℓq` ball. -/
noncomputable def lpStateEquiv (hpq : p.HolderConjugate q)
    (hnorm : ∀ v : V, ‖v‖ = (∑ i, |b.repr v i| ^ p) ^ (1 / p)) :
    𝓢[ℝ, NormCone V] ≃ {a : Fin n → ℝ // ∑ i, |a i| ^ q ≤ 1} :=
  stateEquiv.trans (dualLpEquiv b hpq hnorm)

include b in
lemma lpCone_mem_effect_iff (hnorm : ∀ v : V, ‖v‖ = (∑ i, |b.repr v i| ^ p) ^ (1 / p))
    {z : NormCone V} : z ∈ (Effect (NormCone V) : Set (NormCone V)) ↔
      (∑ i, |b.repr (toProd z).2 i| ^ p) ^ (1 / p) ≤ (toProd z).1 ∧
        (∑ i, |b.repr (toProd z).2 i| ^ p) ^ (1 / p) ≤ 1 - (toProd z).1 := by
  rw [mem_effect_iff, hnorm]

end Lp

/-- The states of the sup-normed norm cone are the closed `ℓ1` ball. -/
noncomputable def supStateEquiv {m : ℕ} :
    𝓢[ℝ, NormCone (Fin m → ℝ)] ≃ {a : Fin m → ℝ // ∑ i, |a i| ≤ 1} :=
  stateEquiv.trans HolderDual.dualSupEquiv

lemma supCone_mem_effect_iff {m : ℕ} {z : NormCone (Fin m → ℝ)} :
    z ∈ (Effect (NormCone (Fin m → ℝ)) : Set (NormCone (Fin m → ℝ))) ↔
      ‖(toProd z).2‖ ≤ (toProd z).1 ∧ ‖(toProd z).2‖ ≤ 1 - (toProd z).1 :=
  mem_effect_iff

end NormCone

end ProbabilisticTheory
