/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.Basic
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.ProjectionTheorem
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SelectionRules

/-!

# The Wigner–Eckart theorem for irreducible angular momentum representations

Tensor operators between arbitrary finite-dimensional irreducible angular momentum
representations.

## i. Overview

`AngularMomentumRepresentation` packages operators `Jx, Jy, Jz` on a complex vector space with
the angular momentum commutation relations. By `spin_classification`, a finite-dimensional
irreducible representation with `Jz ≠ 0` is isomorphic to a standard module `V(n)` by a linear
equivalence carrying `J₊`, `J₋` and `2Jz` to `e`, `f` and `h`; `n = 2j` is twice the spin.

A tensor operator of rank `k` from `ρ₁` on `V` to `ρ₂` on `W` is a linear map
`T : V(k) → Hom(V, W)` with `[J₊, T x] = T (e x)`, `[J₋, T x] = T (f x)` and
`[2Jz, T x] = T (h x)`. Conjugating with the equivalences turns it into a tensor operator between
standard modules, so the results for standard modules carry over:

- two tensor operators of the same rank between the same irreducible representations are
  proportional (the Wigner–Eckart theorem: a single reduced matrix element);
- a nonzero tensor operator satisfies the triangle rule for the spins.

The spin-0 representation (`Jz = 0`) is excluded throughout, since it does not generate a copy of
`sl₂`.

## ii. Key results

- `IsStandardEquiv` and `exists_isStandardEquiv` give the comparison with a standard module.
- `IsTensorOperatorOf` is the predicate for tensor operators between representations.
- `IsTensorOperatorOf.isTensorOperator_conjStd` transports a tensor operator to standard modules.
- `IsTensorOperatorOf.exists_eq_smul_of_ne_zero` is the Wigner–Eckart theorem.
- `IsTensorOperatorOf.triangleRule` is the triangle rule.

## iii. Table of contents

- A. Comparison with the standard modules
- B. Tensor operators between representations
- C. The Wigner–Eckart theorem

## iv. References

- E. P. Wigner, *Group Theory and its Application to the Quantum Mechanics of Atomic Spectra*,
  Academic Press (1959), chapter 21.

## A. Comparison with the standard modules

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open StandardSl2Module

attribute [local instance 100] LieRing.ofAssociativeRing

section StandardBracket

variable {K : Type*} [Field K] [CharZero K] {L : Type*} [LieRing L] [LieAlgebra K L] {h e f : L}
  {n : ℕ}

lemma standard_bracket_eSub (t : IsSl2Triple h e f) (w : StandardSl2Module K n) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    ⁅eSub (K := K) t, w⁆ = ρE w := by
  show Φ (K := K) (n := n) t (eSub t) w = ρE w
  rw [eSub_eq, Φ_apply]
  rfl

lemma standard_bracket_fSub (t : IsSl2Triple h e f) (w : StandardSl2Module K n) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    ⁅fSub (K := K) t, w⁆ = ρF w := by
  show Φ (K := K) (n := n) t (fSub t) w = ρF w
  rw [fSub_eq, Φ_apply]
  rfl

lemma standard_bracket_hSub (t : IsSl2Triple h e f) (w : StandardSl2Module K n) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    ⁅hSub (K := K) t, w⁆ = ρH w := by
  show Φ (K := K) (n := n) t (hSub t) w = ρH w
  rw [hSub_eq, Φ_apply]
  rfl

end StandardBracket

namespace AngularMomentumRepresentation

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A linear equivalence `V ≃ V(n)` carrying `J₊`, `J₋` and `2Jz` to `e`, `f` and `h`. -/
structure IsStandardEquiv (ρ : AngularMomentumRepresentation V) {n : ℕ}
    (ψ : V ≃ₗ[ℂ] StandardSl2Module ℂ n) : Prop where
  map_Jp : ∀ v, ψ (ρ.Jp v) = ρE (ψ v)
  map_Jm : ∀ v, ψ (ρ.Jm v) = ρF (ψ v)
  map_Jz : ∀ v, ψ (((2 : ℂ) • ρ.Jz) v) = ρH (ψ v)

/-- A finite-dimensional irreducible representation with `Jz ≠ 0` is isomorphic to a standard
module by a standard equivalence. -/
lemma exists_isStandardEquiv [FiniteDimensional ℂ V] (ρ : AngularMomentumRepresentation V)
    (hz : ρ.Jz ≠ 0) (hirr : ρ.IsIrreducible) :
    ∃ (n : ℕ) (ψ : V ≃ₗ[ℂ] StandardSl2Module ℂ n), ρ.IsStandardEquiv ψ := by
  obtain ⟨n, ⟨ψ⟩⟩ := ρ.spin_classification hz hirr
  let := standardSl2ModuleLieRingModule (K := ℂ) (n := n) (ρ.isSl2Triple hz)
  refine ⟨n, ψ.toLinearEquiv, ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩⟩
  · have h := ψ.map_lie (eSub (K := ℂ) (ρ.isSl2Triple hz)) v
    rw [standard_bracket_eSub] at h
    have hl : ⁅eSub (K := ℂ) (ρ.isSl2Triple hz), v⁆ = ρ.Jp v := by
      rw [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply]
      rfl
    rw [hl] at h
    exact h
  · have h := ψ.map_lie (fSub (K := ℂ) (ρ.isSl2Triple hz)) v
    rw [standard_bracket_fSub] at h
    have hl : ⁅fSub (K := ℂ) (ρ.isSl2Triple hz), v⁆ = ρ.Jm v := by
      rw [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply]
      rfl
    rw [hl] at h
    exact h
  · have h := ψ.map_lie (hSub (K := ℂ) (ρ.isSl2Triple hz)) v
    rw [standard_bracket_hSub] at h
    have hl : ⁅hSub (K := ℂ) (ρ.isSl2Triple hz), v⁆ = ((2 : ℂ) • ρ.Jz) v := by
      rw [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply]
      rfl
    rw [hl] at h
    exact h

/-- A standard equivalence for a representation with `Jz ≠ 0` lands in some `V(n)` with
`n > 0`. -/
lemma IsStandardEquiv.pos {ρ : AngularMomentumRepresentation V} {n : ℕ}
    {ψ : V ≃ₗ[ℂ] StandardSl2Module ℂ n} (hψ : ρ.IsStandardEquiv ψ) (hz : ρ.Jz ≠ 0) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso
    apply hz
    refine LinearMap.ext fun v => ?_
    have h := hψ.map_Jz v
    have h0 : (ρH : Module.End ℂ (StandardSl2Module ℂ 0)) (ψ v) = 0 := by
      funext i
      have hi : (i : ℕ) = 0 := by omega
      show (((0 : ℕ) : ℂ) - 2 * (i : ℕ)) * ψ v i = 0
      rw [hi]
      simp
    rw [h0, LinearEquiv.map_eq_zero_iff, LinearMap.smul_apply] at h
    exact (smul_eq_zero.mp h).resolve_left two_ne_zero
  · exact hn

lemma IsStandardEquiv.symm_ρE {ρ : AngularMomentumRepresentation V} {n : ℕ}
    {ψ : V ≃ₗ[ℂ] StandardSl2Module ℂ n} (hψ : ρ.IsStandardEquiv ψ) (y : StandardSl2Module ℂ n) :
    ψ.symm (ρE y) = ρ.Jp (ψ.symm y) := by
  rw [LinearEquiv.symm_apply_eq, hψ.map_Jp, LinearEquiv.apply_symm_apply]

lemma IsStandardEquiv.symm_ρF {ρ : AngularMomentumRepresentation V} {n : ℕ}
    {ψ : V ≃ₗ[ℂ] StandardSl2Module ℂ n} (hψ : ρ.IsStandardEquiv ψ) (y : StandardSl2Module ℂ n) :
    ψ.symm (ρF y) = ρ.Jm (ψ.symm y) := by
  rw [LinearEquiv.symm_apply_eq, hψ.map_Jm, LinearEquiv.apply_symm_apply]

lemma IsStandardEquiv.symm_ρH {ρ : AngularMomentumRepresentation V} {n : ℕ}
    {ψ : V ≃ₗ[ℂ] StandardSl2Module ℂ n} (hψ : ρ.IsStandardEquiv ψ) (y : StandardSl2Module ℂ n) :
    ψ.symm (ρH y) = ((2 : ℂ) • ρ.Jz) (ψ.symm y) := by
  rw [LinearEquiv.symm_apply_eq, hψ.map_Jz, LinearEquiv.apply_symm_apply]

/-!

## B. Tensor operators between representations

-/

variable {k : ℕ}

/-- A tensor operator of rank `k` from `ρ₁` on `V` to `ρ₂` on `W`: a linear map
`T : V(k) → Hom(V, W)` with `[J₊, T x] = T (e x)`, `[J₋, T x] = T (f x)` and
`[2Jz, T x] = T (h x)`. -/
structure IsTensorOperatorOf (ρ₁ : AngularMomentumRepresentation V)
    (ρ₂ : AngularMomentumRepresentation W) (T : StandardSl2Module ℂ k →ₗ[ℂ] V →ₗ[ℂ] W) :
    Prop where
  comm_p : ∀ x, ρ₂.Jp ∘ₗ T x - T x ∘ₗ ρ₁.Jp = T (ρE x)
  comm_m : ∀ x, ρ₂.Jm ∘ₗ T x - T x ∘ₗ ρ₁.Jm = T (ρF x)
  comm_z : ∀ x, ((2 : ℂ) • ρ₂.Jz) ∘ₗ T x - T x ∘ₗ ((2 : ℂ) • ρ₁.Jz) = T (ρH x)

/-- Conjugation of an operator-valued map by linear equivalences `V ≃ V(n₁)` and `W ≃ V(n₂)`. -/
def conjStd {n₁ n₂ : ℕ} (ψ₁ : V ≃ₗ[ℂ] StandardSl2Module ℂ n₁)
    (ψ₂ : W ≃ₗ[ℂ] StandardSl2Module ℂ n₂) (T : StandardSl2Module ℂ k →ₗ[ℂ] V →ₗ[ℂ] W) :
    StandardSl2Module ℂ k →ₗ[ℂ] StandardSl2Module ℂ n₁ →ₗ[ℂ] StandardSl2Module ℂ n₂ :=
  (ψ₁.arrowCongr ψ₂).toLinearMap ∘ₗ T

lemma conjStd_apply {n₁ n₂ : ℕ} (ψ₁ : V ≃ₗ[ℂ] StandardSl2Module ℂ n₁)
    (ψ₂ : W ≃ₗ[ℂ] StandardSl2Module ℂ n₂) (T : StandardSl2Module ℂ k →ₗ[ℂ] V →ₗ[ℂ] W)
    (x : StandardSl2Module ℂ k) (y : StandardSl2Module ℂ n₁) :
    conjStd ψ₁ ψ₂ T x y = ψ₂ (T x (ψ₁.symm y)) := rfl

lemma conjStd_injective {n₁ n₂ : ℕ} (ψ₁ : V ≃ₗ[ℂ] StandardSl2Module ℂ n₁)
    (ψ₂ : W ≃ₗ[ℂ] StandardSl2Module ℂ n₂) {T S : StandardSl2Module ℂ k →ₗ[ℂ] V →ₗ[ℂ] W}
    (h : conjStd ψ₁ ψ₂ T = conjStd ψ₁ ψ₂ S) : T = S := by
  refine LinearMap.ext fun x => LinearMap.ext fun v => ?_
  have := LinearMap.congr_fun (LinearMap.congr_fun h x) (ψ₁ v)
  rw [conjStd_apply, conjStd_apply, LinearEquiv.symm_apply_apply] at this
  exact ψ₂.injective this

/-- Conjugation by standard equivalences turns a tensor operator between representations into a
tensor operator between standard modules. -/
lemma IsTensorOperatorOf.isTensorOperator_conjStd {ρ₁ : AngularMomentumRepresentation V}
    {ρ₂ : AngularMomentumRepresentation W} {T : StandardSl2Module ℂ k →ₗ[ℂ] V →ₗ[ℂ] W}
    (hT : IsTensorOperatorOf ρ₁ ρ₂ T) {n₁ n₂ : ℕ} {ψ₁ : V ≃ₗ[ℂ] StandardSl2Module ℂ n₁}
    {ψ₂ : W ≃ₗ[ℂ] StandardSl2Module ℂ n₂} (h₁ : ρ₁.IsStandardEquiv ψ₁)
    (h₂ : ρ₂.IsStandardEquiv ψ₂) : IsTensorOperator (conjStd ψ₁ ψ₂ T) where
  comm_E x := LinearMap.ext fun y => by
    have hT' := LinearMap.congr_fun (hT.comm_p x) (ψ₁.symm y)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply] at hT' ⊢
    rw [conjStd_apply, conjStd_apply, conjStd_apply, h₁.symm_ρE, ← h₂.map_Jp, ← map_sub, hT']
  comm_F x := LinearMap.ext fun y => by
    have hT' := LinearMap.congr_fun (hT.comm_m x) (ψ₁.symm y)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply] at hT' ⊢
    rw [conjStd_apply, conjStd_apply, conjStd_apply, h₁.symm_ρF, ← h₂.map_Jm, ← map_sub, hT']
  comm_H x := LinearMap.ext fun y => by
    have hT' := LinearMap.congr_fun (hT.comm_z x) (ψ₁.symm y)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply] at hT' ⊢
    rw [conjStd_apply, conjStd_apply, conjStd_apply, h₁.symm_ρH, ← h₂.map_Jz, ← map_sub, hT']

/-!

## C. The Wigner–Eckart theorem

-/

namespace IsTensorOperatorOf

variable {ρ₁ : AngularMomentumRepresentation V} {ρ₂ : AngularMomentumRepresentation W}

lemma conjStd_zero {n₁ n₂ : ℕ} (ψ₁ : V ≃ₗ[ℂ] StandardSl2Module ℂ n₁)
    (ψ₂ : W ≃ₗ[ℂ] StandardSl2Module ℂ n₂) :
    conjStd ψ₁ ψ₂ (0 : StandardSl2Module ℂ k →ₗ[ℂ] V →ₗ[ℂ] W) = 0 :=
  LinearMap.comp_zero _

/-- **Triangle rule** for irreducible representations: a nonzero tensor operator of rank `k`
from `ρ₁ ≅ V(n₁)` to `ρ₂ ≅ V(n₂)` satisfies `TriangleRule k n₁ n₂`, i.e. `|j₁ - j₂| ≤ κ ≤ j₁ + j₂`
for `k = 2κ`, `n₁ = 2j₁`, `n₂ = 2j₂`. -/
lemma triangleRule (h₁z : ρ₁.Jz ≠ 0) {T : StandardSl2Module ℂ k →ₗ[ℂ] V →ₗ[ℂ] W}
    (hT : IsTensorOperatorOf ρ₁ ρ₂ T) (hT0 : T ≠ 0) {n₁ n₂ : ℕ}
    {ψ₁ : V ≃ₗ[ℂ] StandardSl2Module ℂ n₁} {ψ₂ : W ≃ₗ[ℂ] StandardSl2Module ℂ n₂}
    (hψ₁ : ρ₁.IsStandardEquiv ψ₁) (hψ₂ : ρ₂.IsStandardEquiv ψ₂) : TriangleRule k n₁ n₂ := by
  have hn₁ := hψ₁.pos h₁z
  refine (hT.isTensorOperator_conjStd hψ₁ hψ₂).triangleRule (by omega) fun h => hT0 ?_
  apply conjStd_injective ψ₁ ψ₂
  rw [h, conjStd_zero]

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- **Wigner–Eckart theorem** for irreducible representations: two tensor operators of the same
rank between the same irreducible representations are proportional, provided the second is
nonzero. -/
lemma exists_eq_smul_of_ne_zero (h₁z : ρ₁.Jz ≠ 0) (h₁ : ρ₁.IsIrreducible) (h₂z : ρ₂.Jz ≠ 0)
    (h₂ : ρ₂.IsIrreducible) {T S : StandardSl2Module ℂ k →ₗ[ℂ] V →ₗ[ℂ] W}
    (hT : IsTensorOperatorOf ρ₁ ρ₂ T) (hS : IsTensorOperatorOf ρ₁ ρ₂ S) (hS0 : S ≠ 0) :
    ∃ c : ℂ, T = c • S := by
  obtain ⟨n₁, ψ₁, hψ₁⟩ := ρ₁.exists_isStandardEquiv h₁z h₁
  obtain ⟨n₂, ψ₂, hψ₂⟩ := ρ₂.exists_isStandardEquiv h₂z h₂
  have hn₁ := hψ₁.pos h₁z
  have hS0' : conjStd ψ₁ ψ₂ S ≠ 0 := by
    intro h
    apply hS0
    apply conjStd_injective ψ₁ ψ₂
    rw [h, conjStd_zero]
  obtain ⟨c, hc⟩ := (hT.isTensorOperator_conjStd hψ₁ hψ₂).exists_eq_smul_of_ne_zero
    (by omega) (hS.isTensorOperator_conjStd hψ₁ hψ₂) hS0'
  refine ⟨c, conjStd_injective ψ₁ ψ₂ ?_⟩
  rw [hc]
  simp only [conjStd, LinearMap.comp_smul]

end IsTensorOperatorOf

end AngularMomentumRepresentation

end PhyslibAlpha.Sl2
