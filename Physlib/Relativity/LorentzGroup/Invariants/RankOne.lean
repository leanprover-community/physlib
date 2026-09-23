/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.LorentzCovariance
/-!
# Lorentz invariants of a single four-vector index

A four-vector `T^{μ}` has no Lorentz invariant built from its four components but `0`. There is
nothing to contract it with: the metric takes two indices and the Levi-Civita symbol four. That
is `eq_zero_of_invariant`, and `mem_of_invariant_of_mem_sup` is the same statement modulo a
Lorentz-stable subspace `S`, the form the Standard Model files use.

The components are vectors `T d` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, indexed by one direction `d`, and `IsLorentzCovariant 1` says the
group moves them by the Lorentz matrix. `componentSpan T` is the set of their combinations.

An invariant of the span is `∑_d c_d • T d` for a coefficient tensor `c` that the Lorentz
matrices themselves fix (`Invariants.Basic`). Along a spatial axis the four light-cone
directions carry boost weights `2`, `-2`, `0`, `0`, and an invariant `c` has no light-cone
component of nonzero weight, which with one index says `c_d = 0` unless `d` is one of the two
directions transverse to time and to that axis (A). No direction is transverse to all three
axes, so running the three axes in turn leaves `c = 0` (B). Section C divides out `S`.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants

namespace RankOne

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 1 → (Fin 1 ⊕ Fin 3)) → B}

/-!

## A. What one axis leaves

The boost along the axis `i` scales the light-cone directions `D₀ - Dᵢ`, `D₀ + Dᵢ` and the two
transverse ones by `t²`, `t⁻²`, `1`, `1`, so their weights are `2`, `-2`, `0`, `0`. An invariant
`c` has no light-cone component of nonzero weight, so writing `c_d` in the light-cone basis
leaves only the two weight-zero directions, and their coefficients in `d` vanish unless `d` is
itself transverse.

-/

/-- A direction transverse to the boost along axis `i`: neither time nor the axis. -/
def Transverse (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) : Prop :=
  μ = Sum.inr (i + 1) ∨ μ = Sum.inr (i + 2)

instance (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) : Decidable (Transverse i μ) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A non-transverse direction has no weight-zero light-cone coefficient. -/
lemma prod_lightConeCoeffInv_eq_zero {i : Fin 3} {d : Fin 1 → Fin 1 ⊕ Fin 3}
    (hd : ¬ Transverse i (d 0)) {κ : Fin 1 → Fin 4}
    (hκ : ∑ s, lightConeWeight (κ s) = 0) :
    ∏ s, lightConeCoeffInv i (d s) (κ s) = 0 := by
  have h : ∀ κ : Fin 4, lightConeWeight κ = 0 → κ = 2 ∨ κ = 3 := by decide
  rw [Fin.sum_univ_one] at hκ
  rw [Fin.prod_univ_one]
  rcases h (κ 0) hκ with hk | hk
  · exact hk ▸ lightConeCoeffInv_two_eq_zero i fun h => hd (Or.inl h)
  · exact hk ▸ lightConeCoeffInv_three_eq_zero i fun h => hd (Or.inr h)

/-- An invariant coefficient tensor vanishes off the two directions transverse to the axis. -/
lemma eq_zero_of_not_transverse {c : (Fin 1 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    (i : Fin 3) {d : Fin 1 → Fin 1 ⊕ Fin 3} (hd : ¬ Transverse i (d 0)) : c d = 0 := by
  rw [eq_sum_lightConeComponent i c d]
  refine Finset.sum_eq_zero fun κ _ => ?_
  by_cases hκ : ∑ s, lightConeWeight (κ s) = 0
  · rw [prod_lightConeCoeffInv_eq_zero hd hκ, zero_mul]
  · rw [hc.lightConeComponent_eq_zero i hκ, mul_zero]

/-!

## B. The classification of the Lorentz invariants

No direction is transverse to all three axes at once, so applying A to the three axes in turn
leaves no coefficient standing.

-/

/-- No direction is transverse to all three axes at once, a finite check. -/
lemma not_transverse_all (μ : Fin 1 ⊕ Fin 3) :
    ¬(Transverse 0 μ ∧ Transverse 1 μ ∧ Transverse 2 μ) := by
  revert μ
  decide

/-- An invariant coefficient tensor is zero. -/
lemma eq_zero_of_isInvariantCoeff {c : (Fin 1 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) : c = 0 := by
  funext d
  show c d = 0
  by_cases h0 : Transverse 0 (d 0)
  · by_cases h1 : Transverse 1 (d 0)
    · by_cases h2 : Transverse 2 (d 0)
      · exact absurd ⟨h0, h1, h2⟩ (not_transverse_all (d 0))
      · exact eq_zero_of_not_transverse hc 2 h2
    · exact eq_zero_of_not_transverse hc 1 h1
  · exact eq_zero_of_not_transverse hc 0 h0

/-- Every Lorentz invariant in the span of the components is zero: one index carries no
  invariant contraction. -/
theorem eq_zero_of_invariant (hT : IsLorentzCovariant 1 B repLorentz T) {x : B}
    (hx : x ∈ componentSpan T) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 := by
  obtain ⟨c, hc, rfl⟩ := hT.exists_isInvariantCoeff_of_mem_componentSpan hx hinv
  simp [eq_zero_of_isInvariantCoeff hc]

/-!

## C. The classification modulo a Lorentz-stable submodule

A stable subspace `S` is divided out by passing to the quotient `B ⧸ S`, that is `B` with
`S` declared zero: the classes of the components again form a single Lorentz tensor, so
section B applies there and an invariant of `componentSpan T ⊔ S` lies in `S`.

-/

/-- A Lorentz invariant of `componentSpan T ⊔ S`, for a Lorentz-stable subspace `S`, already
  lies in `S`. -/
lemma mem_of_invariant_of_mem_sup (hT : IsLorentzCovariant 1 B repLorentz T) {x : B}
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ componentSpan T ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hzero := eq_zero_of_invariant (hT.quotient S hS) (mkQ_mem_componentSpan T S hx)
    fun g => by rw [quotient_apply_mkQ, hinv g]
  rwa [← Submodule.ker_mkQ S, LinearMap.mem_ker]

end RankOne

end Lorentz
