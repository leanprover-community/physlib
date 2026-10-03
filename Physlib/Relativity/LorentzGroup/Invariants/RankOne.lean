/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.LorentzCovariance
/-!
# Lorentz invariants of a single four-vector index

A four-vector `T^{μ}` has no Lorentz invariant but `0`. There is nothing to contract it with:
the metric takes two indices and the Levi-Civita symbol four. For an equivariant map
`f : ℂT(fun _ : Fin 1 => .up) →ₗ[ℂ] B`, `IsLorentzCovariant 1`, that is `eq_zero_of_invariant`,
and `reducesInvariantsTo_bot`, the form the Standard Model files use, is the same statement
modulo a Lorentz-stable submodule `S`.

The invariants of the range of `f` are the images of invariant tensors, so it is enough that an
invariant coefficient tensor `c` (`Invariants.Basic`) vanishes. Along a spatial axis the four
light-cone directions carry boost weights `2`, `-2`, `0`, `0`, and an invariant `c` has no
light-cone component of nonzero weight, which with one index says `c_d = 0` unless `d` is one of
the two directions transverse to time and to that axis (A). No direction is transverse to all three
axes, so running the three axes in turn leaves `c = 0` (B). Section C applies this to `f`.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants complexLorentzTensor

namespace RankOne

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}

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

/-!

## C. The invariants of an equivariant map

The invariants of the range of an equivariant map come from invariant tensors, whose coefficient
tensors are invariant, so section B leaves none of them.

-/

variable {f : ℂT(fun _ : Fin 1 => Color.up) →ₗ[ℂ] B}

/-- Every Lorentz invariant in the range of `f` is zero: one index carry no invariant
  contraction. -/
lemma eq_zero_of_invariant (hf : IsLorentzCovariant 1 B repLorentz f) {x : B}
    (hx : x ∈ LinearMap.range f) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 :=
  hf.eq_zero_of_isInvariantCoeff (fun _ hc => eq_zero_of_isInvariantCoeff hc) hx hinv

/-- The range of `f` reduces to `⊥`: a Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a
  Lorentz-stable submodule, lies in `S`. -/
lemma reducesInvariantsTo_bot (hf : IsLorentzCovariant 1 B repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) ⊥ :=
  hf.reducesInvariantsTo_bot_of_isInvariantCoeff fun _ hc => eq_zero_of_isInvariantCoeff hc

end RankOne

end Lorentz
