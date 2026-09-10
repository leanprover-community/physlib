/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.IsQuadLorentz
/-!
# Lorentz invariants of a single four-vector index

A four-vector `T^{μ}` has no Lorentz invariant built from its four components but `0`. There is
nothing to contract it with: the metric takes two indices and the Levi-Civita symbol four. That
is `eq_zero_of_invariant`, and `mem_of_invariant_of_mem_sup` is the same statement modulo a
Lorentz-stable subspace `S`, the form the Standard Model files use.

The components are vectors `T d` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, indexed by one direction `d`, and `IsSingleLorentz` says the group
moves them by the Lorentz matrix (A). `hT.span` is the set of their combinations.

An invariant of the span is `∑_d c_d • T d` for a coefficient tensor `c` that the Lorentz
matrices themselves fix (A, from `Invariants.Basic`). Along a spatial axis the four light-cone
directions carry boost weights `2`, `-2`, `0`, `0`, and an invariant `c` has no light-cone
component of nonzero weight, which with one index says `c_d = 0` unless `d` is one of the two
directions transverse to time and to that axis (B). No direction is transverse to all three
axes, so running the three axes in turn leaves `c = 0` (C). Section D divides out `S`.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants
open IsQuadLorentz (quotRep quotRep_mkQ)

/-!

## A. Single Lorentz tensors, their span, and coefficient tensors

A direction is an element of `Fin 1 ⊕ Fin 3`, time or one of the three axes, and `T d` is the
component `T^{μ}` at `μ = d`. `IsSingleLorentz B repLorentz T` says the group moves them by the
Lorentz matrix `Λ` of `g : SL(2,ℂ)`, and `hT.span` is the set of combinations `∑ d, c d • T d`
(`mem_span_iff`). The components may be dependent, so the `c` writing a vector of the span is
not determined by it; `Invariants.exists_isInvariantCoeff_of_mem_span` picks out one that the
matrices fix, `act Λ c = c`, and the rest of the file classifies those.

-/

/-- A family `T` of elements of `B`, indexed by a single four-vector index, transforms
  as a vector `T^{μ}` under the representation `repLorentz` of `SL(2,ℂ)`. -/
structure IsSingleLorentz (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 1 → (Fin 1 ⊕ Fin 3)) → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 1 → Fin 1 ⊕ Fin 3),
    (∏ (i : Fin 1), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a

namespace IsSingleLorentz

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 1 → (Fin 1 ⊕ Fin 3)) → B}
  (hT : IsSingleLorentz B repLorentz T)

set_option linter.unusedVariables false in
/-- The span of the components; `hT` is unused, and is present only so it reads `hT.span`. -/
def span (hT : IsSingleLorentz B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span exactly when it is a combination `∑ d, c d • T d`. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ c : (Fin 1 → Fin 1 ⊕ Fin 3) → ℂ, x = ∑ d, c d • T d := by
  rw [span, ← Submodule.span_range_eq_iSup, ← Fintype.range_linearCombination,
    LinearMap.mem_range]
  simp only [Fintype.linearCombination_apply, eq_comm]

include hT in
/-- An invariant of the span is the contraction of an invariant coefficient tensor. -/
theorem exists_isInvariantCoeff_of_mem_span {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ c : (Fin 1 → Fin 1 ⊕ Fin 3) → ℂ, IsInvariantCoeff c ∧ x = ∑ d, c d • T d :=
  Invariants.exists_isInvariantCoeff_of_mem_span hT.repLorentz_T hx hinv

/-!

## B. What one axis leaves

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

## C. The classification of the Lorentz invariants

No direction is transverse to all three axes at once, so applying B to the three axes in turn
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

include hT in
/-- Every Lorentz invariant in the span of the components is zero: one index carries no
  invariant contraction. -/
theorem eq_zero_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 := by
  obtain ⟨c, hc, rfl⟩ := hT.exists_isInvariantCoeff_of_mem_span hx hinv
  simp [eq_zero_of_isInvariantCoeff hc]

/-!

## D. The classification modulo a Lorentz-stable submodule

A stable subspace `S` is divided out by passing to the quotient `B ⧸ S`, that is `B` with
`S` declared zero: the classes of the components again form a single Lorentz tensor, so
section D applies there and an invariant of `hT.span ⊔ S` lies in `S`.

-/

include hT in
/-- The classes of the components in the quotient again form a single Lorentz tensor. -/
lemma isSingleLorentz_quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsSingleLorentz (B ⧸ S) (quotRep (repLorentz := repLorentz) S hS)
      (fun l => S.mkQ (T l)) where
  repLorentz_T g l := by
    rw [quotRep_mkQ, hT.repLorentz_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

include hT in
/-- A Lorentz invariant of `hT.span ⊔ S`, for a Lorentz-stable subspace `S`, already lies
  in `S`. -/
lemma mem_of_invariant_of_mem_sup {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hT' := hT.isSingleLorentz_quotRep S hS
  have hmk : S.mkQ x ∈ hT'.span := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hT.mem_span_iff u).1 hu
    refine (hT'.mem_span_iff _).2 ⟨c, ?_⟩
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, map_sum]
    exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
  have hinv' : ∀ g : SL(2,ℂ),
      quotRep (repLorentz := repLorentz) S hS g (S.mkQ x) = S.mkQ x := by
    intro g
    rw [quotRep_mkQ, hinv g]
  have hzero := hT'.eq_zero_of_invariant hmk hinv'
  rwa [← Submodule.ker_mkQ S, LinearMap.mem_ker]

end IsSingleLorentz

end Lorentz
