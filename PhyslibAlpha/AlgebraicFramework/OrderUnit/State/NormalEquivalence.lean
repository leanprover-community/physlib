/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Normal
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.WeightEquivalence

/-!

# Normality under the state/weight equivalence

A normal state yields a normal finite normalized weight through the canonical map
`UnitalPositiveLinearMap.toWeight`.  The two predicates have intentionally different domains:
state normality is about directed suprema in the whole ordered space, whereas a weight is only
defined on the positive cone.  The theorem below transports suprema across that inclusion rather
than defining a duplicate normal-state predicate.

The converse is deliberately not asserted at this generality.  An arbitrary directed set with a
supremum need not have one common lower bound, so it cannot in general be shifted wholesale into
the positive cone.  A reverse theorem requires either a bounded-below version of state normality
or a strengthened weight predicate that controls those translated directed families.

-/

@[expose] public section

open scoped ENNReal

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E]

namespace UnitalPositiveLinearMap

omit [IsOrderUnit E] in
/-- A normal state induces a normal weight.  No new normality predicate is introduced: the proof
transports a nonempty directed positive set to `E`, applies the canonical state predicate, and
then transports the nonnegative scalar supremum through `ENNReal.ofReal`. -/
theorem IsNormal.toWeight_isNormal {s : 𝓢[ℝ, E]} (hs : s.IsNormal) : s.toWeight.IsNormal := by
  intro D x hD hdir hLUB
  have hLUBcoe : IsLUB ((fun z : PosCone E => (z : E)) '' D) (x : E) := by
    constructor
    · rintro z ⟨z, hz, rfl⟩
      exact hLUB.1 hz
    · intro y hy
      obtain ⟨d, hd⟩ := hD
      have hy_nonneg : (0 : E) ≤ y := by
        exact (d.2.trans (hy ⟨d, hd, rfl⟩))
      let y' : PosCone E := ⟨y, hy_nonneg⟩
      exact hLUB.2 fun z hz => by
        change (z : E) ≤ (y' : E)
        exact hy ⟨z, hz, rfl⟩
  have hdircoe : DirectedOn (· ≤ ·) ((fun z : PosCone E => (z : E)) '' D) := by
    rintro z ⟨z, hz, rfl⟩ w ⟨w, hw, rfl⟩
    obtain ⟨u, hu, hzu, hwu⟩ := hdir z hz w hw
    exact ⟨u, ⟨u, hu, rfl⟩, hzu, hwu⟩
  have hsLUB := hs ((fun z : PosCone E => (z : E)) '' D) (x : E) (hD.image _)
    hdircoe hLUBcoe
  have hENN : IsLUB (ENNReal.ofReal '' (s '' ((fun z : PosCone E => (z : E)) '' D)))
      (ENNReal.ofReal (s (x : E))) := by
    constructor
    · rintro r ⟨r, hr, rfl⟩
      exact ENNReal.ofReal_mono (hsLUB.1 hr)
    · intro b hb
      by_cases htop : b = ⊤
      · subst b
        exact le_top
      · rw [ENNReal.ofReal_le_iff_le_toReal htop]
        apply hsLUB.2
        intro r hr
        rw [← ENNReal.ofReal_le_iff_le_toReal htop]
        exact hb ⟨r, hr, rfl⟩
  have himage : s.toWeight '' D =
      ENNReal.ofReal '' (s '' ((fun z : PosCone E => (z : E)) '' D)) := by
    ext r
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨s (z : E), ⟨(z : E), ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
  simpa only [himage, toWeight_apply] using hENN

end UnitalPositiveLinearMap
