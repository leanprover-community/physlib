/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.SmallSets

/-!
# Indexing a net by the members of a filter

A family indexed by the members of a filter `l` — a net of the shape `k : {s : Set α // s ∈ l} → β`
— is naturally taken along `Filter.comap Subtype.val l.smallSets`, for which `∀ᶠ s in _, p s` says
that `p` holds for every small enough member of `l`. This file records that this index filter is
never the bottom filter, so that convergence along it has content.
-/

public section

open Filter

namespace TauCeti

/-- **A filter indexes a nontrivial net by its own members.** A net indexed by the members of a
filter `l` converges along this filter, the members read through `Filter.smallSets`, so that
`∀ᶠ s in _, p s` says that `p` holds for every small enough member of `l`; it is not the bottom
filter, every member of `l` being an index below itself. -/
theorem comap_val_smallSets_neBot {α : Type*} (l : Filter α) :
    NeBot (comap (Subtype.val : {s : Set α // s ∈ l} → Set α) l.smallSets) := by
  refine comap_neBot_iff.2 fun t ht => ?_
  obtain ⟨V, hV, hVt⟩ := eventually_smallSets.1 ht
  exact ⟨⟨V, hV⟩, hVt V subset_rfl⟩

end TauCeti
