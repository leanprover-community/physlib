/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.OfFinset
import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.Completeness
/-!

# Quanta of 5-d representations

## i. Overview

The 5-bar representations of the `SU(5)×U(1)` carry
the quantum numbers of their `U(1)` charges and their fluxes.

In this module we define the data structure for these quanta and
properties thereof.

## ii. Key results

- `FiveQuanta` is the type of quanta of 5-bar representations.
- `FiveQuanta.toFluxesFive` is the underlying `FluxesFive` of a `FiveQuanta`.
- `FiveQuanta.toCharges` is the underlying Multiset charges of a `FiveQuanta`.
- `FiveQuanta.reduce` is the reduction of a `FiveQuanta` which adds together
  all the fluxes corresponding to the same charge (i.e. representation).
- `FiveQuanta.liftCharges` given a charge `c` the `FiveQuanta` which have
  charge `c` and no exotics or zero fluxes.
- `FiveQuanta.anomalyCoefficient` is the anomaly coefficient associated with a `FiveQuanta`.

## iii. Table of contents

- A. The definition of `FiveQuanta`
  - A.1. The map to underlying fluxes
  - A.2. The map to underlying charges
  - A.3. The map from charges to fluxes
- B. The reduction of a `FiveQuanta`
  - B.1. The reduced `FiveQuanta` has no duplicate elements
  - B.2. The underlying charges of the reduced `FiveQuanta` are the deduped charges
  - B.3. Membership condition on the reduced `FiveQuanta`
  - B.4. Filter of the reduced `FiveQuanta` by a charge
  - B.5. The reduction is idempotent
  - B.6. Preservation of certain sums under reduction
  - B.7. Reduction does nothing if no duplicate charges
  - B.8. The charge map is preserved by reduction
  - B.9. A fluxes in the reduced `FiveQuanta` is a sum of fluxes in the original `FiveQuanta`
  - B.10. No exotics condition on the reduced `FiveQuanta`
    - B.10.1. Number of chiral `L`
    - B.10.2. Number of anti-chiral `L`
    - B.10.3. Number of chiral `D`
    - B.10.4. Number of anti-chiral `D`
    - B.10.5. The `NoExotics` condition on the reduced `FiveQuanta`
  - B.11. Reduce member of `FluxesFive.elemsNoExotics`
- C. Decomposition of a `FiveQuanta` into basic fluxes
  - C.1. Decomposition of fluxes
  - C.2. Decomposition of a `FiveQuanta` (with no exotics)
    - C.2.1. Decomposition distributes over addition
    - C.2.2. Decomposition commutes with filtering charges
    - C.2.3. Decomposition preserves the charge map
    - C.2.4. Decomposition preserves the charges
    - C.2.5. Decomposition preserves the reduction
    - C.2.6. Fluxes of the decomposition of a `FiveQuanta`
- D. Lifting charges to `FiveQuanta`
  - D.1. `liftCharge c`: multiset of five-quanta for a finite set of charges `c` with no exotics
  - D.2. FiveQuanta in `liftCharge c` have a finite set of charges `c`
  - D.3. FiveQuanta in `liftCharge c` have no duplicate charges
  - D.4. Membership in `liftCharge c` iff is reduction of `FiveQuanta` with given fluxes
  - D.5. FiveQuanta in `liftCharge c` do not have zero fluxes
  - D.6. FiveQuanta in `liftCharge c` have no exotics
  - D.7. Membership in `liftCharge c` iff have no exotics, no zero fluxes, and charges `c`
  - D.8. `liftCharge c` is preserved under a map if reduced
- E. Anomaly cancellation coefficients
  - E.1. Anomaly coefficients of a `FiveQuanta`
  - E.2. Anomaly coefficients under a map
  - E.3. Anomaly coefficients is preserved under `reduce`

## iv. References

A reference for the anomaly cancellation conditions is arXiv:1401.5084.

-/
namespace FTheory

namespace SU5
open SU5

/-!

## A. The definition of `FiveQuanta`

-/

/-- The quanta of 5-bar representations corresponding to a multiset of
  `(q, M, N)` for each particle. `(M, N)` are defined in the `FluxesFive` module. -/
abbrev FiveQuanta (𝓩 : Type := ℤ) : Type := Multiset (𝓩 × Fluxes)

namespace FiveQuanta

variable {𝓩 : Type}

/-!

### A.1. The map to underlying fluxes

-/

/-- The underlying `FluxesFive` from a `FiveQuanta`. -/
def toFluxesFive (x : FiveQuanta 𝓩) : FluxesFive := x.map Prod.snd

/-!

### A.2. The map to underlying charges

-/

/-- The underlying Multiset charges from a `FiveQuanta`. -/
def toCharges (x : FiveQuanta 𝓩) : Multiset 𝓩 := x.map Prod.fst

/-!

### A.3. The map from charges to fluxes

-/

/-- The map which takes a charge to the overall flux it
  corresponds to in a `FiveQuanta`. -/
def toChargeMap [DecidableEq 𝓩] (x : FiveQuanta 𝓩) : 𝓩 → Fluxes :=
  fun z => ((x.filter fun p => p.1 = z).map Prod.snd).sum

lemma toChargeMap_of_not_mem [DecidableEq 𝓩] (x : FiveQuanta 𝓩) {z : 𝓩} (h : z ∉ x.toCharges) :
    x.toChargeMap z = 0 := by
  simp [toChargeMap]
  have hl : (Multiset.filter (fun p => p.1 = z) x) = 0 := by
    simp only [Multiset.filter_eq_nil, Prod.forall]
    intro a b f
    by_contra hn
    subst hn
    simp [toCharges] at h
    exact h b f
  rw [hl]
  simp

/-!

## B. The reduction of a `FiveQuanta`

-/

section reduce

variable [DecidableEq 𝓩]

/-- The `reduce` of `FiveQuanta` is a new `FiveQuanta` with all the fluxes
  corresponding to the same charge (i.e. representation) added together. -/
def reduce (x : FiveQuanta 𝓩) : FiveQuanta 𝓩 :=
  x.toCharges.dedup.map fun q5 => (q5, ((x.filter (fun f => f.1 = q5)).map (fun y => y.2)).sum)

/-!

### B.1. The reduced `FiveQuanta` has no duplicate elements

-/

lemma reduce_nodup (x : FiveQuanta 𝓩) : x.reduce.Nodup := by
  simp [reduce, toCharges]
  refine Multiset.Nodup.map ?_ ?_
  · intro q1 q2 h
    simp at h
    exact h.1
  · exact Multiset.nodup_dedup (Multiset.map Prod.fst x)

@[simp]
lemma reduce_dedup (x : FiveQuanta 𝓩) : x.reduce.dedup = x.reduce :=
  Multiset.Nodup.dedup x.reduce_nodup

/-!

### B.2. The underlying charges of the reduced `FiveQuanta` are the deduped charges

-/

lemma reduce_toCharges (x : FiveQuanta 𝓩) : x.reduce.toCharges = x.toCharges.dedup := by
  simp [reduce, toCharges]

/-!

### B.3. Membership condition on the reduced `FiveQuanta`

-/

lemma mem_reduce_iff (x : FiveQuanta 𝓩) (p : 𝓩 × Fluxes) :
    p ∈ x.reduce ↔ p.1 ∈ x.toCharges ∧
      p.2 = ((x.filter (fun f => f.1 = p.1)).map (fun y => y.2)).sum := by
  simp [reduce]
  constructor
  · intro h
    obtain ⟨q, h1, rfl⟩ := h
    simp_all
  · simp
    intro h1 h2
    use p.1
    simp_all
    rw [← h2]

/-!

### B.4. Filter of the reduced `FiveQuanta` by a charge

-/

lemma reduce_filter (x : FiveQuanta 𝓩) (q : 𝓩) (h : q ∈ x.toCharges) :
    x.reduce.filter (fun f => f.1 = q) =
    {(q, ((x.filter (fun f => f.1 = q)).map (fun y => y.2)).sum)} := by
  simp [reduce]
  rw [Multiset.filter_map]
  simp only [Function.comp_apply]
  have hx : (Multiset.filter (fun x => x = q) x.toCharges.dedup) = {q} := by
    refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
    · refine Multiset.Nodup.filter (fun x => x = q) ?_
      exact Multiset.nodup_dedup x.toCharges
    · exact Multiset.nodup_singleton q
    intro a
    simp only [Multiset.mem_filter, Multiset.mem_dedup, Multiset.mem_singleton,
      and_iff_right_iff_imp]
    intro h'
    subst h'
    exact h
  rw [hx]
  simp

/-!

### B.5. The reduction is idempotent

-/

@[simp]
lemma reduce_reduce (x : FiveQuanta 𝓩) :
    x.reduce.reduce = x.reduce := by
  refine Multiset.Nodup.toFinset_inj ?_ ?_ ?_
  · exact reduce_nodup x.reduce
  · exact reduce_nodup x
  ext p
  simp only [Multiset.mem_toFinset]
  rw [mem_reduce_iff, reduce_toCharges, mem_reduce_iff]
  simp only [Multiset.mem_dedup, and_congr_right_iff]
  intro hp
  have h1 (a b c : Fluxes) (h : b = c) : a = b ↔ a = c := by subst h; rfl
  apply h1
  rw [reduce_filter]
  simp only [Multiset.map_singleton, Multiset.sum_singleton]
  exact hp

/-!

### B.6. Preservation of certain sums under reduction

-/

lemma reduce_sum_eq_sum_toCharges {M} [AddCommMonoid M] (x : FiveQuanta 𝓩) (f : 𝓩 → Fluxes →+ M) :
    (x.reduce.map fun (q5, x) => f q5 x).sum = (x.map fun (q5, x) => f q5 x).sum := by
  calc _
      _ = ∑ q5 ∈ x.toCharges.toFinset,
          f q5 ((x.filter (fun f => f.1 = q5)).map (fun y => y.2)).sum := by
        rw [reduce]
        simp [Finset.sum]
      _ = ∑ q5 ∈ x.toCharges.toFinset,
          (((x.filter (fun f => f.1 = q5)).map (fun y => f q5 y.2))).sum := by
        congr
        funext q5
        rw [AddMonoidHom.map_multiset_sum, Multiset.map_map]
        rfl
      _ = (x.toCharges.dedup.bind fun q5 =>
          ((x.filter (fun f => f.1 = q5)).map (fun y => f q5 y.2))).sum := by
        rw [Multiset.sum_bind]
        simp [Finset.sum]
      _ = (((x.toCharges.dedup.bind fun q5 =>
          ((x.filter (fun f => f.1 = q5)))).map (fun y => f y.1 y.2))).sum := by
        congr
        rw [Multiset.map_bind]
        congr
        funext q5
        refine Multiset.map_congr rfl ?_
        intro y hy
        simp at hy
        rw [hy.2]
      _ = ((x.map (fun y => f y.1 y.2))).sum := by
        congr
        apply Multiset.ext.mpr
        intro p
        trans ((x.map Prod.fst).dedup.map (fun y => if p.1 = y then x.count p else 0)).sum
        · rw [@Multiset.count_bind]
          congr
          funext q5
          rw [Multiset.count_filter]
        by_cases h_mem : p.1 ∈ x.map Prod.fst
        · have h_mem_dedup : p.1 ∈ (x.map Prod.fst).dedup := by rwa [Multiset.mem_dedup]
          rw [Multiset.sum_map_eq_nsmul_single p.1]
          simp only [↓reduceIte, smul_eq_mul]
          have h_count_one : Multiset.count p.1 (Multiset.map Prod.fst x).dedup = 1 := by
            refine Multiset.count_eq_one_of_mem ?_ h_mem_dedup
            exact Multiset.nodup_dedup (Multiset.map Prod.fst x)
          simp [h_count_one]
          intro q5' h h2
          simp_all [eq_comm]
        · rw [Multiset.sum_eq_zero]
          refine Eq.symm (Multiset.count_eq_zero_of_notMem ?_)
          intro h
          have h_mem : p.1 ∈ Multiset.map Prod.fst x := by
            simp_all
          (expose_names; exact h_mem_1 h_mem)
          intro p' hp
          simp at hp
          obtain ⟨q5', ⟨f1, hf⟩, hp'⟩ := hp
          by_cases h_eq : p.1 = q5'
          · simp_all
          · simp_all

/-!

### B.7. Reduction does nothing if no duplicate charges

-/

lemma reduce_eq_self_of_ofCharges_nodup (x : FiveQuanta 𝓩) (h : x.toCharges.Nodup) :
    x.reduce = x := by
  rw [reduce, Multiset.Nodup.dedup h]
  simp [toCharges]
  conv_rhs => rw [← Multiset.map_id x]
  apply Multiset.map_congr rfl
  intro p hp
  simp only [id_eq]
  have x_noDup : x.Nodup := Multiset.Nodup.of_map Prod.fst h
  suffices (Multiset.filter (fun f => f.1 = p.1) x) = {p} by simp [this]
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact Multiset.Nodup.filter (fun f => f.1 = p.1) x_noDup
  · exact Multiset.nodup_singleton p
  intro p'
  simp only [Multiset.mem_filter, Multiset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    simp [toCharges] at h
    rw [propext (Multiset.nodup_map_iff_inj_on x_noDup)] at h
    apply h
    · exact h1
    · exact hp
    · exact h2
  · rintro ⟨rfl⟩
    simp_all

/-!

### B.8. The charge map is preserved by reduction

-/

lemma reduce_toChargeMap_eq (x : FiveQuanta 𝓩) :
    x.reduce.toChargeMap = x.toChargeMap := by
  funext q
  by_cases h : q ∈ x.toCharges
  · rw [toChargeMap, reduce_filter]
    · simp
      rfl
    · exact h
  · rw [toChargeMap_of_not_mem, toChargeMap_of_not_mem]
    · exact h
    · rw [reduce_toCharges]
      simp only [Multiset.mem_dedup]
      exact h

/-!

### B.9. A fluxes in the reduced `FiveQuanta` is a sum of fluxes in the original `FiveQuanta`

-/

lemma mem_powerset_sum_of_mem_reduce_toFluxesFive {F : FiveQuanta 𝓩}
    {f : Fluxes} (hf : f ∈ F.reduce.toFluxesFive) :
    f ∈ (Multiset.powerset F.toFluxesFive).map fun s => s.sum := by
  rw [toFluxesFive, Multiset.mem_map] at hf
  obtain ⟨⟨q, f⟩, hp, rfl⟩ := hf
  rw [mem_reduce_iff] at hp
  simp at hp
  obtain ⟨hq, rfl⟩ := hp
  simp only [Multiset.mem_map, Multiset.mem_powerset]
  use (Multiset.map (fun x => x.2) (Multiset.filter (fun x => x.1 = q) F))
  simp only [and_true]
  rw [toFluxesFive]
  refine Multiset.map_le_map ?_
  exact Multiset.filter_le (fun x => x.1 = q) F

lemma mem_powerset_sum_of_mem_reduce_toFluxesFive_filter {F : FiveQuanta 𝓩}
    {f : Fluxes} (hf : f ∈ F.reduce.toFluxesFive) :
    f ∈ (F.toFluxesFive.powerset.filter fun s => s ≠ ∅).map fun s => s.sum := by
  rw [toFluxesFive, Multiset.mem_map] at hf
  obtain ⟨⟨q, f⟩, hp, rfl⟩ := hf
  rw [mem_reduce_iff] at hp
  simp at hp
  obtain ⟨hq, rfl⟩ := hp
  simp only [Multiset.mem_map]
  use (Multiset.map (fun x => x.2) (Multiset.filter (fun x => x.1 = q) F))
  simp only [and_true]
  rw [Multiset.mem_filter]
  apply And.intro
  simp only [Multiset.mem_powerset]
  rw [toFluxesFive]
  refine Multiset.map_le_map ?_
  exact Multiset.filter_le (fun x => x.1 = q) F
  simp [Multiset.empty_eq_zero, ne_eq, Multiset.map_eq_zero, Multiset.filter_eq_nil,
    Prod.forall, not_forall, Decidable.not_not]
  rw [toCharges, Multiset.mem_map] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  use a.2

/-!

### B.10. No exotics condition on the reduced `FiveQuanta`

-/

/-!

#### B.10.1. Number of chiral `L`

-/

lemma reduce_numChiralL_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numChiralL = 3 := by
  have hE : F.toFluxesFive.NoExotics := by
    rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics] at hx
    exact hx.1
  rw [← hE.1, FluxesFive.numChiralL, FluxesFive.numChiralL, FluxesFive.chiralIndicesOfL]
  trans (F.reduce.toFluxesFive.map (fun f => f.M + f.N)).sum
  · congr
    refine Multiset.filter_eq_self.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
    generalize F.toFluxesFive = G at *
    revert f
    revert G
    decide
  · let f : 𝓩 → Fluxes →+ ℤ := fun q5 => ⟨⟨fun x => x.M + x.N, by simp⟩,
      fun x y => by simp [add_add_add_comm]⟩
    rw [toFluxesFive, Multiset.map_map]
    change (F.reduce.map (fun (q5, x) => f q5 x)).sum = _
    rw [reduce_sum_eq_sum_toCharges]
    congr
    rw [FluxesFive.chiralIndicesOfL, toFluxesFive, Multiset.map_map]
    refine (Multiset.filter_eq_self.mpr ?_).symm
    have h' : Multiset.map (fun x => (f x.1) x.2) F = F.toFluxesFive.map (fun f => f.M + f.N) := by
      simp [toFluxesFive, Multiset.map_map]
      rfl
    rw [h']
    clear h'
    generalize F.toFluxesFive = G at *
    revert G
    decide

/-!

#### B.10.2. Number of anti-chiral `L`

-/

lemma reduce_numAntiChiralL_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numAntiChiralL = 0 := by
  rw [FluxesFive.numAntiChiralL, FluxesFive.chiralIndicesOfL]
  have hx : (Multiset.filter (fun x => x < 0) (F.reduce.toFluxesFive.map (fun f => f.M + f.N)))
      = 0 := by
    refine Multiset.filter_eq_nil.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
    generalize F.toFluxesFive = G at *
    revert f
    revert G
    decide
  rw [hx]
  rfl

/-!

#### B.10.3. Number of chiral `D`

-/

lemma reduce_numChiralD_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numChiralD = 3 := by
  have hE : F.toFluxesFive.NoExotics := by
    rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics] at hx
    exact hx.1
  rw [← hE.2.2.1, FluxesFive.numChiralD, FluxesFive.numChiralD, FluxesFive.chiralIndicesOfD]
  trans (F.reduce.toFluxesFive.map (fun f => f.M)).sum
  · congr
    refine Multiset.filter_eq_self.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
    generalize F.toFluxesFive = G at *
    revert f
    revert G
    decide
  · let f : 𝓩 → Fluxes →+ ℤ := fun q5 => ⟨⟨fun x => x.M, by simp⟩,
      fun x y => by simp⟩
    rw [toFluxesFive, Multiset.map_map]
    change (F.reduce.map (fun (q5, x) => f q5 x)).sum = _
    rw [reduce_sum_eq_sum_toCharges]
    congr
    rw [FluxesFive.chiralIndicesOfD, toFluxesFive, Multiset.map_map]
    refine (Multiset.filter_eq_self.mpr ?_).symm
    have h' : Multiset.map (fun x => (f x.1) x.2) F = F.toFluxesFive.map (fun f => f.M) := by
      simp [toFluxesFive, Multiset.map_map]
      rfl
    rw [h']
    clear h'
    generalize F.toFluxesFive = G at *
    revert G
    decide

/-!

#### B.10.4. Number of anti-chiral `D`

-/

lemma reduce_numAntiChiralD_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numAntiChiralD = 0 := by
  rw [FluxesFive.numAntiChiralD, FluxesFive.chiralIndicesOfD]
  have hx : (Multiset.filter (fun x => x < 0) (F.reduce.toFluxesFive.map (fun f => f.M)))
      = 0 := by
    refine Multiset.filter_eq_nil.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
    generalize F.toFluxesFive = G at *
    revert f
    revert G
    decide
  rw [hx]
  rfl

/-!

#### B.10.5. The `NoExotics` condition on the reduced `FiveQuanta`

-/
lemma reduce_noExotics_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.NoExotics := by
  rw [FluxesFive.NoExotics]
  rw [reduce_numChiralL_of_mem_elemsNoExotics hx, reduce_numAntiChiralL_of_mem_elemsNoExotics hx,
    reduce_numChiralD_of_mem_elemsNoExotics hx, reduce_numAntiChiralD_of_mem_elemsNoExotics hx]
  simp

/-!

### B.11. Reduce member of `FluxesFive.elemsNoExotics`

-/

lemma reduce_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive ∈ FluxesFive.elemsNoExotics := by
  rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics]
  apply And.intro
  · exact reduce_noExotics_of_mem_elemsNoExotics hx
  · intro h
    replace h := mem_powerset_sum_of_mem_reduce_toFluxesFive_filter h
    generalize F.toFluxesFive = G at *
    revert G
    decide

end reduce

/-!

## C. Decomposition of a `FiveQuanta` into basic fluxes

-/

/-!

### C.1. Decomposition of fluxes

-/

/-- The decomposition of a flux into `⟨1, -1⟩` and `⟨0, 1⟩`. -/
def decomposeFluxes (f : Fluxes) : Multiset Fluxes :=
  Multiset.replicate (Int.natAbs f.M) ⟨1, -1⟩ +
  Multiset.replicate (Int.natAbs (f.M + f.N)) ⟨0, 1⟩

lemma decomposeFluxes_sum_of_noExotics (f : Fluxes) (hf : ∃ F ∈ FluxesFive.elemsNoExotics, f ∈ F) :
    (decomposeFluxes f).sum = f := by
  obtain ⟨F, hF, hfF⟩ := hf
  revert f
  revert F
  decide

/-!

### C.2. Decomposition of a `FiveQuanta` (with no exotics)

-/

/-- The decomposition of a `FiveQuanta` into a `FiveQuanta` which has the
  same `reduce` by has fluxes `⟨1, -1⟩` and `⟨0,1⟩` only. -/
def decompose (x : FiveQuanta 𝓩) : FiveQuanta 𝓩 :=
  x.bind fun p => (decomposeFluxes p.2).map fun f => (p.1, f)

/-!

#### C.2.1. Decomposition distributes over addition

-/

lemma decompose_add (x y : FiveQuanta 𝓩) :
    (x + y).decompose = x.decompose + y.decompose := by
  simp [decompose]

/-!

#### C.2.2. Decomposition commutes with filtering charges

-/

lemma decompose_filter_charge [DecidableEq 𝓩] (x : FiveQuanta 𝓩) (q : 𝓩) :
    (x.decompose).filter (fun p => p.1 = q) =
    decompose (x.filter (fun p => p.1 = q)) := by
  rw [decompose]
  revert x
  apply Multiset.induction
  · simp [decompose]
  · intro a x ih
    simp only [Multiset.cons_bind, Multiset.filter_add]
    rw [Multiset.filter_cons, decompose_add, ih]
    congr
    match a with
    | (q', f) =>
    simp [decomposeFluxes]
    by_cases h : q' = q
    · subst h
      simp [decompose, decomposeFluxes]
      congr
      all_goals
      · refine Multiset.filter_eq_self.mpr ?_
        intro a ha
        simp [Multiset.mem_replicate] at ha
        rw [ha.2]
    · simp [h, decompose]
      apply And.intro
      all_goals
      · intro a b h
        simp [Multiset.mem_replicate] at h
        simp_all

/-!

#### C.2.3. Decomposition preserves the charge map

-/

lemma decompose_toChargeMap [DecidableEq 𝓩] (x : FiveQuanta 𝓩)
    (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    x.decompose.toChargeMap = x.toChargeMap := by
  ext q
  rw [toChargeMap, decompose_filter_charge]
  simp [decompose]
  rw [Multiset.map_bind]
  simp only [Multiset.map_map, Function.comp_apply, Multiset.map_id', Multiset.sum_bind]
  rw [toChargeMap]
  congr 1
  apply Multiset.map_congr
  · rfl
  intro a ha
  apply decomposeFluxes_sum_of_noExotics
  use x.toFluxesFive
  simp_all [toFluxesFive]
  use a.1
  exact ha.1

/-!

#### C.2.4. Decomposition preserves the charges

-/

lemma decompose_toCharges_dedup [DecidableEq 𝓩] (x : FiveQuanta 𝓩)
    (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    x.decompose.toCharges.dedup = x.toCharges.dedup := by
  refine Multiset.dedup_ext.mpr ?_
  intro q
  simp [decompose, toCharges, -existsAndEq]
  constructor
  · rintro ⟨a, b, c, h1, h2, rfl⟩
    exact ⟨c, h1⟩
  · rintro ⟨c, h1⟩
    have hn : (decomposeFluxes c) ≠ 0 := by
      have c_mem_f : c ∈ x.toFluxesFive := by
        simp [toFluxesFive]
        use q
      generalize x.toFluxesFive = F at *
      clear h1
      revert c
      revert F
      decide
    apply Multiset.exists_mem_of_ne_zero at hn
    obtain ⟨c', h⟩ := hn
    use c', q, c

/-!

#### C.2.5. Decomposition preserves the reduction

-/

lemma decompose_reduce (x : FiveQuanta 𝓩) [DecidableEq 𝓩]
    (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    x.decompose.reduce = x.reduce := by
  rw [reduce, reduce]
  apply Multiset.map_congr
  · rw [decompose_toCharges_dedup x hx]
  · intro q hx'
    simp only [Prod.mk.injEq, true_and]
    change x.decompose.toChargeMap q = x.toChargeMap q
    rw [decompose_toChargeMap x hx]

/-!

#### C.2.6. Fluxes of the decomposition of a `FiveQuanta`

-/

lemma decompose_toFluxesFive (x : FiveQuanta 𝓩)
    (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    x.decompose.toFluxesFive = {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩} := by
  rw [toFluxesFive, decompose]
  rw [Multiset.map_bind]
  simp only [Multiset.map_map, Function.comp_apply, Multiset.map_id', Int.reduceNeg,
    Multiset.insert_eq_cons]
  trans (Multiset.bind x.toFluxesFive fun a => decomposeFluxes a)
  · rw [toFluxesFive, Multiset.bind_map]
  · generalize x.toFluxesFive = F at *
    revert F
    decide

/-!

## D. Lifting charges to `FiveQuanta`

-/

section ofChargesExpand

open SuperSymmetry.SU5.ChargeSpectrum

variable [DecidableEq 𝓩]

/-!

### D.1. `liftCharge c`: multiset of five-quanta for a finite set of charges `c` with no exotics

This is an efficient definition, we will later show that it gives the correct answer

-/

/-- Given a finite set of charges `c` the `FiveQuanta`
  which do not have exotics, duplicate charges or zero fluxes, which map down to `c`. -/
def liftCharge (c : Finset 𝓩) : Multiset (FiveQuanta 𝓩) :=
  /- The multisets of cardinality 3 containing 3 elements of `c`. -/
  let S53 : Multiset (Multiset 𝓩) := toMultisetsThree c
  /- Pairs of multisets (s1, s2) such that s1 and s2 are cardinality of `3` containing
    elements of `c` and that all elements of `c` are in `s1 + s2`. -/
  let S5p : Multiset (Multiset 𝓩 × Multiset 𝓩) :=
    (S53 ×ˢ S53).filter fun (s1, s2) => c.val ≤ s1 + s2
  let Fp : Multiset (FiveQuanta 𝓩) :=
    S5p.map (fun y => y.1.map (fun z => (z, ⟨1, -1⟩)) + y.2.map (fun z => (z, ⟨0, 1⟩)))
  Fp.map reduce

/-!

### D.2. FiveQuanta in `liftCharge c` have a finite set of charges `c`

-/

lemma toCharges_toFinset_of_mem_liftCharge (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h : x ∈ liftCharge c) : x.toCharges.toFinset = c := by
  simp [liftCharge] at h
  obtain ⟨s1, s2, ⟨⟨⟨s1_subset, s1_card⟩, ⟨s2_subset, s2_card⟩⟩, hsum⟩, rfl⟩ := h
  rw [← Multiset.toFinset_dedup, reduce_toCharges]
  simp only [Int.reduceNeg, Multiset.dedup_idem, Multiset.toFinset_dedup]
  simp [toCharges]
  trans (s1 + s2).toFinset
  · exact Eq.symm (Multiset.toFinset_add s1 s2)
  ext a
  simp only [Multiset.toFinset_add, Finset.mem_union, Multiset.mem_toFinset]
  constructor
  · intro hr
    rcases hr with hr | hr
    · apply s1_subset
      simpa using hr
    · apply s2_subset
      simpa using hr
  · intro hr
    simpa using Multiset.mem_of_le hsum hr

/-!

### D.3. FiveQuanta in `liftCharge c` have no duplicate charges

-/

lemma toCharges_nodup_of_mem_liftCharge (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h : x ∈ liftCharge c) : x.toCharges.Nodup := by
  rw [liftCharge, Multiset.mem_map] at h
  obtain ⟨x, h, rfl⟩ := h
  rw [reduce_toCharges]
  exact Multiset.nodup_dedup x.toCharges

/-!

### D.4. Membership in `liftCharge c` iff is reduction of `FiveQuanta` with given fluxes

-/

lemma exists_toCharges_toFluxesFive_of_mem_liftCharge (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h : x ∈ liftCharge c) :
    ∃ a : FiveQuanta 𝓩, a.reduce = x ∧ a.toCharges.toFinset = c ∧ a.toFluxesFive =
      {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩} := by
  have h' := h
  rw [liftCharge, Multiset.mem_map] at h
  obtain ⟨a, h, rfl⟩ := h
  use a
  simp only [Int.reduceNeg, Multiset.insert_eq_cons, true_and]
  apply And.intro
  · trans a.toCharges.dedup.toFinset
    · simp
    rw [← reduce_toCharges]
    exact toCharges_toFinset_of_mem_liftCharge c h'
  · simp at h
    obtain ⟨s1, s2, ⟨⟨⟨s1_subset, s1_card⟩, ⟨s2_subset, s2_card⟩⟩, hsum⟩, rfl⟩ := h
    simp [toFluxesFive, s1_card, s2_card]
    decide

lemma mem_liftCharge_of_exists_toCharges_toFluxesFive (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h : ∃ a : FiveQuanta 𝓩, a.reduce = x ∧ a.toCharges.toFinset = c ∧ a.toFluxesFive =
      {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩}) :
    x ∈ liftCharge c := by
  obtain ⟨x, rfl, h, h2⟩ := h
  rw [liftCharge, Multiset.mem_map]
  use x
  simp only [Int.reduceNeg, Multiset.mem_map, Multiset.mem_filter, Multiset.mem_product,
    mem_toMultisetsThree_iff, Prod.exists, and_true]
  let s1 := (x.filter (fun y => y.2 = ⟨1, -1⟩)).map Prod.fst
  let s2 := (x.filter (fun y => y.2 = ⟨0, 1⟩)).map Prod.fst
  use s1, s2
  have hx : Multiset.filter (fun y => y.2 = ⟨0, 1⟩) x
        = Multiset.filter (fun y => ¬ y.2 = ⟨1, -1⟩) x := by
    refine Multiset.filter_congr ?_
    intro p hp
    have h1 : p.2 ∈ x.toFluxesFive := by simp [toFluxesFive]; use p.1
    rw [h2] at h1
    simp_all
    rcases h1 with hp | hp
    · simp [hp]
    · simp [hp]
  refine ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
  · simp [s1, ← h, toCharges]
  · simp [s1]
    trans (Multiset.filter (fun y => y = ⟨1, -1⟩) (x.toFluxesFive)).card
    · rw [toFluxesFive, Multiset.filter_map]
      simp
    rw [h2]
    decide
  · simp [s2, ← h, toCharges]
  · simp [s2]
    trans (Multiset.filter (fun y => y = ⟨0, 1⟩) (x.toFluxesFive)).card
    · rw [toFluxesFive, Multiset.filter_map]
      simp
    rw [h2]
    decide
  · rw [← h]
    simp [s1, s2, toCharges]
    rw [← Multiset.map_add]
    refine (Multiset.le_iff_subset (Multiset.nodup_dedup (Multiset.map Prod.fst x))).mpr ?_
    simp only [Multiset.dedup_subset']
    refine Multiset.map_subset_map ?_
    rw [hx, Multiset.filter_add_not]
    exact fun ⦃a⦄ a => a
  · simp [s1, s2]
    have h1 : Multiset.map (fun x => (x.1, ⟨1, -1⟩)) (Multiset.filter (fun y => y.2 = ⟨1, -1⟩) x)
        = (Multiset.filter (fun y => y.2 = ⟨1, -1⟩) x) := by
      trans Multiset.map (fun x => x) (Multiset.filter (fun y => y.2 = ⟨1, -1⟩) x)
      · apply Multiset.map_congr
        · rfl
        · intro y hx
          simp at hx
          rw [← hx.2]
      simp
    have h2 : Multiset.map (fun x => (x.1, ⟨0, 1⟩)) (Multiset.filter (fun y => y.2 = ⟨0, 1⟩) x)
        = (Multiset.filter (fun y => y.2 = ⟨0, 1⟩) x) := by
      trans Multiset.map (fun x => x) (Multiset.filter (fun y => y.2 = ⟨0, 1⟩) x)
      · apply Multiset.map_congr
        · rfl
        · intro y hx
          simp at hx
          rw [← hx.2]
      simp
    rw [h1, h2, hx]
    exact Multiset.filter_add_not (fun y => y.2 = ⟨1, -1⟩) x

lemma mem_liftCharge_iff_exists (c : Finset 𝓩) {x : FiveQuanta 𝓩} :
    x ∈ liftCharge c ↔ ∃ a : FiveQuanta 𝓩, a.reduce = x ∧
      a.toCharges.toFinset = c ∧ a.toFluxesFive =
      {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩} :=
  ⟨exists_toCharges_toFluxesFive_of_mem_liftCharge c,
    mem_liftCharge_of_exists_toCharges_toFluxesFive c⟩

/-!

### D.5. FiveQuanta in `liftCharge c` do not have zero fluxes

-/

lemma hasNoZero_of_mem_liftCharge (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h : x ∈ liftCharge c) : x.toFluxesFive.HasNoZero := by
  rw [mem_liftCharge_iff_exists] at h
  obtain ⟨x, rfl, h1, h2⟩ := h
  intro hf
  have hx := mem_powerset_sum_of_mem_reduce_toFluxesFive_filter hf
  rw [h2] at hx
  revert hx
  decide

/-!

### D.6. FiveQuanta in `liftCharge c` have no exotics

-/

lemma noExotics_of_mem_liftCharge (c : Finset 𝓩) (F : FiveQuanta 𝓩)
    (h : F ∈ liftCharge c) :
    F.toFluxesFive.NoExotics := by
  rw [mem_liftCharge_iff_exists] at h
  obtain ⟨x, rfl, h1, h2⟩ := h
  apply reduce_noExotics_of_mem_elemsNoExotics
  rw [h2]
  decide

/-!

### D.7. Membership in `liftCharge c` iff have no exotics, no zero fluxes, and charges `c`

-/

lemma mem_liftCharge_of_mem_noExotics_hasNoZero (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h1 : x.toFluxesFive.NoExotics) (h2 : x.toFluxesFive.HasNoZero)
    (h3 : x.toCharges.toFinset = c) (h4 : x.toCharges.Nodup) :
    x ∈ liftCharge c := by
  have hf : x.toFluxesFive ∈ FluxesFive.elemsNoExotics := by
    rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics]
    simp_all
    exact h2
  rw [mem_liftCharge_iff_exists]
  use x.decompose
  apply And.intro
  · rw [decompose_reduce x hf]
    exact reduce_eq_self_of_ofCharges_nodup x h4
  · constructor
    · trans x.decompose.toCharges.dedup.toFinset
      · simp
      · rw [decompose_toCharges_dedup x hf, ← h3]
        simp
    · rw [decompose_toFluxesFive x hf]

lemma mem_liftCharge_iff (c : Finset 𝓩) (x : FiveQuanta 𝓩) :
    x ∈ liftCharge c ↔ x.toFluxesFive ∈ FluxesFive.elemsNoExotics
      ∧ x.toCharges.toFinset = c ∧ x.toCharges.Nodup := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics]
      refine ⟨?_, ?_⟩
      · exact noExotics_of_mem_liftCharge c x h
      · exact hasNoZero_of_mem_liftCharge c h
    · exact toCharges_toFinset_of_mem_liftCharge c h
    · exact toCharges_nodup_of_mem_liftCharge c h
  · intro ⟨h1, h2, h3⟩
    rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics] at h1
    exact mem_liftCharge_of_mem_noExotics_hasNoZero c h1.1 h1.2 h2 h3

/-!

### D.8. `liftCharge c` is preserved under a map if reduced

-/

lemma map_liftCharge {𝓩 𝓩1 : Type}[DecidableEq 𝓩] [DecidableEq 𝓩1] [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (c : Finset 𝓩) (F : FiveQuanta 𝓩) (h : F ∈ liftCharge c) :
    FiveQuanta.reduce (F.map fun y => (f y.1, y.2)) ∈ liftCharge (c.image f) := by
  rw [mem_liftCharge_iff] at h ⊢
  refine ⟨?_, ?_, ?_⟩
  · apply reduce_mem_elemsNoExotics
    simpa [toFluxesFive, Multiset.map_map] using h.1
  · rw [reduce_toCharges]
    simp [← h.2.1, ← Multiset.toFinset_map, toCharges]
  · rw [reduce_toCharges]
    exact Multiset.nodup_dedup (toCharges (Multiset.map (fun y => (f y.1, y.2)) F))

end ofChargesExpand

/-!

## E. Anomaly cancellation coefficients

-/

section ACCs

variable [CommRing 𝓩]

/-!

### E.1. Anomaly coefficients of a `FiveQuanta`

-/

/--
  The anomaly coefficient of a `FiveQuanta` is given by the pair of integers:
  `(∑ᵢ qᵢ Nᵢ, ∑ᵢ qᵢ² Nᵢ)`.

  The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084.
  The second component is for the mixed U(1)Y-U(1)-U(1) gauge anomaly,
  see equation (23) of arXiv:1401.5084.
-/
def anomalyCoefficient (F : FiveQuanta 𝓩) : 𝓩 × 𝓩 :=
  ((F.map fun x => x.2.2 • x.1).sum, (F.map fun x => x.2.2 • (x.1 * x.1)).sum)

/-!

### E.2. Anomaly coefficients under a map

-/

@[simp]
lemma anomalyCoefficient_of_map {𝓩 𝓩1 : Type} [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (F : FiveQuanta 𝓩) :
    FiveQuanta.anomalyCoefficient (F.map fun y => (f y.1, y.2) : FiveQuanta 𝓩1) =
    (f.prodMap f) F.anomalyCoefficient := by
  simp [FiveQuanta.anomalyCoefficient, map_multiset_sum, Multiset.map_map]

/-!

### E.3. Anomaly coefficients is preserved under `reduce`

-/

lemma anomalyCoefficient_of_reduce (F : FiveQuanta 𝓩) [DecidableEq 𝓩] :
    F.reduce.anomalyCoefficient = F.anomalyCoefficient := by
  simp [anomalyCoefficient]
  constructor
  · let f : 𝓩 → Fluxes →+ 𝓩 := fun q5 => {
      toFun := fun x => x.2 • q5
      map_zero' := by simp
      map_add' := by
        intros x y
        simp [add_mul] }
    simpa [f] using reduce_sum_eq_sum_toCharges F f
  · let f : 𝓩 → Fluxes →+ 𝓩 := fun q5 => {
      toFun := fun x => x.2 • (q5 * q5)
      map_zero' := by simp
      map_add' := by
        intros x y
        simp [add_mul] }
    simpa [f] using reduce_sum_eq_sum_toCharges F f

end ACCs

end FiveQuanta

end SU5
end FTheory
