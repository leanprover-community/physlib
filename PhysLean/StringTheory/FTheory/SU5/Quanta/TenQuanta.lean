/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.OfFinset
import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.Completeness
/-!

# Quanta of 10d representations

## i. Overview

The 10d representations of the `SU(5)×U(1)` carry
the quantum numbers of their `U(1)` charges and their fluxes.

In this module we define the data structure for these quanta and
properties thereof.

## ii. Key results

- `TenQuanta` is the type of quanta of 10d representations.
- `TenQuanta.toFluxesTen` is the underlying `FluxesTen` of a `TenQuanta`.
- `TenQuanta.toCharges` is the underlying Multiset charges of a `TenQuanta`.
- `TenQuanta.reduce` is the reduction of a `TenQuanta` which adds together
  all the fluxes corresponding to the same charge (i.e. representation).
- `TenQuanta.liftCharges` given a charge `c` the `TenQuanta` which have
  charge `c` and no exotics or zero fluxes.
- `TenQuanta.anomalyCoefficient` is the anomaly coefficient associated with a `TenQuanta`.

## iii. Table of contents

- A. The definition of `TenQuanta`
  - A.1. The map to underlying fluxes
  - A.2. The map to underlying charges
  - A.3. The map from charges to fluxes
- B. The reduction of a `TenQuanta`
  - B.1. The reduced `TenQuanta` has no duplicate elements
  - B.2. The underlying charges of the reduced `TenQuanta` are the deduped charges
  - B.3. Membership condition on the reduced `TenQuanta`
  - B.4. Filter of the reduced `TenQuanta` by a charge
  - B.5. The reduction is idempotent
  - B.6. Preservation of certain sums under reduction
  - B.7. Reduction does nothing if no duplicate charges
  - B.8. The charge map is preserved by reduction
  - B.9. A fluxes in the reduced `TenQuanta` is a sum of fluxes in the original `TenQuanta`
  - B.10. No exotics condition on the reduced `TenQuanta`
    - B.10.1. Number of chiral `U`
    - B.10.2. Number of anti-chiral `U`
    - B.10.3. Number of chiral `Q`
    - B.10.4. Number of anti-chiral `Q`
    - B.10.5. Number of chiral `E`
    - B.10.6. Number of anti-chiral `E`
    - B.10.7. The `NoExotics` condition on the reduced `TenQuanta`
  - B.11. Reduce member of `FLuxesTen.elemsNoExotics`
- C. Decomposition of a `TenQuanta` into basic fluxes
  - C.1. Decomposition of fluxes
  - C.2. Decomposition of a `TenQuanta` (with no exotics)
    - C.2.1. Decomposition distributes over addition
    - C.2.2. Decomposition commutes with filtering charges
    - C.2.3. Decomposition preserves the charge map
    - C.2.4. Decomposition preserves the charges
    - C.2.5. Decomposition preserves the reduction
    - C.2.6. Fluxes of the decomposition of a `TenQuanta`
- D. Lifting charges to `TenQuanta`
  - D.1. `liftCharge c`: multiset of ten-quanta for a finite set of charges `c` with no exotics
  - D.2. TenQuanta in `liftCharge c` have a finite set of charges `c`
  - D.3. TenQuanta in `liftCharge c` have no duplicate charges
  - D.4. Membership in `liftCharge c` iff is reduction of `TenQuanta` with given fluxes
  - D.5. TenQuanta in `liftCharge c` do not have zero fluxes
  - D.6. TenQuanta in `liftCharge c` have no exotics
  - D.7. Membership in `liftCharge c` iff have no exotics, no zero fluxes, and charges `c`
  - D.8. `liftCharge c` is preserved under a map if reduced
- E. Anomaly cancellation coefficients
  - E.1. Anomaly coefficients of a `TenQuanta`
  - E.2. Anomaly coefficients under a map
  - E.3. Anomaly coefficients is preserved under `reduce`

## iv. References

A reference for the anomaly cancellation conditions is arXiv:1401.5084.

-/
namespace FTheory

namespace SU5
open SU5

/-!

## A. The definition of `TenQuanta`

-/

/-- The quanta of w0d representations corresponding to a multiset of
  `(q, M, N)` for each particle. `(M, N)` are defined in the `FluxesFive` module. -/
abbrev TenQuanta (𝓩 : Type := ℤ) : Type := Multiset (𝓩 × Fluxes)

namespace TenQuanta

variable {𝓩 : Type}

/-!

### A.1. The map to underlying fluxes

-/

/-- The underlying `FluxesTen` from a `TenQuanta`. -/
def toFluxesTen (x : TenQuanta 𝓩) : FluxesTen := x.map Prod.snd

/-!

### A.2. The map to underlying charges

-/

/-- The underlying Multiset charges from a `TenQuanta`. -/
def toCharges (x : TenQuanta 𝓩) : Multiset 𝓩 := x.map Prod.fst

/-!

### A.3. The map from charges to fluxes

-/

/-- The map which takes a charge to the overall flux it
  corresponds to in a `TenQuanta`. -/
def toChargeMap [DecidableEq 𝓩] (x : TenQuanta 𝓩) : 𝓩 → Fluxes :=
  fun z => ((x.filter fun p => p.1 = z).map Prod.snd).sum

lemma toChargeMap_of_not_mem [DecidableEq 𝓩] (x : TenQuanta 𝓩) {z : 𝓩} (h : z ∉ x.toCharges) :
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

## B. The reduction of a `TenQuanta`

-/

section reduce

variable [DecidableEq 𝓩]

/-- The `reduce` of `TenQuanta` is a new `TenQuanta` with all the fluxes
  corresponding to the same charge (i.e. representation) added together. -/
def reduce (x : TenQuanta 𝓩) : TenQuanta 𝓩 :=
  x.toCharges.dedup.map fun q10 => (q10, ((x.filter (fun f => f.1 = q10)).map (fun y => y.2)).sum)

/-!

### B.1. The reduced `TenQuanta` has no duplicate elements

-/

lemma reduce_nodup (x : TenQuanta 𝓩) : x.reduce.Nodup := by
  simp [reduce, toCharges]
  refine Multiset.Nodup.map ?_ ?_
  · intro q1 q2 h
    simp at h
    exact h.1
  · exact Multiset.nodup_dedup (Multiset.map Prod.fst x)

@[simp]
lemma reduce_dedup (x : TenQuanta 𝓩) : x.reduce.dedup = x.reduce :=
  Multiset.Nodup.dedup x.reduce_nodup

/-!

### B.2. The underlying charges of the reduced `TenQuanta` are the deduped charges

-/

lemma reduce_toCharges (x : TenQuanta 𝓩) : x.reduce.toCharges = x.toCharges.dedup := by
  simp [reduce, toCharges]

/-!

### B.3. Membership condition on the reduced `TenQuanta`

-/

lemma mem_reduce_iff (x : TenQuanta 𝓩) (p : 𝓩 × Fluxes) :
    p ∈ x.reduce ↔ p.1 ∈ x.toCharges ∧
      p.2 = ((x.filter (fun f => f.1 = p.1)).map (fun y => y.2)).sum := by
  simp [reduce]
  constructor
  · intro h
    obtain ⟨q, h1, rfl⟩ := h
    simp_all
  · simp only [and_imp]
    intro h1 h2
    use p.1
    simp_all
    rw [← h2]

/-!

### B.4. Filter of the reduced `TenQuanta` by a charge

-/

lemma reduce_filter (x : TenQuanta 𝓩) (q : 𝓩) (h : q ∈ x.toCharges) :
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
lemma reduce_reduce (x : TenQuanta 𝓩) :
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

lemma reduce_sum_eq_sum_toCharges {M} [AddCommMonoid M] (x : TenQuanta 𝓩) (f : 𝓩 → Fluxes →+ M) :
    (x.reduce.map fun (q, x) => f q x).sum = (x.map fun (q, x) => f q x).sum := by
  calc _
      _ = ∑ q ∈ x.toCharges.toFinset,
          f q ((x.filter (fun f => f.1 = q)).map (fun y => y.2)).sum := by
        rw [reduce]
        simp [Finset.sum]
      _ = ∑ q ∈ x.toCharges.toFinset,
          (((x.filter (fun f => f.1 = q)).map (fun y => f q y.2))).sum := by
        congr
        funext q5
        rw [AddMonoidHom.map_multiset_sum, Multiset.map_map]
        rfl
      _ = (x.toCharges.dedup.bind fun q =>
          ((x.filter (fun f => f.1 = q)).map (fun y => f q y.2))).sum := by
        rw [Multiset.sum_bind]
        simp [Finset.sum]
      _ = (((x.toCharges.dedup.bind fun q =>
          ((x.filter (fun f => f.1 = q)))).map (fun y => f y.1 y.2))).sum := by
        congr
        rw [Multiset.map_bind]
        congr
        funext q
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

lemma reduce_eq_self_of_ofCharges_nodup (x : TenQuanta 𝓩) (h : x.toCharges.Nodup) :
    x.reduce = x := by
  rw [reduce]
  rw [Multiset.Nodup.dedup h]
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

lemma reduce_toChargeMap_eq (x : TenQuanta 𝓩) :
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

### B.9. A fluxes in the reduced `TenQuanta` is a sum of fluxes in the original `TenQuanta`

-/

lemma mem_powerset_sum_of_mem_reduce_toFluxesTen {F : TenQuanta 𝓩}
    {f : Fluxes} (hf : f ∈ F.reduce.toFluxesTen) :
    f ∈ (Multiset.powerset F.toFluxesTen).map fun s => s.sum := by
  rw [toFluxesTen, Multiset.mem_map] at hf
  obtain ⟨⟨q, f⟩, hp, rfl⟩ := hf
  rw [mem_reduce_iff] at hp
  simp at hp
  obtain ⟨hq, rfl⟩ := hp
  simp only [Multiset.mem_map, Multiset.mem_powerset]
  use (Multiset.map (fun x => x.2) (Multiset.filter (fun x => x.1 = q) F))
  simp only [and_true]
  rw [toFluxesTen]
  refine Multiset.map_le_map ?_
  exact Multiset.filter_le (fun x => x.1 = q) F

lemma mem_powerset_sum_of_mem_reduce_toFluxesTen_filter {F : TenQuanta 𝓩}
    {f : Fluxes} (hf : f ∈ F.reduce.toFluxesTen) :
    f ∈ (F.toFluxesTen.powerset.filter fun s => s ≠ 0).map fun s => s.sum := by
  rw [toFluxesTen, Multiset.mem_map] at hf
  obtain ⟨⟨q, f⟩, hp, rfl⟩ := hf
  rw [mem_reduce_iff] at hp
  simp at hp
  obtain ⟨hq, rfl⟩ := hp
  simp only [Multiset.mem_map]
  use (Multiset.map (fun x => x.2) (Multiset.filter (fun x => x.1 = q) F))
  simp only [ne_eq, Multiset.mem_filter, Multiset.mem_powerset, Multiset.map_eq_zero,
    Multiset.filter_eq_nil, Prod.forall, not_forall, Decidable.not_not, and_true]
  apply And.intro
  rw [toFluxesTen]
  refine Multiset.map_le_map ?_
  exact Multiset.filter_le (fun x => x.1 = q) F
  simpa [toCharges] using hq

/-!

### B.10. No exotics condition on the reduced `TenQuanta`

-/

/-!

#### B.10.1. Number of chiral `U`

-/

lemma reduce_numChiralU_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numChiralU = 3 := by
  have hE : F.toFluxesTen.NoExotics := by
    rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics] at hx
    exact hx.1
  rw [← hE.2.2.1, FluxesTen.numChiralU, FluxesTen.numChiralU, FluxesTen.chiralIndicesOfU]
  trans (F.reduce.toFluxesTen.map (fun f => f.M - f.N)).sum
  · congr
    refine Multiset.filter_eq_self.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  · let f : 𝓩 → Fluxes →+ ℤ := fun q5 => ⟨⟨fun x => x.M - x.N, by simp⟩,
      fun x y => by simp; ring⟩
    rw [toFluxesTen, Multiset.map_map]
    change (F.reduce.map (fun (q5, x) => f q5 x)).sum = _
    rw [reduce_sum_eq_sum_toCharges]
    congr
    rw [FluxesTen.chiralIndicesOfU, toFluxesTen, Multiset.map_map]
    refine (Multiset.filter_eq_self.mpr ?_).symm
    have h' : Multiset.map (fun x => (f x.1) x.2) F = F.toFluxesTen.map (fun f => f.M - f.N) := by
      simp [toFluxesTen, Multiset.map_map]
      rfl
    rw [h']
    clear h'
    generalize F.toFluxesTen = G at *
    revert G
    decide

/-!

#### B.10.2. Number of anti-chiral `U`

-/

lemma reduce_numAntiChiralU_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numAntiChiralU = 0 := by
  rw [FluxesTen.numAntiChiralU, FluxesTen.chiralIndicesOfU]
  have hx : (Multiset.filter (fun x => x < 0) (F.reduce.toFluxesTen.map (fun f => f.M - f.N)))
      = 0 := by
    refine Multiset.filter_eq_nil.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  rw [hx]
  rfl

/-!

#### B.10.3. Number of chiral `Q`

-/

lemma reduce_numChiralQ_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numChiralQ = 3 := by
  have hE : F.toFluxesTen.NoExotics := by
    rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics] at hx
    exact hx.1
  rw [← hE.1, FluxesTen.numChiralQ, FluxesTen.numChiralQ, FluxesTen.chiralIndicesOfQ]
  trans (F.reduce.toFluxesTen.map (fun f => f.M)).sum
  · congr
    refine Multiset.filter_eq_self.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  · let f : 𝓩 → Fluxes →+ ℤ := fun q5 => ⟨⟨fun x => x.M, by simp⟩,
      fun x y => by simp⟩
    rw [toFluxesTen, Multiset.map_map]
    change (F.reduce.map (fun (q5, x) => f q5 x)).sum = _
    rw [reduce_sum_eq_sum_toCharges]
    congr
    rw [FluxesTen.chiralIndicesOfQ, toFluxesTen, Multiset.map_map]
    refine (Multiset.filter_eq_self.mpr ?_).symm
    have h' : Multiset.map (fun x => (f x.1) x.2) F = F.toFluxesTen.map (fun f => f.M) := by
      simp [toFluxesTen, Multiset.map_map]
      rfl
    rw [h']
    clear h'
    generalize F.toFluxesTen = G at *
    revert G
    decide

/-!

#### B.10.4. Number of anti-chiral `Q`

-/

lemma reduce_numAntiChiralQ_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numAntiChiralQ = 0 := by
  rw [FluxesTen.numAntiChiralQ, FluxesTen.chiralIndicesOfQ]
  have hx : (Multiset.filter (fun x => x < 0) (F.reduce.toFluxesTen.map (fun f => f.M)))
      = 0 := by
    refine Multiset.filter_eq_nil.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  rw [hx]
  rfl

/-!

#### B.10.5. Number of chiral `E`

-/

lemma reduce_numChiralE_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numChiralE = 3 := by
  have hE : F.toFluxesTen.NoExotics := by
    rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics] at hx
    exact hx.1
  rw [← hE.2.2.2.2.1, FluxesTen.numChiralE, FluxesTen.numChiralE, FluxesTen.chiralIndicesOfE]
  trans (F.reduce.toFluxesTen.map (fun f => f.M + f.N)).sum
  · congr
    refine Multiset.filter_eq_self.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  · let f : 𝓩 → Fluxes →+ ℤ := fun q5 => ⟨⟨fun x => x.M + x.N, by simp⟩,
      fun x y => by simp; ring⟩
    rw [toFluxesTen, Multiset.map_map]
    change (F.reduce.map (fun (q5, x) => f q5 x)).sum = _
    rw [reduce_sum_eq_sum_toCharges]
    congr
    rw [FluxesTen.chiralIndicesOfE, toFluxesTen, Multiset.map_map]
    refine (Multiset.filter_eq_self.mpr ?_).symm
    have h' : Multiset.map (fun x => (f x.1) x.2) F = F.toFluxesTen.map (fun f => f.M + f.N) := by
      simp [toFluxesTen, Multiset.map_map]
      rfl
    rw [h']
    clear h'
    generalize F.toFluxesTen = G at *
    revert G
    decide

/-!

#### B.10.6. Number of anti-chiral `E`

-/

lemma reduce_numAntiChiralE_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numAntiChiralE = 0 := by
  rw [FluxesTen.numAntiChiralE, FluxesTen.chiralIndicesOfE]
  have hx : (Multiset.filter (fun x => x < 0) (F.reduce.toFluxesTen.map (fun f => f.M + f.N)))
      = 0 := by
    refine Multiset.filter_eq_nil.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  rw [hx]
  rfl

/-!

#### B.10.7. The `NoExotics` condition on the reduced `TenQuanta`

-/

lemma reduce_noExotics_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.NoExotics := by
  rw [FluxesTen.NoExotics]
  rw [reduce_numChiralU_of_mem_elemsNoExotics hx, reduce_numAntiChiralU_of_mem_elemsNoExotics hx,
    reduce_numChiralQ_of_mem_elemsNoExotics hx, reduce_numAntiChiralQ_of_mem_elemsNoExotics hx,
    reduce_numChiralE_of_mem_elemsNoExotics hx, reduce_numAntiChiralE_of_mem_elemsNoExotics hx]
  simp

/-!

### B.11. Reduce member of `FLuxesTen.elemsNoExotics`

-/

lemma reduce_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen ∈ FluxesTen.elemsNoExotics := by
  rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics]
  apply And.intro
  · exact reduce_noExotics_of_mem_elemsNoExotics hx
  · intro h
    replace h := mem_powerset_sum_of_mem_reduce_toFluxesTen_filter h
    generalize F.toFluxesTen = G at *
    revert G
    decide

end reduce

/-!

## C. Decomposition of a `TenQuanta` into basic fluxes

-/

/-!

### C.1. Decomposition of fluxes

-/

/-- The decomposition of a relevant flux into `⟨1, 0⟩`, `⟨1, 1⟩` and `⟨1, -1⟩` . -/
def decomposeFluxes (f : Fluxes) : Multiset Fluxes :=
  if f = ⟨1, 0⟩ then {⟨1, 0⟩}
  else if f = ⟨1, 1⟩ then {⟨1, 1⟩}
  else if f = ⟨1, -1⟩ then {⟨1, -1⟩}
  else if f = ⟨2, 1⟩ then {⟨1, 1⟩, ⟨1, 0⟩}
  else if f = ⟨2, -1⟩ then {⟨1, -1⟩, ⟨1, 0⟩}
  else if f = ⟨3, 0⟩ then {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩}
  else if f = ⟨2, 0⟩ then {⟨1, 0⟩, ⟨1, 0⟩}
  else {f}

lemma decomposeFluxes_sum_of_noExotics (f : Fluxes) (hf : ∃ F ∈ FluxesTen.elemsNoExotics, f ∈ F) :
    (decomposeFluxes f).sum = f := by
  obtain ⟨F, hF, hfF⟩ := hf
  revert f
  revert F
  decide

/-!

### C.2. Decomposition of a `TenQuanta` (with no exotics)

-/

/-- The decomposition of a `TenQuanta` into a `TenQuanta` which has the
  same `reduce` by has fluxes `{⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩}` or `{⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩}` only.

  This only works for fluxes which have no exotics or zeros. -/
def decompose (x : TenQuanta 𝓩) : TenQuanta 𝓩 :=
  x.bind fun p => (decomposeFluxes p.2).map fun f => (p.1, f)

/-!

#### C.2.1. Decomposition distributes over addition

-/

lemma decompose_add (x y : TenQuanta 𝓩) :
    (x + y).decompose = x.decompose + y.decompose := by
  simp [decompose]

/-!

#### C.2.2. Decomposition commutes with filtering charges

-/

lemma decompose_filter_charge [DecidableEq 𝓩] (x : TenQuanta 𝓩) (q : 𝓩) :
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
    · simp [h, decompose]

/-!

#### C.2.3. Decomposition preserves the charge map

-/

lemma decompose_toChargeMap [DecidableEq 𝓩] (x : TenQuanta 𝓩)
    (hx : x.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
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
  use x.toFluxesTen
  simp_all [toFluxesTen]
  use a.1
  exact ha.1

/-!

#### C.2.4. Decomposition preserves the charges

-/

lemma decompose_toCharges_dedup [DecidableEq 𝓩] (x : TenQuanta 𝓩)
    (hx : x.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    x.decompose.toCharges.dedup = x.toCharges.dedup := by
  refine Multiset.dedup_ext.mpr ?_
  intro q
  simp [decompose, toCharges, -existsAndEq]
  constructor
  · rintro ⟨a, b, c, h1, h2, rfl⟩
    exact ⟨c, h1⟩
  · rintro ⟨c, h1⟩
    have hn : (decomposeFluxes c) ≠ 0 := by
      have c_mem_f : c ∈ x.toFluxesTen := by
        simp [toFluxesTen]
        use q
      generalize x.toFluxesTen = F at *
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

lemma decompose_reduce (x : TenQuanta 𝓩) [DecidableEq 𝓩]
    (hx : x.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    x.decompose.reduce = x.reduce := by
  rw [reduce, reduce]
  apply Multiset.map_congr
  · rw [decompose_toCharges_dedup x hx]
  · intro q hx'
    simp only [Prod.mk.injEq, true_and]
    change x.decompose.toChargeMap q = x.toChargeMap q
    rw [decompose_toChargeMap x hx]

/-!

#### C.2.6. Fluxes of the decomposition of a `TenQuanta`

-/

lemma decompose_toFluxesTen (x : TenQuanta 𝓩)
    (hx : x.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    x.decompose.toFluxesTen = {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩} ∨
    x.decompose.toFluxesTen = {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩} := by
  rw [toFluxesTen, decompose]
  rw [Multiset.map_bind]
  simp only [Multiset.map_map, Function.comp_apply, Multiset.map_id', Multiset.insert_eq_cons,
    Int.reduceNeg]
  have hx : (Multiset.bind x fun a => decomposeFluxes a.2) =
      (Multiset.bind x.toFluxesTen fun a => decomposeFluxes a) := by
    rw [toFluxesTen, Multiset.bind_map]
  rw [hx]
  clear hx
  generalize x.toFluxesTen = F at *
  revert F
  decide

/-!

## D. Lifting charges to `TenQuanta`

-/

section toChargesExpand

open SuperSymmetry.SU5.ChargeSpectrum

variable [DecidableEq 𝓩]

/-!

### D.1. `liftCharge c`: multiset of ten-quanta for a finite set of charges `c` with no exotics

This is an efficient definition, we will later show that it gives the correct answer

-/

/-- Given a finite set of charges `c` the `TenQuanta`
  which do not have exotics, duplicate charges or zero fluxes, which map down to `c`.
  This is defined to be as efficient as possible. -/
def liftCharge (c : Finset 𝓩) : Multiset (TenQuanta 𝓩) :=
  /- The {(1, 0), (1, 0), (1, 0)} case. -/
  /- The multisets of cardinality 3 containing 3 elements of `c`. -/
  let S10 : Multiset (Multiset 𝓩) := toMultisetsThree c
  let F1 : Multiset (TenQuanta 𝓩) :=
    (S10.map (fun s => s.map (fun z => (z, ⟨1, 0⟩)))).filter (fun s => c.val ≤ s.toCharges)
  /- The {(1, 1), (1, -1), (1, 0)} case. -/
  let F2 : Multiset (TenQuanta 𝓩) := ((c.product <| c.product <| c).val.map
    fun (x, y, z) => {(x, ⟨1, 1⟩), (y, ⟨1, -1⟩), (z, ⟨1, 0⟩)}).filter (fun s => c.val ≤ s.toCharges)
  /- All together-/
  (F1 + F2).map reduce

/-!

### D.2. TenQuanta in `liftCharge c` have a finite set of charges `c`

-/

lemma toCharge_toFinset_of_mem_liftCharge (c : Finset 𝓩)
    {x : TenQuanta 𝓩} (h : x ∈ liftCharge c) :
    x.toCharges.toFinset = c := by
  rw [liftCharge, Multiset.mem_map] at h
  obtain ⟨a, h, rfl⟩ := h
  rw [reduce_toCharges]
  simp at h
  rcases h with h | h
  · obtain ⟨⟨s, h, rfl⟩, h'⟩ := h
    simp_all [toCharges]
    ext a
    simp only [Multiset.mem_toFinset]
    constructor
    · intro hr
      apply h.1
      simpa using hr
    · intro hr
      exact Multiset.mem_of_le h' hr
  · obtain ⟨⟨q1, q2, q3, h, rfl⟩, h'⟩ := h
    simp_all [toCharges]
    refine Eq.symm ((fun {α} {s₁ s₂} => Finset.ext_iff.mpr) ?_)
    intro a
    constructor
    · intro hr
      simpa using Multiset.mem_of_le h' hr
    · intro hr
      simp at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2

/-!

### D.3. TenQuanta in `liftCharge c` have no duplicate charges

-/

lemma toCharges_nodup_of_mem_liftCharge (c : Finset 𝓩) {x : TenQuanta 𝓩}
    (h : x ∈ liftCharge c) : x.toCharges.Nodup := by
  rw [liftCharge, Multiset.mem_map] at h
  obtain ⟨x, h, rfl⟩ := h
  rw [reduce_toCharges]
  exact Multiset.nodup_dedup x.toCharges

/-!

### D.4. Membership in `liftCharge c` iff is reduction of `TenQuanta` with given fluxes

-/

lemma exists_toCharges_toFluxesTen_of_mem_liftCharge (c : Finset 𝓩)
    {x : TenQuanta 𝓩} (h : x ∈ liftCharge c) :
    ∃ a : TenQuanta 𝓩, a.reduce = x ∧ a.toCharges.toFinset = c ∧
    (a.toFluxesTen = {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩}
    ∨ a.toFluxesTen = {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩}) := by
  have h' := h
  rw [liftCharge, Multiset.mem_map] at h
  obtain ⟨a, h, rfl⟩ := h
  use a
  simp only [Multiset.insert_eq_cons, Int.reduceNeg, true_and]
  apply And.intro
  · rw [← toCharge_toFinset_of_mem_liftCharge c h', reduce_toCharges]
    simp
  simp at h
  rcases h with h | h
  · obtain ⟨⟨s, h, rfl⟩, h'⟩ := h
    left
    simp [toFluxesTen]
    rw [h.2]
    decide
  · obtain ⟨⟨q1, q2, q3, h, rfl⟩, h'⟩ := h
    simp [toFluxesTen]

lemma mem_liftCharge_of_exists_toCharges_toFluxesTen (c : Finset 𝓩) {x : TenQuanta 𝓩}
    (h :∃ a : TenQuanta 𝓩, a.reduce = x ∧ a.toCharges.toFinset = c ∧
    (a.toFluxesTen = {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩}
    ∨ a.toFluxesTen = {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩})) :
    x ∈ liftCharge c := by
  obtain ⟨x, rfl, h, h2⟩ := h
  rw [liftCharge, Multiset.mem_map]
  use x
  simp only [Finset.product_eq_sprod, Finset.product_val, Int.reduceNeg, Multiset.insert_eq_cons,
    Multiset.mem_add, Multiset.mem_filter, Multiset.mem_map, mem_toMultisetsThree_iff, Prod.exists,
    and_true]
  rcases h2 with h2 | h2
  · left
    subst h
    simp only [Multiset.toFinset_subset, Multiset.toFinset_val]
    apply And.intro
    · use x.toCharges
      simp only [Multiset.Subset.refl, true_and]
      apply And.intro
      · simp [toCharges]
        trans x.toFluxesTen.card
        · simp [toFluxesTen]
        rw [h2]
        decide
      · trans Multiset.map (fun z => z) x
        swap
        · simp
        rw [toCharges, Multiset.map_map]
        apply Multiset.map_congr
        rfl
        intro p hp
        simp only [Function.comp_apply]
        have h1 : p.2 ∈ x.toFluxesTen := by
          simp [toFluxesTen]
          use p.1
        rw [h2] at h1
        simp at h1
        change _ = (p.1, p.2)
        rw [h1]
    · exact Multiset.dedup_le x.toCharges
  · right
    have h2' := h2
    simp [toFluxesTen] at h2
    rw [← Multiset.map_eq_cons] at h2
    obtain ⟨p1, hp1, hp1_2, h2⟩ := h2
    rw [← Multiset.map_eq_cons] at h2
    obtain ⟨p2, hp2, hp2_2, h2⟩ := h2
    rw [Multiset.map_eq_singleton] at h2
    obtain ⟨p3, hp3, hp3_2⟩ := h2
    apply And.intro
    · use p1.1, p2.1, p3.1
      subst h
      simp only [Multiset.toFinset_val, Multiset.mem_product, Multiset.mem_dedup, Int.reduceNeg]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · simp [toCharges]
        use p1.2
      · simp [toCharges]
        use p2.2
        apply Multiset.erase_subset p1 x hp2
      · simp [toCharges]
        use p3.2
        apply Multiset.erase_subset p1 x
        apply Multiset.erase_subset p2 _
        rw [hp3]
        simp
      · symm
        refine Eq.symm (Multiset.eq_of_le_of_card_le ?_ ?_)
        · refine (Multiset.cons_le_of_notMem ?_).mpr ⟨?_, ?_⟩
          · simp
          · rw [← hp1_2]
            exact hp1
          refine (Multiset.cons_le_of_notMem ?_).mpr ⟨?_, ?_⟩
          · simp
          · rw [← hp2_2]
            apply Multiset.erase_subset p1 x
            exact hp2
          simp only [Multiset.singleton_le]
          rw [← hp3_2]
          apply Multiset.erase_subset p1 x
          apply Multiset.erase_subset p2 _
          rw [hp3]
          simp
        · trans x.toFluxesTen.card
          · simp [toFluxesTen]
          rw [h2']
          simp
    · rw [← h]
      simp only [Multiset.toFinset_val]
      exact Multiset.dedup_le x.toCharges

lemma mem_liftCharge_iff_exists (c : Finset 𝓩) {x : TenQuanta 𝓩} :
    x ∈ liftCharge c ↔
    ∃ a : TenQuanta 𝓩, a.reduce = x ∧ a.toCharges.toFinset = c ∧
    (a.toFluxesTen = {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩}
    ∨ a.toFluxesTen = {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩}) := by
  constructor
  · exact exists_toCharges_toFluxesTen_of_mem_liftCharge c
  · exact mem_liftCharge_of_exists_toCharges_toFluxesTen c

/-!

### D.5. TenQuanta in `liftCharge c` do not have zero fluxes

-/

lemma hasNoZero_of_mem_liftCharge (c : Finset 𝓩) {x : TenQuanta 𝓩}
    (h : x ∈ liftCharge c) : x.toFluxesTen.HasNoZero := by
  rw [mem_liftCharge_iff_exists] at h
  obtain ⟨x, rfl, h1, h2⟩ := h
  intro hf
  have hx := mem_powerset_sum_of_mem_reduce_toFluxesTen_filter hf
  rcases h2 with h2 | h2
  all_goals
    rw [h2] at hx
    revert hx
    decide

/-!

### D.6. TenQuanta in `liftCharge c` have no exotics

-/

lemma noExotics_of_mem_liftCharge (c : Finset 𝓩) (F : TenQuanta 𝓩)
    (h : F ∈ liftCharge c) :
    F.toFluxesTen.NoExotics := by
  rw [mem_liftCharge_iff_exists] at h
  obtain ⟨x, rfl, h1, h2⟩ := h
  apply reduce_noExotics_of_mem_elemsNoExotics
  rcases h2 with h2 | h2
  all_goals
    rw [h2]
    decide

/-!

### D.7. Membership in `liftCharge c` iff have no exotics, no zero fluxes, and charges `c`

-/

lemma mem_liftCharge_of_mem_noExotics_hasNoZero (c : Finset 𝓩) {x : TenQuanta 𝓩}
    (h1 : x.toFluxesTen.NoExotics) (h2 : x.toFluxesTen.HasNoZero)
    (h3 : x.toCharges.toFinset = c) (h4 : x.toCharges.Nodup) :
    x ∈ liftCharge c := by
  have hf : x.toFluxesTen ∈ FluxesTen.elemsNoExotics := by
    rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics]
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
    · exact decompose_toFluxesTen x hf

lemma mem_liftCharge_iff (c : Finset 𝓩) (x : TenQuanta 𝓩) :
    x ∈ liftCharge c ↔ x.toFluxesTen ∈ FluxesTen.elemsNoExotics
      ∧ x.toCharges.toFinset = c ∧ x.toCharges.Nodup := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics]
      refine ⟨?_, ?_⟩
      · exact noExotics_of_mem_liftCharge c x h
      · exact hasNoZero_of_mem_liftCharge c h
    · exact toCharge_toFinset_of_mem_liftCharge c h
    · exact toCharges_nodup_of_mem_liftCharge c h
  · intro ⟨h1, h2, h3⟩
    rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics] at h1
    exact mem_liftCharge_of_mem_noExotics_hasNoZero c h1.1 h1.2 h2 h3

/-!

### D.8. `liftCharge c` is preserved under a map if reduced

-/

lemma map_liftCharge {𝓩 𝓩1 : Type}[DecidableEq 𝓩] [DecidableEq 𝓩1] [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (c : Finset 𝓩) (F : TenQuanta 𝓩) (h : F ∈ liftCharge c) :
    TenQuanta.reduce (F.map fun y => (f y.1, y.2)) ∈ liftCharge (c.image f) := by
  rw [mem_liftCharge_iff] at h ⊢
  refine ⟨?_, ?_, ?_⟩
  · apply reduce_mem_elemsNoExotics
    simpa [toFluxesTen, Multiset.map_map] using h.1
  · rw [reduce_toCharges]
    simp [← h.2.1, ← Multiset.toFinset_map, toCharges]
  · rw [reduce_toCharges]
    exact Multiset.nodup_dedup (toCharges (Multiset.map (fun y => (f y.1, y.2)) F))

end toChargesExpand

/-!

## E. Anomaly cancellation coefficients

-/

section ACCs

variable [CommRing 𝓩]

/-!

### E.1. Anomaly coefficients of a `TenQuanta`

-/

/--
  The anomaly coefficient of a `TenQuanta` is given by the pair of integers:
  `(∑ᵢ qᵢ Nᵢ, 3 * ∑ᵢ qᵢ² Nᵢ)`.

  The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084.
  The second component is for the mixed U(1)Y-U(1)-U(1) gauge anomaly,
    see equation (23) of arXiv:1401.5084.
-/
def anomalyCoefficient (F : TenQuanta 𝓩) : 𝓩 × 𝓩 :=
  ((F.map fun x => x.2.2 • x.1).sum, 3 * (F.map fun x => x.2.2 • (x.1 * x.1)).sum)

/-!

### E.2. Anomaly coefficients under a map

-/

@[simp]
lemma anomalyCoefficient_of_map {𝓩 𝓩1 : Type} [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (F : TenQuanta 𝓩) :
    TenQuanta.anomalyCoefficient (F.map fun y => (f y.1, y.2) : TenQuanta 𝓩1) =
    (f.prodMap f) F.anomalyCoefficient := by
  simp [TenQuanta.anomalyCoefficient, map_multiset_sum, Multiset.map_map, map_ofNat]

/-!

### E.3. Anomaly coefficients is preserved under `reduce`

-/

lemma anomalyCoefficient_of_reduce [DecidableEq 𝓩] (F : TenQuanta 𝓩) :
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
    apply congrArg
    simpa [f] using reduce_sum_eq_sum_toCharges F f

end ACCs

end TenQuanta

end SU5

end FTheory
