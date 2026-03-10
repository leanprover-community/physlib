/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas
/-!

# Fluxes of representations

## i. Overview

Associated with each matter curve `Σ` are `G₄`-fluxes and `hypercharge` fluxes.

For a given matter curve `Σ`, and a Standard Model representation `R`,
these two fluxes contribute to the chiral index `χ(R)` of the representation
(eq 17 of [1]).

The chiral index is equal to the difference the number of left-handed minus
the number of right-handed fermions `Σ` leads to in the representation `R`.
Thus, for example, if `χ(R) = 0`, then all fermions in the representation `R`
arising from `Σ` arise in vector-like pairs, and can be given a mass term without
the presence of a Higgs like-particle.

For a 10d representation matter curve the non-zero chiral indices can be parameterized in terms
of two integers `M : ℤ` and `N : ℤ`. For the SM representation
- `Q = (3,2)_{1/6}` the chirality index is `M`
- `U = (bar 3,1)_{-2/3}` the chirality index is `M - N`
- `E = (1,1)_{1}` the chirality index is `M + N`
We call refer to `M` as the chirality flux of the 10d representation, and
`N` as the hypercharge flux. There exact definitions are given in (eq 19 of [1]).

Similarly, for the 5-bar representation matter curve the non-zero chiral indices can be
likewise be parameterized in terms of two integers `M : ℤ` and `N : ℤ`. For the SM representation
- `D = (bar 3,1)_{1/3}` the chirality index is `M`
- `L = (1,2)_{-1/2}` the chirality index is `M + N`
We again refer to `M` as the chirality flux of the 5-bar representation, and
`N` as the hypercharge flux. The exact definitions are given in (eq 19 of [1]).

If one wishes to put the condition of no chiral exotics in the spectrum, then
we must ensure that the chiral indices above give the chiral content of the MSSM.
These correspond to the following conditions:
1. The two higgs `Hu` and `Hd` must arise from different 5d-matter curves. Otherwise
  they will give a `μ`-term.
2. The matter curve containing `Hu` must give one anti-chiral `(1,2)_{-1/2}` and
  no `(bar 3,1)_{1/3}`. Thus `N = -1` and `M = 0`.
3. The matter curve containing `Hd` must give one chiral `(1,2)_{-1/2}` and
  no `(bar 3,1)_{1/3}`. Thus `N = 1` and `M = 0`.
4. We should have no anti-chiral `(3,2)_{1/6}` and anti-chiral `(bar 3,1)_{-2/3}`.
  Thus `0 ≤ M ` for all 10d-matter curves and 5d matter curves.
5. For the 10d-matter curves we should have no anti-chiral `(bar 3,1)_{-2/3}`
    and no anti-chiral `(1,1)_{1}`. Thus `-M ≤ N ≤ M` for all 10d-matter curves.
6. For the 5d-matter curves we should have no anti-chiral `(1,2)_{-1/2}` (the only
  anti-chiral one present is the one from `Hu`) and thus
  `-M ≤ N` for all 5d-matter curves.
7. To ensure we have 3-families of fermions we must have that `∑ M = 3` and
    `∑ N = 0` for the matter 10d and 5bar matter curves, and in addition `∑ (M + N) = 3` for the
    matter 5d matter curves.
See the conditions in equation 26 - 28 of [1].

## ii. Key results

The above theory is implemented by defining two data structures:
- `Fluxes` : The data of the fluxes `(M, N)` carried by a matter field.
- `FluxesTen` of type `Multiset Fluxes`
  which contains the chirality `M` and hypercharge fluxes
  `N` of the 10d-matter curves.
- `FluxesFive` of type `Multiset Fluxes`
  which contains the chirality `M` and hypercharge fluxes
  `N` of the 5-bar-matter curves (excluding the higgses).

Note: Neither `FluxesTen` or `FluxesFive` are fundamental to the theory,
they can be derived from other data structures.

## iii. Table of contents

- A. Fluxes
  - A.1. Repr instance on `Fluxes`
  - A.2. Extensionality lemma for the fluxes
  - A.3. The zero flux
  - A.4. Addition of fluxes
  - A.5. The instance of an additive commutative monoid on fluxes
- B. Fluxes of the 5d matter representation
  - B.1. Decidability instance on `FluxesFive`
  - B.2. The proposition for no element to be zero
  - B.3. The SM representation `D = (bar 3,1)_{1/3}`
    - B.3.1. Chiral indices of `D`
    - B.3.2. The number of chiral `D`
    - B.3.3. The number of anti-chiral `D`
    - B.3.4. Relation between number of chiral and anti-chiral `D`
  - B.4. The SM representation `L = (1,2)_{-1/2}`
    - B.4.1. Chiral indices of `L`
    - B.4.2. The number of chiral `L`
    - B.4.3. The number of anti-chiral `L`
    - B.4.4. Relation between number of chiral and anti-chiral `L`
  - B.5. No exotics from the 5-bar matter fields
- C. Fluxes of the 10d matter representation
  - C.1. Decidability instance on `FluxesTen`
  - C.2. The proposition for no element to be zero
  - C.3. The SM representation `Q = (3,2)_{1/6}`
    - C.3.1. Chiral indices of `Q`
    - C.3.2. The number of chiral `Q`
    - C.3.3. The number of anti-chiral `Q`
    - C.3.4. Relation between number of chiral and anti-chiral `Q`
  - C.4. The SM representation `U = (bar 3,1)_{-2/3}`
    - C.4.1. Chiral indices of `U`
    - C.4.2. The number of chiral `U`
    - C.4.3. The number of anti-chiral `U`
    - C.4.4. Relation between number of chiral and anti-chiral `Q`
  - C.5. The SM representation `E = (1,1)_{1}`
    - C.5.1. Chiral indices of `E`
    - C.5.2. The number of chiral `E`
    - C.5.3. The number of anti-chiral `E`
    - C.5.4. Relation between number of chiral and anti-chiral `E`
  - C.6. No exotics from the 10d matter fields

## iv. References

- [1] arXiv:1401.5084
- For an old version of the material in this module see PR #569.

-/

@[expose] public section
namespace FTheory

namespace SU5

/-!

## A. Fluxes

To each matter curve we associate a pair of integers `(M, N)`,
the former of which is the chirality flux and the latter the hypercharge flux.

-/

/-- The data of the fluxes carried by a matter field. -/
structure Fluxes where
  /-- The chirality flux. -/
  M : ℤ
  /-- The hypercharge flux. -/
  N : ℤ
deriving DecidableEq

namespace Fluxes

/-!

### A.1. Repr instance on `Fluxes`

-/

instance : Repr Fluxes where
  reprPrec x _ := "⟨" ++ repr x.M ++ ", " ++ repr x.N ++ "⟩"

/-!

### A.2. Extensionality lemma for the fluxes

-/

lemma ext_iff {f1 f2 : Fluxes} : f1 = f2 ↔ f1.M = f2.M ∧ f1.N = f2.N := by
  cases f1; cases f2; simp

instance : Zero Fluxes := ⟨0, 0⟩

/-!

### A.3. The zero flux

-/

@[simp]
lemma zero_M : (0 : Fluxes).M = 0 := rfl

@[simp]
lemma zero_N : (0 : Fluxes).N = 0 := rfl

/-!

### A.4. Addition of fluxes

-/

instance : Add Fluxes where
  add f1 f2 := ⟨f1.M + f2.M, f1.N + f2.N⟩

@[simp]
lemma add_M (f1 f2 : Fluxes) : (f1 + f2).M = f1.M + f2.M := rfl

@[simp]
lemma add_N (f1 f2 : Fluxes) : (f1 + f2).N = f1.N + f2.N := rfl

/-!

### A.5. The instance of an additive commutative monoid on fluxes

-/

instance : AddCommMonoid Fluxes where
  add_assoc f1 f2 f3 := Fluxes.ext_iff.mpr <| by simp only [add_M, add_N]; ring_nf; simp
  zero_add f := Fluxes.ext_iff.mpr <| by simp
  add_zero f := Fluxes.ext_iff.mpr <| by simp
  add_comm f1 f2 := Fluxes.ext_iff.mpr <| by simp only [add_M, add_N]; ring_nf; simp
  nsmul n f := ⟨n * f.M, n * f.N⟩
  nsmul_zero f := Fluxes.ext_iff.mpr <| by simp
  nsmul_succ n f := Fluxes.ext_iff.mpr <| by
    simp only [Nat.cast_add, Nat.cast_one, add_M, add_N]; ring_nf; simp

end Fluxes

/-!

## B. Fluxes of the 5d matter representation

-/

/-- The fluxes `(M, N)` of the 5-bar matter curves of a theory. -/
abbrev FluxesFive : Type := Multiset Fluxes

namespace FluxesFive

/-!

### B.1. Decidability instance on `FluxesFive`

-/

instance : DecidableEq FluxesFive :=
  inferInstanceAs (DecidableEq (Multiset Fluxes))

/-!

### B.2. The proposition for no element to be zero

-/

/-- The proposition on `FluxesFive` such that `(0, 0)` is not in `F`
  and as such each component in `F` leads to chiral matter. -/
abbrev HasNoZero (F : FluxesFive) : Prop := 0 ∉ F

/-!

### B.3. The SM representation `D = (bar 3,1)_{1/3}`

-/

/-!

#### B.3.1. Chiral indices of `D`

-/

/-- The multiset of chiral indices of the representation `D = (bar 3,1)_{1/3}`
  arising from the matter 5d representations. -/
def chiralIndicesOfD (F : FluxesFive) : Multiset ℤ := F.map (fun f => f.M)

/-!

#### B.3.2. The number of chiral `D`

-/

/-- The total number of chiral `D` representations arising from the matter 5d
  representations. -/
def numChiralD (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfD F).filter (fun x => 0 ≤ x)).sum

/-!

#### B.3.3. The number of anti-chiral `D`

-/

/-- The total number of anti-chiral `D` representations arising from the matter 5d
  representations. -/
def numAntiChiralD (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfD F).filter (fun x => x < 0)).sum

/-!

#### B.3.4. Relation between number of chiral and anti-chiral `D`

-/

lemma numChiralD_eq_sum_sub_numAntiChiralD (F : FluxesFive) :
    F.numChiralD = (chiralIndicesOfD F).sum - F.numAntiChiralD := by
  have h1 : (chiralIndicesOfD F) =
    (chiralIndicesOfD F).filter (fun x => 0 ≤ x) +
    (chiralIndicesOfD F).filter (fun x => ¬ 0 ≤ x) := by
      exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfD)
  rw [h1]
  simp [chiralIndicesOfD, numChiralD, numAntiChiralD]

/-!

### B.4. The SM representation `L = (1,2)_{-1/2}`

-/

/-!

#### B.4.1. Chiral indices of `L`

-/

/-- The multiset of chiral indices of the representation `L = (1,2)_{-1/2}`
  arising from the matter 5d representations. -/
def chiralIndicesOfL (F : FluxesFive) : Multiset ℤ := F.map (fun f => f.M + f.N)

/-!

#### B.4.2. The number of chiral `L`

-/

/-- The total number of chiral `L` representations arising from the matter 5d
  representations. -/
def numChiralL (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfL F).filter (fun x => 0 ≤ x)).sum

/-!

#### B.4.3. The number of anti-chiral `L`

-/

/-- The total number of anti-chiral `L` representations arising from the matter 5d
  representations. -/
def numAntiChiralL (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfL F).filter (fun x => x < 0)).sum

/-!

#### B.4.4. Relation between number of chiral and anti-chiral `L`

-/

lemma numChiralL_eq_sum_sub_numAntiChiralL (F : FluxesFive) :
    F.numChiralL = (chiralIndicesOfL F).sum - F.numAntiChiralL := by
  have h1 : (chiralIndicesOfL F) =
    (chiralIndicesOfL F).filter (fun x => 0 ≤ x) +
    (chiralIndicesOfL F).filter (fun x => ¬ 0 ≤ x) := by
      exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfL)
  rw [h1]
  simp [chiralIndicesOfL, numChiralL, numAntiChiralL]

/-!

### B.5. No exotics from the 5-bar matter fields

-/

/-- The condition that the 5d-matter representations do not lead to exotic chiral matter in the
  MSSM spectrum. This corresponds to the conditions that:
- There are 3 chiral `L` representations and no anti-chiral `L` representations.
- There are 3 chiral `D` representations and no anti-chiral `D` representations.
-/
def NoExotics (F : FluxesFive) : Prop :=
  F.numChiralL = 3 ∧ F.numAntiChiralL = 0 ∧ F.numChiralD = 3 ∧ F.numAntiChiralD = 0

instance (F : FluxesFive) : Decidable (F.NoExotics) :=
  instDecidableAnd

end FluxesFive

/-!

## C. Fluxes of the 10d matter representation

-/

/-- The fluxes `(M, N)` of the 10d matter curves of a theory. -/
abbrev FluxesTen : Type := Multiset Fluxes

namespace FluxesTen

/-!

### C.1. Decidability instance on `FluxesTen`

-/

instance : DecidableEq FluxesTen :=
  inferInstanceAs (DecidableEq (Multiset Fluxes))

/-!

### C.2. The proposition for no element to be zero

-/

/-- The proposition on `FluxesTen` such that `(0, 0)` is not in `F`
  and as such each component in `F` leads to chiral matter. -/
abbrev HasNoZero (F : FluxesTen) : Prop := 0 ∉ F

/-!

### C.3. The SM representation `Q = (3,2)_{1/6}`

-/

/-!

#### C.3.1. Chiral indices of `Q`

-/

/-- The multiset of chiral indices of the representation `Q = (3,2)_{1/6}`
  arising from the matter 10d representations, corresponding to `M`. -/
def chiralIndicesOfQ (F : FluxesTen) : Multiset ℤ := F.map (fun f => f.M)

/-!

#### C.3.2. The number of chiral `Q`

-/

/-- The total number of chiral `Q` representations arising from the matter 10d
  representations. -/
def numChiralQ (F : FluxesTen) : ℤ := ((chiralIndicesOfQ F).filter (fun x => 0 ≤ x)).sum

/-!

#### C.3.3. The number of anti-chiral `Q`

-/

/-- The total number of anti-chiral `Q` representations arising from the matter 10d
  representations. -/
def numAntiChiralQ (F : FluxesTen) : ℤ := ((chiralIndicesOfQ F).filter (fun x => x < 0)).sum

/-!

#### C.3.4. Relation between number of chiral and anti-chiral `Q`

-/

lemma numChiralQ_eq_sum_sub_numAntiChiralQ (F : FluxesTen) :
    F.numChiralQ = (chiralIndicesOfQ F).sum - F.numAntiChiralQ := by
  have h1 : (chiralIndicesOfQ F) =
    (chiralIndicesOfQ F).filter (fun x => 0 ≤ x) +
    (chiralIndicesOfQ F).filter (fun x => ¬ 0 ≤ x) := by
      exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfQ)
  rw [h1]
  simp [chiralIndicesOfQ, numChiralQ, numAntiChiralQ]

/-!

### C.4. The SM representation `U = (bar 3,1)_{-2/3}`

-/

/-!

#### C.4.1. Chiral indices of `U`

-/

/-- The multiset of chiral indices of the representation `U = (bar 3,1)_{-2/3}`
  arising from the matter 10d representations, corresponding to `M - N` -/
def chiralIndicesOfU (F : FluxesTen) : Multiset ℤ := F.map (fun f => f.M - f.N)

/-!

#### C.4.2. The number of chiral `U`

-/

/-- The total number of chiral `U` representations arising from the matter 10d
  representations. -/
def numChiralU (F : FluxesTen) : ℤ := ((chiralIndicesOfU F).filter (fun x => 0 ≤ x)).sum

/-!

#### C.4.3. The number of anti-chiral `U`

-/

/-- The total number of anti-chiral `U` representations arising from the matter 10d
  representations. -/
def numAntiChiralU (F : FluxesTen) : ℤ := ((chiralIndicesOfU F).filter (fun x => x < 0)).sum

/-

#### C.4.4. Relation between number of chiral and anti-chiral `Q`

-/

lemma numChiralU_eq_sum_sub_numAntiChiralU (F : FluxesTen) :
    F.numChiralU = (chiralIndicesOfU F).sum - F.numAntiChiralU := by
  have h1 : (chiralIndicesOfU F) =
    (chiralIndicesOfU F).filter (fun x => 0 ≤ x) +
    (chiralIndicesOfU F).filter (fun x => ¬ 0 ≤ x) := by
      exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfU)
  rw [h1]
  simp [chiralIndicesOfU, numChiralU, numAntiChiralU]
/-!

### C.5. The SM representation `E = (1,1)_{1}`

-/

/-!

#### C.5.1. Chiral indices of `E`

-/

/-- The multiset of chiral indices of the representation `E = (1,1)_{1}`
  arising from the matter 10d representations, corresponding to `M + N` -/
def chiralIndicesOfE (F : FluxesTen) : Multiset ℤ := F.map (fun f => f.M + f.N)

/-!

#### C.5.2. The number of chiral `E`

-/

/-- The total number of chiral `E` representations arising from the matter 10d
  representations. -/
def numChiralE (F : FluxesTen) : ℤ := ((chiralIndicesOfE F).filter (fun x => 0 ≤ x)).sum

/-!

#### C.5.3. The number of anti-chiral `E`

-/

/-- The total number of anti-chiral `E` representations arising from the matter 10d
  representations. -/
def numAntiChiralE (F : FluxesTen) : ℤ := ((chiralIndicesOfE F).filter (fun x => x < 0)).sum

/-!

#### C.5.4. Relation between number of chiral and anti-chiral `E`

-/

lemma numChiralE_eq_sum_sub_numAntiChiralE (F : FluxesTen) :
    F.numChiralE = (chiralIndicesOfE F).sum - F.numAntiChiralE := by
  have h1 : (chiralIndicesOfE F) =
    (chiralIndicesOfE F).filter (fun x => 0 ≤ x) +
    (chiralIndicesOfE F).filter (fun x => ¬ 0 ≤ x) := by
      exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfE)
  rw [h1]
  simp [chiralIndicesOfE, numChiralE, numAntiChiralE]

/-!

### C.6. No exotics from the 10d matter fields

-/

/-- The condition that the 10d-matter representations do not lead to exotic chiral matter in the
  MSSM spectrum. This corresponds to the conditions that:
- There are 3 chiral `Q` representations and no anti-chiral `Q` representations.
- There are 3 chiral `U` representations and no anti-chiral `U` representations.
- There are 3 chiral `E` representations and no anti-chiral `E` representations.
-/
def NoExotics (F : FluxesTen) : Prop :=
  F.numChiralQ = 3 ∧ F.numAntiChiralQ = 0 ∧
  F.numChiralU = 3 ∧ F.numAntiChiralU = 0 ∧
  F.numChiralE = 3 ∧ F.numAntiChiralE = 0

instance (F : FluxesTen) : Decidable (F.NoExotics) :=
  instDecidableAnd

end FluxesTen

end SU5

end FTheory
