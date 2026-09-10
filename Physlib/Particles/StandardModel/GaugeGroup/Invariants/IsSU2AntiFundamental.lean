/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiFundamental
/-!
# Gauge tensors carrying anti-fundamental `su(2)` indices

The conjugate of an isospin doublet carries an anti-fundamental index, moved by the complex
conjugate of the `SU(2)` matrix rather than by the matrix itself. A Yukawa coupling `H̄ Q d`
carries one fundamental and one anti-fundamental index, `2 ⊗ 2̄`; the up-type coupling
`ε H Q u` carries two anti-fundamental ones, `2̄ ⊗ 2̄`. This file classifies the isospin
invariants in both cases, in the form the Standard Model files consume: modulo an
isospin-stable submodule, the invariants of `2 ⊗ 2̄` are the multiples of the trace
`T ![0, 0] + T ![1, 1]`, and those of `2̄ ⊗ 2̄` the multiples of the same epsilon contraction
as for `2 ⊗ 2`.

Neither needs a classification of its own. `SU(2)` is pseudo-real: for `U ∈ SU(2)` the
conjugate matrix is `ε U ε⁻¹`, with `ε` the antisymmetric symbol, so an anti-fundamental index
is a fundamental index in another basis. Re-indexing each anti-fundamental slot by `ε` turns
either law into the bi-fundamental law of `IsSU2BiFundamental`, for the very same
representation, and the theorem of that file applies. The re-index is invertible, so it
leaves the span of the components alone, and all that has to be tracked is which contraction
of the original family the epsilon contraction of the re-indexed family is: minus the trace
for `2 ⊗ 2̄`, and the epsilon contraction itself for `2̄ ⊗ 2̄`. `SU(3)` has no such identity,
which is why the colour side needs a separate `IsSU3FunAntiFun`.

Section A treats one fundamental and one anti-fundamental index, section B two
anti-fundamental ones; each gives the law, the re-index, the contraction and the theorem. An
aside at the end holds the gauge form of the first theorem, which the Higgs sector uses.
-/

@[expose] public section

namespace StandardModel

open Matrix ComplexConjugate

/-!

## A. One fundamental and one anti-fundamental index

The law carries a factor of `U` for the first index and a factor of `conj U` for the second,
with the summed index in the row slot. It is the law obeyed by a conjugate Higgs symbol times
a Higgs symbol, once the hypercharge character is set aside.

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with one
  fundamental and one anti-fundamental isospin index: a factor of `U` for the first index
  and a factor of its complex conjugate for the second. -/
def IsSU2FunAntiFunMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 2) → B) : Prop :=
  ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2, (U.1 (a 0) (l 0) * conj (U.1 (a 1) (l 1))) • T a

/-- A family `T` of elements of `B`, indexed by one `su(2)` fundamental index and one
  anti-fundamental one, transforms as a tensor `T^a_b` under the isospin factor of the gauge
  group. Nothing is asked of the colour and hypercharge factors. -/
structure IsSU2FunAntiFun (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 2) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2FunAntiFunMat g (repGauge (1, g, 1)) T

namespace IsSU2FunAntiFun

open IsSU2BiFundamental

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}

/-!

## A.1. The epsilon re-index of the anti-fundamental slot

Re-indexing the second slot by the antisymmetric symbol turns the law into the
bi-fundamental one: the four conjugation identities of `IsSU2BiFundamental` remove every
complex conjugate, after which the two sides agree. The re-index is invertible, so the span
of the components is unchanged.

-/

/-- The family obtained by re-indexing the anti-fundamental slot with the antisymmetric
  symbol. -/
def reindex (T : (Fin 2 → Fin 2) → B) : (Fin 2 → Fin 2) → B :=
  fun l => ∑ m : Fin 2, epsilon (l 1) m • T ![l 0, m]

/-- The re-index at second index `0` picks out the component with second index `1`. -/
@[simp] lemma reindex_apply_zero (T : (Fin 2 → Fin 2) → B) (p : Fin 2) :
    reindex T ![p, 0] = T ![p, 1] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-index at second index `1` picks out minus the component with second index
  `0`. -/
@[simp] lemma reindex_apply_one (T : (Fin 2 → Fin 2) → B) (p : Fin 2) :
    reindex T ![p, 1] = -T ![p, 0] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-indexed family obeys the bi-fundamental law. -/
lemma map_reindex {T : (Fin 2 → Fin 2) → B} (hf : IsSU2FunAntiFunMat U f T) :
    IsSU2BiFundamentalMat U f (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hf' : ∀ k : Fin 2 → Fin 2, f (T k)
      = ∑ a : Fin 2 → Fin 2, (U.1 (a 0) (k 0) * conj (U.1 (a 1) (k 1))) • T a := hf
  intro l
  simp only [reindex, map_add, map_smul, hf', sum_pi_two, Fin.sum_univ_two,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hl (l 0) with h0 | h0 <;> rcases hl (l 1) with h1 | h1 <;> rw [h0, h1] <;>
    simp only [epsilon_zero_zero, epsilon_zero_one, epsilon_one_zero, epsilon_one_one,
      conj_apply_zero_zero, conj_apply_zero_one, conj_apply_one_zero,
      conj_apply_one_one] <;>
    module

/-- The re-index of a fundamental and anti-fundamental family is a bi-fundamental family
  for the same representation. -/
lemma isSU2BiFundamental_reindex {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) :
    IsSU2BiFundamental B repGauge (reindex T) where
  repGauge_T g := map_reindex (hT.repGauge_T g)

/-- Every component of the original family lies in the span of the re-indexed one. -/
lemma self_mem_span_reindex (T : (Fin 2 → Fin 2) → B) (d : Fin 2 → Fin 2) :
    T d ∈ span (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hd : T d = T ![d 0, d 1] := by rw [← eq_cons]
  rw [hd]
  rcases hl (d 1) with h1 | h1 <;> rw [h1]
  · rw [show T ![d 0, (0 : Fin 2)] = -reindex T ![d 0, 1] from by
      rw [reindex_apply_one, neg_neg]]
    exact neg_mem (mem_span _)
  · rw [← reindex_apply_zero T (d 0)]
    exact mem_span _

/-- The re-index does not change the span of the components. -/
lemma span_reindex (T : (Fin 2 → Fin 2) → B) : span (reindex T) = span T := by
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun d => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, reindex]
    exact sum_mem fun m _ => Submodule.smul_mem _ _ (mem_span _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact self_mem_span_reindex T d

/-!

## A.2. The delta contraction

The one invariant of `2 ⊗ 2̄` is the trace `T ![0, 0] + T ![1, 1]`. It is the epsilon
contraction of the re-indexed family up to a sign, which is stated rather than absorbed into
a definition, so that the re-index stays the plain re-index and the trace the plain trace.

-/

/-- The delta contraction: the trace of a family with one fundamental and one
  anti-fundamental index. -/
def deltaContraction (T : (Fin 2 → Fin 2) → B) : B := T ![0, 0] + T ![1, 1]

/-- The delta contraction lies in the span of the components. -/
lemma deltaContraction_mem_span (T : (Fin 2 → Fin 2) → B) :
    deltaContraction T ∈ span T :=
  add_mem (mem_span _) (mem_span _)

/-- The epsilon contraction of the re-indexed family is minus the delta contraction of the
  original one. -/
lemma epsilonContraction_reindex (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction (reindex T) = -deltaContraction T := by
  rw [epsilonContraction, reindex_apply_zero, reindex_apply_one, deltaContraction]
  abel

/-- Any map moving the components by an element of `SU(2)` fixes the delta contraction. -/
lemma map_deltaContraction {T : (Fin 2 → Fin 2) → B} (hf : IsSU2FunAntiFunMat U f T) :
    f (deltaContraction T) = deltaContraction T := by
  have h := map_epsilonContraction (map_reindex hf)
  rw [epsilonContraction_reindex, map_neg, neg_inj] at h
  exact h

/-- The delta contraction is isospin invariant. Nothing constrains the colour and
  hypercharge factors, which may well move it. -/
lemma repGauge_deltaContraction {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, V, 1) (deltaContraction T) = deltaContraction T :=
  map_deltaContraction (hT.repGauge_T V)

/-!

## A.3. The invariants modulo a stable submodule

-/

/-- An isospin invariant of the span of the components joined with an isospin-stable
  submodule `S` is a multiple of the delta contraction up to an isospin-invariant remainder
  in `S`: the theorem of `IsSU2BiFundamental` for the re-indexed family, read through the
  sign of `epsilonContraction_reindex`. -/
theorem mem_span_sup_su2_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ V : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, V, 1) y ∈ S)
    (hx : x ∈ span T ⊔ S)
    (hinv : ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • deltaContraction T + y
      ∧ ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) y = y := by
  obtain ⟨c, y, hyS, hxy, hyinv⟩ :=
    hT.isSU2BiFundamental_reindex.mem_span_sup_su2_invariant_iff x S hS
      (by rw [span_reindex]; exact hx) hinv
  refine ⟨-c, y, hyS, ?_, hyinv⟩
  rw [hxy, epsilonContraction_reindex, smul_neg, neg_smul]

end IsSU2FunAntiFun

/-!

## B. Two anti-fundamental indices

The law carries a factor of `conj U` per index. It is the law obeyed by a product of two
Higgs symbols, once the hypercharge character is set aside.

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with two
  anti-fundamental isospin indices: one factor of the complex conjugate of `U` per index. -/
def IsSU2BiAntiFunMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 2) → B) : Prop :=
  ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2,
      (conj (U.1 (a 0) (l 0)) * conj (U.1 (a 1) (l 1))) • T a

/-- A family `T` of elements of `B`, indexed by two `su(2)` anti-fundamental indices,
  transforms as a tensor `T_{a b}` under the isospin factor of the gauge group. Nothing is
  asked of the colour and hypercharge factors. -/
structure IsSU2BiAntiFun (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 2) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2BiAntiFunMat g (repGauge (1, g, 1)) T

namespace IsSU2BiAntiFun

open IsSU2BiFundamental

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}

/-!

## B.1. The epsilon re-index of both slots

-/

/-- The family obtained by re-indexing both slots with the antisymmetric symbol. -/
def reindex (T : (Fin 2 → Fin 2) → B) : (Fin 2 → Fin 2) → B :=
  fun l => ∑ m : Fin 2, ∑ n : Fin 2, (epsilon (l 0) m * epsilon (l 1) n) • T ![m, n]

/-- The re-index exchanges the two like components. -/
@[simp] lemma reindex_zero_zero (T : (Fin 2 → Fin 2) → B) :
    reindex T ![0, 0] = T ![1, 1] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-index exchanges the two mixed components and negates them. -/
@[simp] lemma reindex_zero_one (T : (Fin 2 → Fin 2) → B) :
    reindex T ![0, 1] = -T ![1, 0] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-index exchanges the two mixed components and negates them. -/
@[simp] lemma reindex_one_zero (T : (Fin 2 → Fin 2) → B) :
    reindex T ![1, 0] = -T ![0, 1] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-index exchanges the two like components. -/
@[simp] lemma reindex_one_one (T : (Fin 2 → Fin 2) → B) :
    reindex T ![1, 1] = T ![0, 0] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-indexed family obeys the bi-fundamental law. -/
lemma map_reindex {T : (Fin 2 → Fin 2) → B} (hf : IsSU2BiAntiFunMat U f T) :
    IsSU2BiFundamentalMat U f (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hf' : ∀ k : Fin 2 → Fin 2, f (T k)
      = ∑ a : Fin 2 → Fin 2,
        (conj (U.1 (a 0) (k 0)) * conj (U.1 (a 1) (k 1))) • T a := hf
  intro l
  simp only [reindex, map_add, map_smul, hf', sum_pi_two, Fin.sum_univ_two,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hl (l 0) with h0 | h0 <;> rcases hl (l 1) with h1 | h1 <;> rw [h0, h1] <;>
    simp only [epsilon_zero_zero, epsilon_zero_one, epsilon_one_zero, epsilon_one_one,
      conj_apply_zero_zero, conj_apply_zero_one, conj_apply_one_zero,
      conj_apply_one_one] <;>
    module

/-- The re-index of a family with two anti-fundamental indices is a bi-fundamental family
  for the same representation. -/
lemma isSU2BiFundamental_reindex {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) :
    IsSU2BiFundamental B repGauge (reindex T) where
  repGauge_T g := map_reindex (hT.repGauge_T g)

/-- Every component of the original family lies in the span of the re-indexed one. -/
lemma self_mem_span_reindex (T : (Fin 2 → Fin 2) → B) (d : Fin 2 → Fin 2) :
    T d ∈ span (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hd : T d = T ![d 0, d 1] := by rw [← eq_cons]
  rw [hd]
  rcases hl (d 0) with h0 | h0 <;> rcases hl (d 1) with h1 | h1 <;> rw [h0, h1]
  · rw [← reindex_one_one T]
    exact mem_span _
  · rw [show T ![(0 : Fin 2), 1] = -reindex T ![1, 0] from by
      rw [reindex_one_zero, neg_neg]]
    exact neg_mem (mem_span _)
  · rw [show T ![(1 : Fin 2), 0] = -reindex T ![0, 1] from by
      rw [reindex_zero_one, neg_neg]]
    exact neg_mem (mem_span _)
  · rw [← reindex_zero_zero T]
    exact mem_span _

/-- The re-index does not change the span of the components. -/
lemma span_reindex (T : (Fin 2 → Fin 2) → B) : span (reindex T) = span T := by
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun d => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, reindex]
    exact sum_mem fun m _ => sum_mem fun n _ => Submodule.smul_mem _ _ (mem_span _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact self_mem_span_reindex T d

/-!

## B.2. The epsilon contraction

The re-index exchanges the two mixed components and negates each, and the two signs cancel
in their antisymmetric combination: the invariant of `2̄ ⊗ 2̄` is the very epsilon
contraction of `IsSU2BiFundamental`.

-/

/-- The re-index leaves the epsilon contraction alone. -/
lemma epsilonContraction_reindex (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction (reindex T) = epsilonContraction T := by
  rw [epsilonContraction, reindex_zero_one, reindex_one_zero, epsilonContraction]
  abel

/-- Any map moving the components by an element of `SU(2)` in the anti-fundamental fixes
  the epsilon contraction. -/
lemma map_epsilonContraction {T : (Fin 2 → Fin 2) → B} (hf : IsSU2BiAntiFunMat U f T) :
    f (epsilonContraction T) = epsilonContraction T := by
  have h := IsSU2BiFundamental.map_epsilonContraction (map_reindex hf)
  rwa [epsilonContraction_reindex] at h

/-- The epsilon contraction is isospin invariant. -/
lemma repGauge_epsilonContraction {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, V, 1) (epsilonContraction T) = epsilonContraction T :=
  map_epsilonContraction (hT.repGauge_T V)

/-!

## B.3. The invariants modulo a stable submodule

-/

/-- An isospin invariant of the span of the components joined with an isospin-stable
  submodule `S` is a multiple of the epsilon contraction up to an isospin-invariant
  remainder in `S`. -/
theorem mem_span_sup_su2_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ V : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, V, 1) y ∈ S)
    (hx : x ∈ span T ⊔ S)
    (hinv : ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • epsilonContraction T + y
      ∧ ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) y = y := by
  obtain ⟨c, y, hyS, hxy, hyinv⟩ :=
    hT.isSU2BiFundamental_reindex.mem_span_sup_su2_invariant_iff x S hS
      (by rw [span_reindex]; exact hx) hinv
  exact ⟨c, y, hyS, by rw [hxy, epsilonContraction_reindex], hyinv⟩

end IsSU2BiAntiFun

/-!

## Aside: the gauge form of the theorem of section A, for the Higgs sector

-/

namespace IsSU2FunAntiFun

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}

/-- A gauge invariant of the span joined with a gauge-stable submodule is a multiple of the
  delta contraction up to a gauge-invariant remainder, once the delta contraction is known to
  be gauge invariant. The hypothesis on the delta contraction cannot be dropped: the law says
  nothing about the hypercharge factor, which may scale it. -/
theorem mem_span_sup_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hdc : ∀ g : GaugeGroupI, repGauge g (deltaContraction T) = deltaContraction T)
    (hx : x ∈ IsSU2BiFundamental.span T ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • deltaContraction T + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  obtain ⟨c, y, hyS, hxy, -⟩ :=
    hT.mem_span_sup_su2_invariant_iff x S (fun V => hS (1, V, 1)) hx fun V => hinv (1, V, 1)
  refine ⟨c, y, hyS, hxy, fun g => ?_⟩
  rw [show y = x - c • deltaContraction T from by rw [hxy]; abel, map_sub, map_smul,
    hinv g, hdc g]

end IsSU2FunAntiFun

end StandardModel
