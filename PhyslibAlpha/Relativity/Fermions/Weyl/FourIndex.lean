/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Mathematics.ForMathlib.Fin
public import PhyslibAlpha.Mathematics.RepresentationTheory.SlotAction
public import PhyslibAlpha.Relativity.Fermions.Weyl.Metric
public import Mathlib.Analysis.Complex.RealDeriv
/-!
# Invariants of four Weyl indices

The invariants of four left-handed Weyl indices are spanned by two products of Weyl metrics.

## i. Overview

A coefficient function `C : (Fin n → Fin 2) → ℂ` of `n` left-handed Weyl indices carries the action
of `M ∈ SL(2, ℂ)` on each index, `SlotAction.act M C`. With four indices the products of two Weyl
metrics `ε_{ab} = metricRaw`, pairing the slots `ε_{a₀a₁} ε_{a₂a₃}`, `ε_{a₀a₂} ε_{a₁a₃}` and
`ε_{a₀a₃} ε_{a₁a₂}`, are invariant. They obey the Schouten identity
`ε₀₁ ε₂₃ - ε₀₂ ε₁₃ + ε₀₃ ε₁₂ = 0` (A), and the first two span all invariants (C).

The argument is infinitesimal. The unipotent elements `1 + z E` and `1 + z F` of `SL(2, ℂ)`, with
`E = !![0, 1; 0, 0]` and `F = !![0, 0; 1, 0]`, move a fixed coefficient function along a line, so
it is killed by the infinitesimal actions of `E` and `F`, one slot at a time (B). For four
indices those two conditions are linear equations on the sixteen coefficients. They force every
coefficient with more raised than lowered indices, or fewer, to vanish, and leave the six balanced
ones in a two-dimensional space. The two coefficients at `1100` and `1010` fix all the others
(`eq_sum_pairingBasis_of_infAct_eq_zero`). This form, in terms of `E` and `F` alone, is what the
bispinor results of `PhyslibAlpha.Relativity.Bispinors.Invariants` use, one chirality at a time.
The right-handed and the two dual Weyl representations have the same invariants, the group acting
on them through a reparametrisation of itself (C.3). On two indices the same equations leave only
the multiples of the metric (D).

## ii. Key results

- `Fermion.metricPairing` : a product of two Weyl metrics on four indices.
- `Fermion.metricPairing_schouten` : the Schouten identity.
- `Fermion.eq_sum_pairingBasis_of_infAct_eq_zero` : a coefficient function killed by `E` and `F`
  is a combination of `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`.
- `Fermion.infAct_eq_zero_of_invariant` : an invariant coefficient function is killed by `E` and
  `F`.
- `Fermion.mem_span_pairingBasis_iff` : the invariants of four left-handed Weyl indices are the span
  of `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`.
- `Fermion.linearIndependent_pairingBasis` : the two are linearly independent.
- `Fermion.mem_span_pairingBasis_iff_map_star` and its two siblings : the same for right-handed,
  dual left-handed and dual right-handed indices.
- `Fermion.eq_smul_metricCoeff_of_infAct_eq_zero` : on two Weyl indices `E` and `F` leave only the
  multiples of the metric.

## iii. Table of contents

- A. Products of Weyl metrics
- B. The unipotent elements
- C. Four Weyl indices
  - C.1. The infinitesimal equations
  - C.2. The invariants
  - C.3. The other Weyl representations
- D. Two Weyl indices

## iv. References

* None.

-/

@[expose] public section

namespace Fermion

open Matrix MatrixGroups SlotAction

/-!

## A. Products of Weyl metrics

-/

/-- The product `ε_{a_i a_j} ε_{a_k a_l}` of two Weyl metrics on four Weyl indices, pairing the
  slots `i, j` and `k, l`. -/
def metricPairing (i j k l : Fin 4) (a : Fin 4 → Fin 2) : ℂ :=
  metricRaw (a i) (a j) * metricRaw (a k) (a l)

/-- Every index vector of four slots is a vector literal. -/
lemma exists_eq_vecCons {α : Type*} (a : Fin 4 → α) : ∃ w x y z, a = ![w, x, y, z] :=
  ⟨a 0, a 1, a 2, a 3, by funext i; fin_cases i <;> rfl⟩

/-- The Schouten identity `ε₀₁ ε₂₃ - ε₀₂ ε₁₃ + ε₀₃ ε₁₂ = 0`. Two-component spinors admit no
  totally antisymmetric tensor of rank three. -/
lemma metricPairing_schouten :
    metricPairing 0 1 2 3 - metricPairing 0 2 1 3 + metricPairing 0 3 1 2 = 0 := by
  funext a
  obtain ⟨w, x, y, z, rfl⟩ := exists_eq_vecCons a
  fin_cases w <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [metricPairing, metricRaw]

/-- The two pairings spanning the invariants of four Weyl indices, `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`. -/
def pairingBasis : Fin 2 → (Fin 4 → Fin 2) → ℂ := ![metricPairing 0 2 1 3, metricPairing 0 1 2 3]

/-- Two index vectors, `1100` and `1010`, on which `pairingBasis` is the unit matrix. -/
def pairingPoint : Fin 2 → Fin 4 → Fin 2 := ![![1, 1, 0, 0], ![1, 0, 1, 0]]

/-- The two basis pairings evaluated at the two test points form the unit matrix. -/
lemma pairingBasis_pairingPoint (i j : Fin 2) :
    pairingBasis i (pairingPoint j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [pairingBasis, pairingPoint, metricPairing, metricRaw]

/-- The two pairings are linearly independent. -/
lemma linearIndependent_pairingBasis : LinearIndependent ℂ pairingBasis := by
  refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
  have h := congrFun hg (pairingPoint i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pairingBasis_pairingPoint, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply] at h
  exact h

/-!

## B. The unipotent elements

-/

/-- The unipotent element `!![1, z; 0, 1] = 1 + z E` of `SL(2, ℂ)`. -/
def upperUnipotent (z : ℂ) : SL(2,ℂ) :=
  ⟨1 + z • !![0, 1; 0, 0], by simp [det_fin_two, one_apply]⟩

/-- The unipotent element `!![1, 0; z, 1] = 1 + z F` of `SL(2, ℂ)`. -/
def lowerUnipotent (z : ℂ) : SL(2,ℂ) :=
  ⟨1 + z • !![0, 0; 1, 0], by simp [det_fin_two, one_apply]⟩

/-- At `t = 0` the line `t ↦ 1 + c t G` is the identity. -/
lemma one_add_smul_zero_apply (G : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (p q : Fin 2) :
    (1 + (c * ((0 : ℝ) : ℂ)) • G) p q = if p = q then 1 else 0 := by
  simp [one_apply]

/-- The line `t ↦ 1 + c t G` has derivative `c G`. -/
lemma hasDerivAt_one_add_smul (G : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (p q : Fin 2) :
    HasDerivAt (fun t : ℝ => (1 + (c * (t : ℂ)) • G) p q) ((c • G) p q) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c).mul_const (G p q)).const_add
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) p q)
  simpa [mul_assoc] using h

/-!

## C. Four Weyl indices

### C.1. The infinitesimal equations

-/

/-- An invariant coefficient function of `n` Weyl indices is killed by the infinitesimal actions
  of `E` and `F`, the derivatives of the unipotent lines. -/
lemma infAct_eq_zero_of_invariant {n : ℕ} {C : (Fin n → Fin 2) → ℂ}
    (hC : ∀ M : SL(2,ℂ), act M.1 C = C) :
    infAct !![0, 1; 0, 0] C = 0 ∧ infAct !![0, 0; 1, 0] C = 0 := by
  constructor
  · simpa using infAct_eq_zero_of_act_eq (one_add_smul_zero_apply _ 1)
      (hasDerivAt_one_add_smul _ 1) fun t => hC (upperUnipotent (1 * t))
  · simpa using infAct_eq_zero_of_act_eq (one_add_smul_zero_apply _ 1)
      (hasDerivAt_one_add_smul _ 1) fun t => hC (lowerUnipotent (1 * t))

/-- The infinitesimal action at four Weyl indices, written out slot by slot. -/
lemma infAct_four (N : Fin 2 → Fin 2 → ℂ) (C : (Fin 4 → Fin 2) → ℂ) (w x y z : Fin 2) :
    infAct N C ![w, x, y, z] = ∑ q, (N w q * C ![q, x, y, z] + N x q * C ![w, q, y, z]
      + N y q * C ![w, x, q, z] + N z q * C ![w, x, y, q]) := by
  have hu : ∀ (s : Fin 4) (q : Fin 2), Function.update ![w, x, y, z] s q
      = ![if s = 0 then q else w, if s = 1 then q else x, if s = 2 then q else y,
        if s = 3 then q else z] := by
    intro s q
    funext i
    fin_cases s <;> fin_cases i <;> rfl
  simp only [infAct, Fin.sum_univ_four, hu, ← Finset.sum_add_distrib]
  simp

/-- A coefficient function of four Weyl indices killed by `E` and `F` is a combination of
  `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`, with its values at `1100` and `1010` as coefficients. The equations
  of `E` at `0111`, of `F` at `1000` and their neighbours kill the unbalanced coefficients, and
  those of `E` at the four index vectors with a single raised slot relate the six balanced ones. -/
lemma eq_sum_pairingBasis_of_infAct_eq_zero {C : (Fin 4 → Fin 2) → ℂ}
    (hE : infAct !![0, 1; 0, 0] C = 0) (hF : infAct !![0, 0; 1, 0] C = 0) :
    C = ∑ i, C (pairingPoint i) • pairingBasis i := by
  have e := fun w x y z => (infAct_four _ C w x y z).symm.trans (congrFun hE ![w, x, y, z])
  have f := fun w x y z => (infAct_four _ C w x y z).symm.trans (congrFun hF ![w, x, y, z])
  have e0111 := e 0 1 1 1; have e0011 := e 0 0 1 1; have e0101 := e 0 1 0 1
  have e0110 := e 0 1 1 0; have e1001 := e 1 0 0 1; have e1010 := e 1 0 1 0
  have e1000 := e 1 0 0 0; have e0100 := e 0 1 0 0; have e0010 := e 0 0 1 0
  have e0001 := e 0 0 0 1; have f1000 := f 1 0 0 0; have f1100 := f 1 1 0 0
  have f1010 := f 1 0 1 0; have f0110 := f 0 1 1 0; have f1001 := f 1 0 0 1
  have f0011 := f 0 0 1 1
  simp [Fin.sum_univ_two] at e0111 e0011 e0101 e0110 e1001 e1010 e1000 e0100 e0010 e0001
  simp [Fin.sum_univ_two] at f1000 f1100 f1010 f0110 f1001 f0011
  funext a
  obtain ⟨w, x, y, z, rfl⟩ := exists_eq_vecCons a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  fin_cases w <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [pairingBasis, pairingPoint, metricPairing, metricRaw]
  · linear_combination f1000
  · linear_combination (f1001 + f0011 - f1010) / 2
  · linear_combination (f1010 + f0110 - f1100) / 2
  · linear_combination (e0010 + e0001 - e1000 - e0100) / 2
  · linear_combination (f1100 + f0110 - f1010) / 2
  · linear_combination (e0100 + e0001 - e1000 - e0010) / 2
  · linear_combination (e1000 + e0100 + e0010 - e0001) / 2
  · linear_combination (e0011 + e0101 - e1001) / 2
  · linear_combination (f1100 + f1010 - f0110) / 2
  · linear_combination e1000
  · linear_combination (e0011 + e1001 - e0101) / 2
  · linear_combination (e0101 + e1001 - e0011) / 2
  · linear_combination (e0110 + e1010 - e0011) / 2
  · linear_combination e0111

/-!

### C.2. The invariants

The pairings are invariant because `M ε Mᵀ = (det M) ε`, applied to each pair of slots.

-/

/-- The Weyl metric against two rows of a matrix gives the determinant times the metric. -/
lemma sum_metricRaw_mul (M : Matrix (Fin 2) (Fin 2) ℂ) (p q : Fin 2) :
    ∑ x, ∑ z, metricRaw x z * (M p x * M q z) = M.det * metricRaw p q := by
  fin_cases p <;> fin_cases q <;> simp [metricRaw, det_fin_two, Fin.sum_univ_two] <;> ring

/-- A sum over index vectors of four slots is a fourfold sum. -/
lemma sum_pi_four {β : Type*} [AddCommMonoid β] (F : (Fin 4 → Fin 2) → β) :
    ∑ d, F d = ∑ w, ∑ x, ∑ y, ∑ z, F ![w, x, y, z] := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ F fun _ => rfl]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ _ fun _ => rfl]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ _ fun _ => rfl]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ _ fun _ => rfl]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fintype.sum_unique]
  rfl

/-- The pairing `ε₀₂ ε₁₃` is invariant. -/
lemma act_metricPairing_zero_two (M : SL(2,ℂ)) :
    act M.1 (metricPairing 0 2 1 3) = metricPairing 0 2 1 3 := by
  funext a
  simp only [act]
  rw [sum_pi_four]
  have h := congrArg₂ (· * ·) (sum_metricRaw_mul M.1 (a 0) (a 2))
    (sum_metricRaw_mul M.1 (a 1) (a 3))
  simp only [M.2, one_mul] at h
  rw [metricPairing, ← h]
  simp [metricPairing, Fin.prod_univ_four, Fin.sum_univ_two, metricRaw]
  ring

/-- The pairing `ε₀₁ ε₂₃` is invariant. -/
lemma act_metricPairing_zero_one (M : SL(2,ℂ)) :
    act M.1 (metricPairing 0 1 2 3) = metricPairing 0 1 2 3 := by
  funext a
  simp only [act]
  rw [sum_pi_four]
  have h := congrArg₂ (· * ·) (sum_metricRaw_mul M.1 (a 0) (a 1))
    (sum_metricRaw_mul M.1 (a 2) (a 3))
  simp only [M.2, one_mul] at h
  rw [metricPairing, ← h]
  simp [metricPairing, Fin.prod_univ_four, Fin.sum_univ_two, metricRaw]
  ring

/-- The invariants of four left-handed Weyl indices are the span of `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`. -/
lemma mem_span_pairingBasis_iff (C : (Fin 4 → Fin 2) → ℂ) :
    (∀ M : SL(2,ℂ), act M.1 C = C) ↔ C ∈ Submodule.span ℂ (Set.range pairingBasis) := by
  constructor
  · intro hC
    obtain ⟨hE, hF⟩ := infAct_eq_zero_of_invariant hC
    rw [eq_sum_pairingBasis_of_infAct_eq_zero hE hF]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hC M
    refine Submodule.span_induction (p := fun C _ => act M.1 C = C) ?_ ?_ ?_ ?_ hC
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact act_metricPairing_zero_two M
      · exact act_metricPairing_zero_one M
    · funext a
      simp [act]
    · intro C C' _ _ h h'
      funext a
      have ha := congrFun h a
      have ha' := congrFun h' a
      simp only [act, Pi.add_apply, add_mul, Finset.sum_add_distrib] at ha ha' ⊢
      rw [ha, ha']
    · intro k C _ h
      funext a
      have ha := congrFun h a
      simp only [act, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum] at ha ⊢
      rw [ha]


/-!

### C.3. The other Weyl representations

On right-handed, dual left-handed and dual right-handed indices `M` acts through its conjugate,
`(M⁻¹)ᵀ` and `(M⁻¹)ᴴ`. Each of these runs over all of `SL(2, ℂ)` as `M` does
(`Fermion.map_star_coe_map_starRingEnd`, `Fermion.inv_coe_transpose_inv`,
`Fermion.conjTranspose_inv_coe_transpose_inv_map`), so their invariants are the same span.

-/

/-- The invariants of four right-handed Weyl indices are the span of `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`. -/
lemma mem_span_pairingBasis_iff_map_star (C : (Fin 4 → Fin 2) → ℂ) :
    (∀ M : SL(2,ℂ), act (M.1.map star) C = C)
      ↔ C ∈ Submodule.span ℂ (Set.range pairingBasis) := by
  rw [← mem_span_pairingBasis_iff]
  refine ⟨fun h N => ?_, fun h M => h (SpecialLinearGroup.map (starRingEnd ℂ) M)⟩
  have h' := h (SpecialLinearGroup.map (starRingEnd ℂ) N)
  rwa [map_star_coe_map_starRingEnd] at h'

/-- The invariants of four dual left-handed Weyl indices are the span of `ε₀₂ ε₁₃` and
  `ε₀₁ ε₂₃`. -/
lemma mem_span_pairingBasis_iff_inv_transpose (C : (Fin 4 → Fin 2) → ℂ) :
    (∀ M : SL(2,ℂ), act (M.1⁻¹)ᵀ C = C) ↔ C ∈ Submodule.span ℂ (Set.range pairingBasis) := by
  rw [← mem_span_pairingBasis_iff]
  refine ⟨fun h N => ?_, fun h M => ?_⟩
  · have h' := h N.transpose⁻¹
    rwa [inv_coe_transpose_inv, transpose_transpose] at h'
  · have h' := h (M⁻¹).transpose
    rwa [SpecialLinearGroup.coe_transpose, ← Lorentz.SL2C.inverse_coe] at h'

/-- The invariants of four dual right-handed Weyl indices are the span of `ε₀₂ ε₁₃` and
  `ε₀₁ ε₂₃`. -/
lemma mem_span_pairingBasis_iff_inv_conjTranspose (C : (Fin 4 → Fin 2) → ℂ) :
    (∀ M : SL(2,ℂ), act (M.1⁻¹)ᴴ C = C) ↔ C ∈ Submodule.span ℂ (Set.range pairingBasis) := by
  rw [← mem_span_pairingBasis_iff]
  refine ⟨fun h N => ?_, fun h M => ?_⟩
  · have h' := h (SpecialLinearGroup.map (starRingEnd ℂ) N).transpose⁻¹
    rwa [conjTranspose_inv_coe_transpose_inv_map] at h'
  · have he : (M.1⁻¹)ᴴ = (SpecialLinearGroup.map (starRingEnd ℂ) (M⁻¹).transpose).1 := by
      ext i j
      rw [Lorentz.SL2C.inverse_coe]
      rfl
    rw [he]
    exact h _

/-!

## D. Two Weyl indices

On two indices the equations of `E` and `F` leave only the multiples of the metric
`ε_{a₀ a₁}`. This is the infinitesimal form of the uniqueness of the Weyl metric
(`Fermion.LeftHandedWeyl.invariants_tprod_eq_span_metricVal`), used for two bispinor indices.

-/

/-- The Weyl metric `ε_{a₀ a₁}` as a coefficient function of two Weyl indices. -/
def metricCoeff (a : Fin 2 → Fin 2) : ℂ := metricRaw (a 0) (a 1)

/-- A coefficient function of two Weyl indices killed by `E` and `F` is a multiple of the
  metric. The equation of `E` at `01` kills `C₁₁`, that of `F` at `10` kills `C₀₀`, and that of
  `E` at `00` gives `C₁₀ = -C₀₁`. -/
lemma eq_smul_metricCoeff_of_infAct_eq_zero {C : (Fin 2 → Fin 2) → ℂ}
    (hE : infAct !![0, 1; 0, 0] C = 0) (hF : infAct !![0, 0; 1, 0] C = 0) :
    C = C ![0, 1] • metricCoeff := by
  have hu : ∀ x y s q : Fin 2, Function.update ![x, y] s q
      = ![if s = 0 then q else x, if s = 1 then q else y] := by
    intro x y s q
    funext i
    fin_cases s <;> fin_cases i <;> rfl
  have e01 := congrFun hE ![0, 1]
  have e00 := congrFun hE ![0, 0]
  have f10 := congrFun hF ![1, 0]
  simp [infAct, Fin.sum_univ_two, hu] at e01 e00 f10
  funext a
  obtain ⟨x, y, rfl⟩ : ∃ x y, a = ![x, y] := ⟨a 0, a 1, by funext i; fin_cases i <;> rfl⟩
  fin_cases x <;> fin_cases y <;> simp [metricCoeff, metricRaw]
  · linear_combination f10
  · linear_combination e00
  · linear_combination e01

/-- The metric is invariant, `M ε Mᵀ = (det M) ε`. -/
lemma act_metricCoeff (M : SL(2,ℂ)) : act M.1 metricCoeff = metricCoeff := by
  funext a
  have h := sum_metricRaw_mul M.1 (a 0) (a 1)
  rw [M.2, one_mul] at h
  simpa [act, Physlib.Fin.sum_fin_two_arrow, metricCoeff, Fin.prod_univ_two, mul_assoc] using h

/-- The invariants of two left-handed Weyl indices are the multiples of the metric. -/
lemma mem_span_metricCoeff_iff (C : (Fin 2 → Fin 2) → ℂ) :
    (∀ M : SL(2,ℂ), act M.1 C = C) ↔ C ∈ ℂ ∙ metricCoeff := by
  constructor
  · intro hC
    obtain ⟨hE, hF⟩ := infAct_eq_zero_of_invariant hC
    rw [eq_smul_metricCoeff_of_infAct_eq_zero hE hF]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro hC M
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.1 hC
    funext a
    have ha := congrFun (act_metricCoeff M) a
    simp only [act, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum] at ha ⊢
    rw [ha]

end Fermion
