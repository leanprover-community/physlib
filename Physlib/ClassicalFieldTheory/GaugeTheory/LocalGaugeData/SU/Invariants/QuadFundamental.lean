/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.Invariants.BiFundamental
/-!
# Invariants of four fundamental indices of `SU(2)`

## i. Overview

Four fundamental indices of `SU(2)` can be paired off by the antisymmetric symbol in three
ways, and the Schouten identity is one linear relation between them. The invariant tensors are
the combinations of the pairings `ε^{ab} ε^{cd}` and `ε^{ac} ε^{bd}`, `epsilonPair₁₂` and
`epsilonPair₁₃` (A, B).

Three elements of `SU(2)` pin the components `c` of an invariant tensor down (B). The phase
`diag (ω, ω̄)`, for `ω` a primitive eighth root of unity, scales `c l` by `ω` to the power of the
number of zeros of `l` plus seven times the number of ones, so only the six balanced components,
with two labels of each kind, survive. The quarter turn equates each balanced component with its
complement, leaving three unknowns. The eighth turn carries `c ![0, 0, 0, 0]` to a quarter of the
sum of the balanced components, which therefore vanishes. Two unknowns remain, and they are the
coefficients of the two pairings.

For an equivariant map out of these tensors, and for the map `fundMap T` of a family, the
invariants reduce to the span of the images of the two pairings (C).

## ii. Key results

- `suTensor.epsilonPair₁₂`, `suTensor.epsilonPair₁₃` : the two pairings.
- `suTensor.mem_span_epsilonPairs_of_invariant` : the invariant tensors lie in their span.
- `suTensor.reducesInvariantsTo_span_epsilonContractions` : the reduction of the invariants of
  the span of a family.

## iii. Table of contents

- A. The two pairings
- B. The invariant tensors
- C. The invariants of the span of a family

-/

@[expose] public section

namespace suTensor

open Matrix MatrixGroups TensorSpecies Tensor SU

/-!

## A. The two pairings

-/

/-- The antisymmetric symbol of `SU(2)` as a function of two labels. -/
def epsilon (a b : Fin 2) : ℂ := (if a = 0 ∧ b = 1 then 1 else 0) - (if a = 1 ∧ b = 0 then 1 else 0)

/-- The antisymmetric symbol is invariant: `∑ g a x g b y ε x y = det g ε a b`. -/
lemma sum_mul_epsilon (g : SU 2) (a b : Fin 2) :
    ∑ x, ∑ y, g.1 a x * g.1 b y * epsilon x y = epsilon a b := by
  have hdet := det_fin_two_eq_one g
  simp only [Fin.sum_univ_two, epsilon]
  fin_cases a <;> fin_cases b <;> simp <;>
    first | ring1 | linear_combination hdet | linear_combination (-1 : ℂ) * hdet

/-- The pairing `ε^{ab} ε^{cd}` of the first index with the second and the third with the
  fourth. -/
noncomputable def epsilonPair₁₂ : (suTensor 2).Tensor fun _ : Fin 4 => .fund :=
  ∑ l : Fin 4 → Fin 2, (epsilon (l 0) (l 1) * epsilon (l 2) (l 3)) •
    Tensor.basis (S := suTensor 2) (fun _ : Fin 4 => Color.fund) l

/-- The pairing `ε^{ac} ε^{bd}` of the first index with the third and the second with the
  fourth. -/
noncomputable def epsilonPair₁₃ : (suTensor 2).Tensor fun _ : Fin 4 => .fund :=
  ∑ l : Fin 4 → Fin 2, (epsilon (l 0) (l 2) * epsilon (l 1) (l 3)) •
    Tensor.basis (S := suTensor 2) (fun _ : Fin 4 => Color.fund) l

lemma basis_repr_epsilonPair₁₂ (l : Fin 4 → Fin 2) :
    (Tensor.basis _).repr epsilonPair₁₂ l = epsilon (l 0) (l 1) * epsilon (l 2) (l 3) := by
  rw [epsilonPair₁₂, Module.Basis.repr_sum_self]

lemma basis_repr_epsilonPair₁₃ (l : Fin 4 → Fin 2) :
    (Tensor.basis _).repr epsilonPair₁₃ l = epsilon (l 0) (l 2) * epsilon (l 1) (l 3) := by
  rw [epsilonPair₁₃, Module.Basis.repr_sum_self]

/-- A sum over four labels is a fourfold sum. -/
lemma sum_fin_four_arrow {M : Type*} [AddCommMonoid M] (F : (Fin 4 → Fin 2) → M) :
    ∑ ψ : Fin 4 → Fin 2, F ψ = ∑ x, ∑ y, ∑ z, ∑ w, F ![x, y, z, w] := by
  rw [show (∑ ψ : Fin 4 → Fin 2, F ψ)
      = ∑ p : Fin 2 × Fin 2 × Fin 2 × Fin 2, F ![p.1, p.2.1, p.2.2.1, p.2.2.2] from
        Fintype.sum_equiv
          { toFun := fun d => (d 0, d 1, d 2, d 3)
            invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
            left_inv := fun d => by funext i; fin_cases i <;> simp
            right_inv := fun p => by simp } _ _ fun d => by
          congr 1
          funext i
          fin_cases i <;> simp]
  simp only [Fintype.sum_prod_type]

/-- A product of two invariant pairings of labels is invariant. -/
lemma sum_mul_epsilon_mul_epsilon (g : SU 2) (l : Fin 4 → Fin 2) (i j k m : Fin 4)
    (hijkm : ∀ ψ : Fin 4 → Fin 2, (∏ r, g.1 (l r) (ψ r))
      = g.1 (l i) (ψ i) * g.1 (l j) (ψ j) * (g.1 (l k) (ψ k) * g.1 (l m) (ψ m)))
    (F : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 4 → Fin 2) (hF : ∀ x y z w, F x y z w i = x ∧
      F x y z w j = y ∧ F x y z w k = z ∧ F x y z w m = w)
    (hsum : ∀ G : (Fin 4 → Fin 2) → ℂ, ∑ ψ, G ψ = ∑ x, ∑ y, ∑ z, ∑ w, G (F x y z w)) :
    ∑ ψ : Fin 4 → Fin 2, (∏ r, g.1 (l r) (ψ r)) * (epsilon (ψ i) (ψ j) * epsilon (ψ k) (ψ m))
      = epsilon (l i) (l j) * epsilon (l k) (l m) := by
  rw [hsum, ← sum_mul_epsilon g (l i) (l j), ← sum_mul_epsilon g (l k) (l m),
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hF x y z w
  rw [hijkm, h1, h2, h3, h4]
  ring

/-- The pairing `ε^{ab} ε^{cd}` is invariant. -/
lemma epsilonPair₁₂_invariant (g : SU 2) : g • epsilonPair₁₂ = epsilonPair₁₂ := by
  refine (Tensor.basis _).repr.injective (Finsupp.ext fun l => ?_)
  rw [basis_repr_smul_fund, basis_repr_epsilonPair₁₂]
  simp only [basis_repr_epsilonPair₁₂]
  exact sum_mul_epsilon_mul_epsilon g l 0 1 2 3 (fun ψ => by rw [Fin.prod_univ_four]; ring)
    (fun x y z w => ![x, y, z, w]) (fun x y z w => ⟨rfl, rfl, rfl, rfl⟩) sum_fin_four_arrow

/-- The pairing `ε^{ac} ε^{bd}` is invariant. -/
lemma epsilonPair₁₃_invariant (g : SU 2) : g • epsilonPair₁₃ = epsilonPair₁₃ := by
  refine (Tensor.basis _).repr.injective (Finsupp.ext fun l => ?_)
  rw [basis_repr_smul_fund, basis_repr_epsilonPair₁₃]
  simp only [basis_repr_epsilonPair₁₃]
  refine sum_mul_epsilon_mul_epsilon g l 0 2 1 3 (fun ψ => by rw [Fin.prod_univ_four]; ring)
    (fun x y z w => ![x, z, y, w]) (fun x y z w => ⟨rfl, rfl, rfl, rfl⟩) fun G => ?_
  rw [sum_fin_four_arrow]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Finset.sum_comm

/-!

## B. The invariant tensors

-/

section Components

variable {c : (Fin 4 → Fin 2) → ℂ}
  (hc : ∀ (g : SU 2) (l : Fin 4 → Fin 2), c l = ∑ ψ, (∏ i, g.1 (l i) (ψ i)) * c ψ)

include hc in
/-- The phase `diag (ω, ω̄)`, with `ω` a primitive eighth root of unity, scales the component at
  `l` by `ω` to the power of the number of zeros of `l` plus seven times the number of ones, so
  the component vanishes unless that power is a multiple of eight. -/
lemma eq_zero_of_not_dvd (l : Fin 4 → Fin 2) (hl : ¬ 8 ∣ ∑ i, ![1, 7] (l i)) : c l = 0 := by
  have hω := rootOfUnity_isPrimitiveRoot (N := 8) (by norm_num)
  have hstar : star (rootOfUnity 8) = rootOfUnity 8 ^ 7 := by
    have h := congrArg (rootOfUnity 8 ^ 7 * ·) (rootOfUnity_mul_star (N := 8))
    simp only [mul_one] at h
    rw [← h, ← mul_assoc, ← pow_succ, hω.pow_eq_one, one_mul]
  have hd : (diagPhase (rootOfUnity 8) rootOfUnity_mul_star).1
      = diagonal fun x => rootOfUnity 8 ^ (![1, 7] x) := by
    rw [diagPhase_val, hstar]
    congr 1
    funext x
    fin_cases x <;> simp
  have h := hc (diagPhase (rootOfUnity 8) rootOfUnity_mul_star) l
  rw [Finset.sum_eq_single l (fun ψ _ hψ => by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hψ
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi]), zero_mul])
    (by simp), hd] at h
  simp only [diagonal_apply_eq, Finset.prod_pow_eq_pow_sum] at h
  have hne : rootOfUnity 8 ^ (∑ i, ![1, 7] (l i)) ≠ 1 := fun h' =>
    hl ((hω.pow_eq_one_iff_dvd _).1 h')
  have h' : (1 - rootOfUnity 8 ^ (∑ i, ![1, 7] (l i))) * c l = 0 := by
    linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hne.symm)

include hc in
/-- The quarter turn equates each balanced component with its complement. -/
lemma quarterTurn_relations :
    c ![0, 0, 1, 1] = c ![1, 1, 0, 0] ∧ c ![0, 1, 0, 1] = c ![1, 0, 1, 0] ∧
      c ![0, 1, 1, 0] = c ![1, 0, 0, 1] := by
  have h := fun l => hc (rotation 0 1 (by norm_num)) l
  have h1 := h ![0, 0, 1, 1]
  have h2 := h ![0, 1, 0, 1]
  have h3 := h ![0, 1, 1, 0]
  simp only [sum_fin_four_arrow, Fin.sum_univ_two, Fin.prod_univ_four, rotation_val] at h1 h2 h3
  simp at h1 h2 h3
  exact ⟨h1, h2, h3⟩

include hc in
/-- The ten unbalanced components vanish. -/
lemma unbalanced_eq_zero :
    c ![0, 0, 0, 0] = 0 ∧ c ![0, 0, 0, 1] = 0 ∧ c ![0, 0, 1, 0] = 0 ∧ c ![0, 1, 0, 0] = 0 ∧
      c ![1, 0, 0, 0] = 0 ∧ c ![0, 1, 1, 1] = 0 ∧ c ![1, 0, 1, 1] = 0 ∧ c ![1, 1, 0, 1] = 0 ∧
      c ![1, 1, 1, 0] = 0 ∧ c ![1, 1, 1, 1] = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact eq_zero_of_not_dvd hc _ (by norm_num [Fin.sum_univ_four])

include hc in
/-- The eighth turn carries the component at `![0, 0, 0, 0]` to a quarter of the sum of the
  balanced components, so that sum vanishes. -/
lemma sum_balanced_eq_zero :
    c ![0, 0, 1, 1] + c ![0, 1, 0, 1] + c ![0, 1, 1, 0] + c ![1, 0, 0, 1] + c ![1, 0, 1, 0]
      + c ![1, 1, 0, 0] = 0 := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := unbalanced_eq_zero hc
  have h := hc (rotation invSqrtTwo invSqrtTwo invSqrtTwo_sq_add) ![0, 0, 0, 0]
  simp only [sum_fin_four_arrow, Fin.sum_univ_two, Fin.prod_univ_four, rotation_val] at h
  simp [z1, z2, z3, z4, z5, z6, z7, z8, z9, z10] at h
  linear_combination (-4 : ℂ) * h - 2 * (c ![0, 0, 1, 1] + c ![0, 1, 0, 1] + c ![0, 1, 1, 0]
    + c ![1, 0, 0, 1] + c ![1, 0, 1, 0] + c ![1, 1, 0, 0])
    * (1 + 2 * (invSqrtTwo : ℂ) * invSqrtTwo) * invSqrtTwo_mul_self

include hc in
/-- An invariant function of four labels is a combination of the two pairings, with the
  components at `![0, 1, 0, 1]` and `![0, 0, 1, 1]` as coefficients. -/
lemma eq_add_of_pairings (l : Fin 4 → Fin 2) :
    c l = c ![0, 1, 0, 1] * (epsilon (l 0) (l 1) * epsilon (l 2) (l 3))
      + c ![0, 0, 1, 1] * (epsilon (l 0) (l 2) * epsilon (l 1) (l 3)) := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := unbalanced_eq_zero hc
  obtain ⟨r1, r2, r3⟩ := quarterTurn_relations hc
  have hs := sum_balanced_eq_zero hc
  obtain ⟨a, b, d, e, rfl⟩ : ∃ a b d e : Fin 2, l = ![a, b, d, e] :=
    ⟨l 0, l 1, l 2, l 3, by funext i; fin_cases i <;> rfl⟩
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
    simp [epsilon, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10] <;>
    first
      | linear_combination r1 | linear_combination -r1 | linear_combination r2
      | linear_combination -r2 | linear_combination (hs + r1 + r2 + r3) / 2
      | linear_combination (hs + r1 + r2 + r3) / 2 - r3

end Components

/-- An invariant tensor with four fundamental indices of `SU(2)` is a combination of the two
  pairings of its indices by the antisymmetric symbol. -/
lemma mem_span_epsilonPairs_of_invariant (t : (suTensor 2).Tensor fun _ : Fin 4 => .fund)
    (ht : ∀ g : SU 2, g • t = t) :
    t ∈ Submodule.span ℂ {epsilonPair₁₂, epsilonPair₁₃} := by
  have hc : ∀ (g : SU 2) (l : Fin 4 → Fin 2), (Tensor.basis _).repr t l
      = ∑ ψ, (∏ i, g.1 (l i) (ψ i)) * (Tensor.basis _).repr t ψ := fun g l => by
    rw [← basis_repr_smul_fund, ht]
  refine Submodule.mem_span_pair.2 ⟨(Tensor.basis _).repr t ![0, 1, 0, 1],
    (Tensor.basis _).repr t ![0, 0, 1, 1],
    (Tensor.basis _).repr.injective (Finsupp.ext fun l => ?_)⟩
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, basis_repr_epsilonPair₁₂,
    basis_repr_epsilonPair₁₃, smul_eq_mul]
  exact (eq_add_of_pairings hc l).symm

/-!

## C. The invariants of the span of a family

-/

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ (SU 2) B}

/-- For an equivariant map `f` out of the tensors with four fundamental indices of `SU(2)`, the
  invariants of the range reduce to the span of the images of the two pairings. -/
lemma reducesInvariantsTo_span_map_epsilonPairs
    {f : (suTensor 2).Tensor (fun _ : Fin 4 => .fund) →ₗ[ℂ] B}
    (hf : (suTensor 2).IsEquivariant (fun _ => .fund) ρ f) :
    ReducesInvariantsTo (fun g : SU 2 => ρ g) (LinearMap.range f)
      (Submodule.span ℂ {f epsilonPair₁₂, f epsilonPair₁₃}) := by
  have h := hf.reducesInvariantsTo_map (isAdjointClosed 2 _)
    (Submodule.span ℂ {epsilonPair₁₂, epsilonPair₁₃}) mem_span_epsilonPairs_of_invariant
  rwa [Submodule.map_span, Set.image_pair] at h

/-- The map of a family sends the first pairing to the contraction pairing the first label with
  the second and the third with the fourth. -/
lemma fundMap_epsilonPair₁₂ (T : (Fin 4 → Fin 2) → B) :
    fundMap T epsilonPair₁₂
      = T ![0, 1, 0, 1] - T ![0, 1, 1, 0] - T ![1, 0, 0, 1] + T ![1, 0, 1, 0] := by
  simp only [epsilonPair₁₂, map_sum, map_smul, fundMap_basis, sum_fin_four_arrow,
    Fin.sum_univ_two, epsilon]
  simp
  abel

/-- The map of a family sends the second pairing to the contraction pairing the first label with
  the third and the second with the fourth. -/
lemma fundMap_epsilonPair₁₃ (T : (Fin 4 → Fin 2) → B) :
    fundMap T epsilonPair₁₃
      = T ![0, 0, 1, 1] - T ![0, 1, 1, 0] - T ![1, 0, 0, 1] + T ![1, 1, 0, 0] := by
  simp only [epsilonPair₁₃, map_sum, map_smul, fundMap_basis, sum_fin_four_arrow,
    Fin.sum_univ_two, epsilon]
  simp
  abel

/-- For a family with four fundamental labels of `SU(2)` whose map is equivariant, the invariants
  of the span of the family reduce to the span of its two epsilon contractions. -/
lemma reducesInvariantsTo_span_epsilonContractions {T : (Fin 4 → Fin 2) → B}
    (hT : (suTensor 2).IsEquivariant (fun _ => .fund) ρ (fundMap T)) :
    ReducesInvariantsTo (fun g : SU 2 => ρ g) (Submodule.span ℂ (Set.range T))
      (Submodule.span ℂ
        {T ![0, 1, 0, 1] - T ![0, 1, 1, 0] - T ![1, 0, 0, 1] + T ![1, 0, 1, 0],
          T ![0, 0, 1, 1] - T ![0, 1, 1, 0] - T ![1, 0, 0, 1] + T ![1, 1, 0, 0]}) := by
  rw [← fundMap_epsilonPair₁₂, ← fundMap_epsilonPair₁₃,
    ← range_familyMap (S := suTensor 2) (c := fun _ : Fin 4 => Color.fund) (Equiv.refl _) T]
  exact reducesInvariantsTo_span_map_epsilonPairs hT

end suTensor
