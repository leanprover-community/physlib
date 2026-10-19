/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Classification

/-!
# Weight spaces for sl₂ modules

Restates the rank-one weight-space results using endomorphism eigenspaces.

## i. Overview

The eigenspaces of the Cartan operator are weight spaces. The raising and lowering
operators map them to neighboring weights. In a finite-dimensional irreducible module the
weights in a primitive string occur with multiplicity one, and the highest weight is unique.

## ii. Key results

- `weightSpace` defines the Cartan eigenspace.
- `e_mapsTo_weightSpace` and `f_mapsTo_weightSpace` shift weights by two.
- `weightSpace_finrank_le_one` and `weightSpace_highest_unique` express multiplicity one
  and uniqueness of the highest weight.

## iii. Table of contents

- A. Weight spaces

## iv. References

- Mathlib, `Mathlib.Algebra.Lie.Sl2`.

## A. Weight spaces
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] {h e f : L}

/-- The eigenspace of the Cartan operator `h` with eigenvalue `n`. -/
def weightSpace (_t : IsSl2Triple h e f) (n : K) : Submodule K M :=
  Module.End.eigenspace (LieModule.toEnd K L M h) n

/-- The raising operator maps weight `n` into weight `n + 2`. -/
lemma e_mapsTo_weightSpace (t : IsSl2Triple h e f) (n : K) :
    ∀ v ∈ weightSpace (M := M) t n, LieModule.toEnd K L M e v ∈ weightSpace t (n + 2) := by
  intro v hv
  simp only [weightSpace, Module.End.mem_eigenspace_iff, LieModule.toEnd_apply_apply] at hv ⊢
  rw [leibniz_lie, t.lie_h_e_smul (R := K), hv, smul_lie, lie_smul]
  module

/-- `f` lowers the weight by `2`. Dual to `e_mapsTo_weightSpace`. -/
lemma f_mapsTo_weightSpace (t : IsSl2Triple h e f) (n : K) :
    ∀ v ∈ weightSpace (M := M) t n, LieModule.toEnd K L M f v ∈ weightSpace t (n - 2) := by
  intro v hv
  simp only [weightSpace, Module.End.mem_eigenspace_iff, LieModule.toEnd_apply_apply] at hv ⊢
  rw [leibniz_lie, t.lie_lie_smul_f (R := K), neg_lie, hv, smul_lie, lie_smul]
  module

omit [LieModule K L M] in
/-- If a basis diagonalises `T`, then `T` multiplies the `i`-th coordinate by `μ i`. -/
lemma repr_apply_diag {ι : Type*} (b : Module.Basis ι K M) (T : Module.End K M)
    (μ : ι → K) (hT : ∀ j, T (b j) = μ j • b j) (i : ι) (w : M) :
    b.repr (T w) i = μ i * b.repr w i := by
  have key : (Finsupp.lapply i ∘ₗ b.repr.toLinearMap) ∘ₗ T =
      μ i • (Finsupp.lapply i ∘ₗ b.repr.toLinearMap) := by
    refine b.ext fun j => ?_
    by_cases hji : j = i <;> simp [hT, hji]
  simpa using congrArg (fun S => S w) key

section Weights

variable [CharZero K] [FiniteDimensional K M] {t : IsSl2Triple h e f}
    [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M]
    {m₀ : M} {N : ℕ} (P : t.HasPrimitiveVectorWith m₀ (N : K))

include P

/-- A weight vector has vanishing string coordinates at every other weight. -/
lemma string_coord_eq_zero {n : K} {w : M} (hw : w ∈ weightSpace (M := M) t n)
    (i : Fin (N + 1)) (hi : (N : K) - 2 * (i : ℕ) ≠ n) : (stringBasis P).repr w i = 0 := by
  have hT : ∀ j, LieModule.toEnd K L M h (stringBasis P j) =
      ((N : K) - 2 * (j : ℕ)) • stringBasis P j := fun j => by
    rw [stringBasis, Module.Basis.mk_apply, LieModule.toEnd_apply_apply]
    exact P.lie_h_pow_toEnd_f j
  have h1 := repr_apply_diag (stringBasis P) _ _ hT i w
  rw [(Module.End.mem_eigenspace_iff.mp hw), map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  exact (mul_eq_zero.mp (by linear_combination h1 : (n - ((N : K) - 2 * (i : ℕ))) *
    (stringBasis P).repr w i = 0)).resolve_left (sub_ne_zero.mpr hi.symm)

/-- The weight space is trivial at a value that is not a weight of the string. -/
lemma weightSpace_eq_bot_of_ne {n : K} (hn : ∀ i : Fin (N + 1), (N : K) - 2 * (i : ℕ) ≠ n) :
    weightSpace (M := M) t n = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
  apply (stringBasis P).repr.injective
  refine Finsupp.ext fun i => ?_
  simpa using string_coord_eq_zero P hw i (hn i)

/-- The weight space of a weight of the string has dimension at most one. -/
lemma weightSpace_finrank_le_one_of_eq {n : K} (i₀ : Fin (N + 1))
    (hi₀ : (N : K) - 2 * (i₀ : ℕ) = n) : Module.finrank K (weightSpace (M := M) t n) ≤ 1 := by
  have hinj : Function.Injective ((Finsupp.lapply i₀ ∘ₗ (stringBasis P).repr.toLinearMap) ∘ₗ
      (weightSpace (M := M) t n).subtype) := by
    rw [injective_iff_map_eq_zero]
    intro w hw0
    refine Subtype.ext ((stringBasis P).repr.injective (Finsupp.ext fun i => ?_))
    by_cases hi : i = i₀
    · subst hi; simpa using hw0
    · simpa using string_coord_eq_zero P w.2 i
        (fun h' => hi (string_weight_injective (h'.trans hi₀.symm)))
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

end Weights

/-- Every Cartan weight space of a finite-dimensional irreducible `sl₂` module has
dimension at most one. The lowering-string basis has pairwise distinct weights. -/
lemma weightSpace_finrank_le_one [IsAlgClosed K] [CharZero K] [FiniteDimensional K M]
    (t : IsSl2Triple h e f) [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M]
    (n : K) : Module.finrank K (weightSpace (M := M) t n) ≤ 1 := by
  have : Nontrivial M :=
    (LieSubmodule.nontrivial_iff K ↥(t.toLieSubalgebra (R := K)) M).mp inferInstance
  obtain ⟨μ0, m₀, -, P⟩ := t.exists_hasPrimitiveVectorWith (R := K) (M := M)
  obtain ⟨N, rfl⟩ := P.exists_nat
  by_cases hex : ∃ i : Fin (N + 1), (N : K) - 2 * (i : ℕ) = n
  · obtain ⟨i₀, hi₀⟩ := hex
    exact weightSpace_finrank_le_one_of_eq P i₀ hi₀
  · rw [weightSpace_eq_bot_of_ne P (not_exists.mp hex)]
    simp

/-- A vector at a weight with empty weight space two steps above is killed by `e`. -/
lemma lie_e_eq_zero_of_top_weight {n : K} {v : M} (t : IsSl2Triple h e f)
    (hv : v ∈ weightSpace (M := M) t n) (hn : weightSpace (M := M) t (n + 2) = ⊥) :
    ⁅e, v⁆ = 0 := by
  have hmem := e_mapsTo_weightSpace t n v hv
  rw [hn] at hmem
  simpa using hmem

/-- A top weight `p` of a finite-dimensional irreducible module fixes the dimension. -/
lemma finrank_of_top_weight [CharZero K] [FiniteDimensional K M]
    (t : IsSl2Triple h e f) [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M]
    {p : ℕ} (hp : weightSpace (M := M) t (p : K) ≠ ⊥)
    (hp' : weightSpace (M := M) t ((p : K) + 2) = ⊥) : Module.finrank K M = p + 1 := by
  obtain ⟨v, hvmem, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  have hlie_h : (⁅h, v⁆ : M) = (p : K) • v := by
    simpa [weightSpace, Module.End.mem_eigenspace_iff, LieModule.toEnd_apply_apply] using hvmem
  exact finrank_eq_succ
    (⟨hv0, hlie_h, lie_e_eq_zero_of_top_weight t hvmem hp'⟩ : t.HasPrimitiveVectorWith v (p : K))

/-- A nonzero weight space with no weight space two steps above it determines the
highest weight of a finite-dimensional irreducible module. -/
lemma weightSpace_highest_unique [CharZero K] [FiniteDimensional K M]
    (t : IsSl2Triple h e f) [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M]
    {m n : ℕ} (hm : weightSpace (M := M) t (m : K) ≠ ⊥)
    (hm' : weightSpace (M := M) t ((m : K) + 2) = ⊥)
    (hn : weightSpace (M := M) t (n : K) ≠ ⊥)
    (hn' : weightSpace (M := M) t ((n : K) + 2) = ⊥) : m = n := by
  have h1 := finrank_of_top_weight t hm hm'
  have h2 := finrank_of_top_weight t hn hn'
  omega

end PhyslibAlpha.Sl2
