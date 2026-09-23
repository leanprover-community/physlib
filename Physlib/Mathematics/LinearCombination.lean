/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nathaneal Sajan
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Finite linear combinations under a linear map

A family `T : ι → B` of vectors of a module, indexed by a finite type, has the combinations
`∑ i, c i • T i` for coefficients `c : ι → R`. Two bookkeeping identities about them: contracting
against coefficients moved by a matrix regroups as the same combination of the matrix-moved
components, and a linear map given on the family by a matrix moves a combination by that matrix
acting on the coefficients.

Over `ℂ`, when linear maps on `B` move combinations by moving their coefficients, a combination
fixed by all the maps is the combination of fixed coefficients, provided the coefficient maps
have their adjoints among themselves: `Fintype.exists_invariant_coeff_of_adjoint_mem`.
-/

@[expose] public section

variable {ι κ R B B' : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]
  [AddCommMonoid B] [Module R B] [AddCommMonoid B'] [Module R B']

/-- Contracting the components against coefficients moved by a matrix is the original
  combination of the matrix-moved components. -/
lemma Fintype.sum_sum_mul_smul (M : ι → κ → R) (c : κ → R) (T : ι → B) :
    ∑ a, (∑ d, c d * M a d) • T a = ∑ d, c d • ∑ a, M a d • T a := by
  simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

/-- A linear map that moves each component of a family by a matrix moves a combination of the
  components by that matrix acting on the coefficients, with the free index first. -/
lemma LinearMap.map_sum_smul_of_forall_eq (φ : B →ₗ[R] B') (T : ι → B) (T' : κ → B')
    (M : κ → ι → R) (hT : ∀ l, φ (T l) = ∑ a, M a l • T' a) (c : ι → R) :
    φ (∑ l, c l • T l) = ∑ a, (∑ l, c l * M a l) • T' a := by
  rw [map_sum, Fintype.sum_sum_mul_smul]
  exact Finset.sum_congr rfl fun l _ => by rw [map_smul, hT]

open scoped InnerProductSpace in
/-- A vector of the span of `T` fixed by every `φ g` is the combination of coefficients fixed
  by every `A g`, where `φ g` moves combinations by moving their coefficients with `A g`. The
  one condition on `A` is that for every `g` some `g'` acts as the adjoint of `g` for the
  standard inner product on coefficients; neither the `φ g` nor the `A g` need form a
  representation, and `B` carries no inner product. The components may be dependent, so the
  coefficients need not be unique: the proof takes the part of any coefficients orthogonal to
  those contracting to `0`. -/
lemma Fintype.exists_invariant_coeff_of_adjoint_mem {ι G B : Type*} [Fintype ι]
    [AddCommGroup B] [Module ℂ B] (T : ι → B) (φ : G → B →ₗ[ℂ] B)
    (A : G → (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hφ : ∀ (g : G) (c : ι → ℂ), φ g (∑ i, c i • T i) = ∑ i, A g c i • T i)
    (hA : ∀ g : G, ∃ g' : G, ∀ u v : EuclideanSpace ℂ ι,
      ⟪u, WithLp.toLp 2 (A g v.ofLp)⟫_ℂ = ⟪WithLp.toLp 2 (A g' u.ofLp), v⟫_ℂ)
    {x : B} (hx : x ∈ ⨆ i, ℂ ∙ T i) (hinv : ∀ g, φ g x = x) :
    ∃ c : ι → ℂ, x = ∑ i, c i • T i ∧ ∀ g, A g c = c := by
  classical
  obtain ⟨c, rfl⟩ : ∃ c : ι → ℂ, x = ∑ i, c i • T i := by
    rw [← Submodule.span_range_eq_iSup, ← Fintype.range_linearCombination,
      LinearMap.mem_range] at hx
    simpa only [Fintype.linearCombination_apply, eq_comm] using hx
  -- `K`: the coefficients contracting to `0`, stable under every `A g`.
  set q := Fintype.linearCombination ℂ T ∘ₗ (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap
  have hq : ∀ u, q u = ∑ i, u.ofLp i • T i := fun u => Fintype.linearCombination_apply ℂ T _
  set K := LinearMap.ker q
  have hKstab : ∀ g, ∀ u ∈ K, WithLp.toLp 2 (A g u.ofLp) ∈ K := fun g u hu => by
    rw [LinearMap.mem_ker, hq] at hu ⊢
    rw [← hφ, hu, map_zero]
  -- Replace `c` by its part `k'` in `Kᗮ`, which contracts to the same vector.
  obtain ⟨k, hk, k', hk', hkk'⟩ := K.exists_add_mem_mem_orthogonal (WithLp.toLp 2 c)
  have hx' : ∑ i, c i • T i = q k' := by
    rw [← zero_add (q k'), ← LinearMap.mem_ker.1 hk, ← map_add, ← hkk', hq]
  refine ⟨k'.ofLp, hx'.trans (hq k'), fun g => ?_⟩
  -- The change of `k'` under `A g` lies in `K` by invariance of the vector, and in `Kᗮ` since
  -- the adjoint of `A g` preserves `K`.
  have h1 : WithLp.toLp 2 (A g k'.ofLp) - k' ∈ K := by
    rw [LinearMap.mem_ker, map_sub, hq, ← hφ, ← hq, ← hx', hinv, sub_self]
  have h2 : WithLp.toLp 2 (A g k'.ofLp) ∈ Kᗮ := by
    obtain ⟨g', hg'⟩ := hA g
    refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
    rw [hg' u k']
    exact Submodule.inner_right_of_mem_orthogonal (hKstab g' u hu) hk'
  have h3 : WithLp.toLp 2 (A g k'.ofLp) - k' ∈ K ⊓ Kᗮ := ⟨h1, Submodule.sub_mem _ h2 hk'⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at h3
  exact congrArg WithLp.ofLp h3
