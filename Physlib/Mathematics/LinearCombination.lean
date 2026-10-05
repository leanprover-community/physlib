/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nathaneal Sajan
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Finite linear combinations under a linear map

A family `T : ι → B` of vectors of an `R`-module spans Mathlib's
`Submodule.span R (Set.range T)`. The index type is arbitrary and may be empty. When it is
finite, the elements of the span are exactly the combinations `∑ i, c i • T i`, for
coefficients `c : ι → R` that need not be unique (`Submodule.mem_span_range_iff_exists_fun`).
The one fact added here is that a linear map carries this span to the span of the images of
the family (`Submodule.map_span_range`).

Two bookkeeping identities about these combinations: contracting
against coefficients moved by a matrix regroups as the same combination of the matrix-moved
components, and a linear map given on the family by a matrix moves a combination by that matrix
acting on the coefficients.

Over `ℂ`, when linear maps on `B` move combinations by moving their coefficients, a combination
fixed by all the maps is the combination of fixed coefficients, provided the coefficient maps
have their adjoints among themselves: `Fintype.exists_invariant_coeff_of_adjoint_mem`. When the
coefficient maps are matrices, the condition is that the conjugate transpose of each matrix is
again one of them: `Fintype.exists_mulVec_eq_of_conjTranspose_mem`.

Spans are bounded through their members: the range of a linear map is the span of the images
of a basis, and a product of submodules lying in spans of families lies in any submodule
containing the products of their members.

- A. The image of the span of a family
- B. Combinations moved by linear maps
- C. Fixed vectors of the span
- D. Spans bounded through their members
-/

@[expose] public section

/-!

## A. The image of the span of a family

-/

/-- The image of the span of a family is the span of the images. -/
lemma Submodule.map_span_range {R B B' : Type*} [Semiring R] [AddCommMonoid B] [Module R B]
    [AddCommMonoid B'] [Module R B'] {ι : Sort*} (f : B →ₗ[R] B') (T : ι → B) :
    (Submodule.span R (Set.range T)).map f = Submodule.span R (Set.range fun i => f (T i)) := by
  rw [Submodule.map_span, Set.range_comp']

/-!

## B. Combinations moved by linear maps

-/

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

open Matrix in
/-- The matrix form of `LinearMap.map_sum_smul_of_forall_eq`: a linear map moving `T l` to
  `∑ a, M a l • T' a` moves the combination with coefficients `c` to the combination with
  coefficients `M *ᵥ c`. -/
lemma LinearMap.map_sum_smul_eq_sum_mulVec_smul (φ : B →ₗ[R] B') (T : ι → B) (T' : κ → B')
    (M : Matrix κ ι R) (hT : ∀ l, φ (T l) = ∑ a, M a l • T' a) (c : ι → R) :
    φ (∑ l, c l • T l) = ∑ a, (M *ᵥ c) a • T' a := by
  rw [φ.map_sum_smul_of_forall_eq T T' M hT c]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [mulVec, dotProduct, mul_comm]

/-!

## C. Fixed vectors of the span

-/

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
    {x : B} (hx : x ∈ Submodule.span ℂ (Set.range T)) (hinv : ∀ g, φ g x = x) :
    ∃ c : ι → ℂ, x = ∑ i, c i • T i ∧ ∀ g, A g c = c := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
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

open Matrix in
/-- The matrix form of `Fintype.exists_invariant_coeff_of_adjoint_mem`: when each `φ g` moves
  the family by a matrix `M g`, and the conjugate transpose of each `M g` is some `M g'`, a
  vector of the span fixed by every `φ g` is the combination of a coefficient vector fixed by
  every `M g`. -/
lemma Fintype.exists_mulVec_eq_of_conjTranspose_mem {ι G B : Type*} [Fintype ι]
    [AddCommGroup B] [Module ℂ B] (T : ι → B) (φ : G → B →ₗ[ℂ] B) (M : G → Matrix ι ι ℂ)
    (hT : ∀ g l, φ g (T l) = ∑ a, M g a l • T a) (hM : ∀ g, ∃ g', M g' = (M g)ᴴ)
    {x : B} (hx : x ∈ Submodule.span ℂ (Set.range T)) (hinv : ∀ g, φ g x = x) :
    ∃ c : ι → ℂ, x = ∑ i, c i • T i ∧ ∀ g, M g *ᵥ c = c :=
  Fintype.exists_invariant_coeff_of_adjoint_mem T φ (fun g => (M g).mulVecLin)
    (fun g c => (φ g).map_sum_smul_eq_sum_mulVec_smul T T (M g) (hT g) c)
    (fun g => by
      obtain ⟨g', hg'⟩ := hM g
      refine ⟨g', fun u v => ?_⟩
      -- `⟪u, M v⟫ = ⟪Mᴴ u, v⟫`, written with dot products
      simp only [mulVecLin_apply, EuclideanSpace.inner_eq_star_dotProduct, hg', star_mulVec,
        conjTranspose_conjTranspose]
      rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm]) hx hinv

/-!

## D. Spans bounded through their members

-/

/-- The range of a linear map is the span of the images of a basis. -/
lemma LinearMap.range_eq_span_range_basis {ι R M N : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (b : Module.Basis ι R M) (f : M →ₗ[R] N) :
    LinearMap.range f = Submodule.span R (Set.range fun i => f (b i)) := by
  rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span_range]

/-- A product of two submodules, each inside the span of a family, lies in any submodule
  containing the products of the members of the two families. -/
lemma Submodule.mul_le_of_le_span_range {ι κ R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] {V V' X : Submodule R A} {a : ι → A} {b : κ → A}
    (hV : V ≤ Submodule.span R (Set.range a)) (hV' : V' ≤ Submodule.span R (Set.range b))
    (hX : ∀ i j, a i * b j ∈ X) : V * V' ≤ X := by
  refine (mul_le_mul' hV hV').trans ?_
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  exact hX i j

/-- The three-factor form of `Submodule.mul_le_of_le_span_range`. -/
lemma Submodule.mul_mul_le_of_le_span_range {ι κ ν R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] {V V' V'' X : Submodule R A} {a : ι → A} {b : κ → A} {c : ν → A}
    (hV : V ≤ Submodule.span R (Set.range a)) (hV' : V' ≤ Submodule.span R (Set.range b))
    (hV'' : V'' ≤ Submodule.span R (Set.range c)) (hX : ∀ i j k, a i * (b j * c k) ∈ X) :
    V * (V' * V'') ≤ X :=
  mul_le_of_le_span_range hV
    (mul_le_of_le_span_range (X := Submodule.span R (Set.range fun p : κ × ν => b p.1 * c p.2))
      hV' hV'' fun j k => Submodule.subset_span ⟨(j, k), rfl⟩)
    fun i p => hX i p.1 p.2
