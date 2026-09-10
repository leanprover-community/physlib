/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
/-!
# Families of components and their invariants

Every file of this folder studies a family `T : ι → B` of vectors in a module `B`: the
components of a tensor with a fixed set of gauge indices, such as a product of two gluon
field strengths `F^a F^b` indexed by `ι = Fin 2 → Fin 8`. A gauge transformation moves the
components into one another by a fixed matrix, and the question is always the same: which
linear combinations of the components does every transformation leave alone? The answer,
file by file, is a specific contraction, the trace `∑ a, T ![a, a]` or an epsilon symbol,
and this file holds the three steps of the argument that do not depend on the family.

The first is bookkeeping: a vector lies in the span of the components precisely when it is a
linear combination `∑ i, c i • T i`, so the span is described by coefficient functions
`c : ι → ℂ`, on which the transformations act by the matrix of the law.

The second is the heart of the matter. An invariant vector of the span need not have an
invariant coefficient function, because the components may be linearly dependent. But the
coefficients contracting to zero form a subspace stable under the action, and when the action
preserves the standard inner product, so does its orthogonal complement. Projecting the
coefficient of an invariant vector onto that complement leaves the vector alone and makes
the coefficient invariant. So an invariant of the span is the contraction of an invariant
coefficient, and classifying invariants of the span reduces to classifying invariant
coefficient functions, a finite linear-algebra problem: `Family.exists_invariant_coeff`.

The third is peeling. The Standard Model files handle many families at once and remove them
one at a time modulo a stable submodule `S` in which the other families are parked. A
classification of the invariants of a family, valid in every module, applies in the quotient
`B ⧸ S`, and `Family.exists_smul_add_of_mem_sup` lifts it back: an invariant of the span
joined with `S` is a multiple of the contraction up to an invariant remainder in `S`.
-/

@[expose] public section

namespace StandardModel

namespace Family

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ι : Type*} [Fintype ι]

/-!

## A. The span of a family

-/

/-- A vector lies in the span of the components precisely when it is a linear combination
  of them. -/
lemma mem_iSup_span_singleton_iff (T : ι → B) (x : B) :
    x ∈ (⨆ i, ℂ ∙ T i) ↔ ∃ c : ι → ℂ, x = ∑ i, c i • T i := by
  rw [← Submodule.span_range_eq_iSup, ← Fintype.range_linearCombination, LinearMap.mem_range]
  simp only [Fintype.linearCombination_apply, eq_comm]

omit [Fintype ι] in
/-- Every component lies in the span. -/
lemma mem_iSup_span_singleton (T : ι → B) (i : ι) : T i ∈ ⨆ i, ℂ ∙ T i :=
  Submodule.mem_iSup_of_mem i (Submodule.mem_span_singleton_self _)

/-- A sum over pairs of indices is a double sum. -/
lemma sum_pi_two {n : ℕ} {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin n) → M) :
    ∑ d : Fin 2 → Fin n, F d = ∑ x : Fin n, ∑ y : Fin n, F ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin n, F d) = ∑ p : Fin n × Fin n, F ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin n) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-!

## B. An invariant of the span is the contraction of an invariant coefficient

The transformations are a family of linear maps `φ g` on `B`, indexed by a group `G`, and
the law says that `φ g` moves a contraction `∑ i, c i • T i` to the contraction against
`A g c`, for a linear action `A g` on coefficient functions. One property of `A` is needed:
`A g⁻¹` is the adjoint of `A g` for the standard inner product on coefficients, which is to
say that `A` is unitary. For an action by real matrices this follows from `A g⁻¹` being the
transpose of `A g` and `A g` commuting with conjugation, `sum_star_mul_of_transpose`.

-/

section Complement

variable {G : Type*} [Group G] (T : ι → B) (φ : G → B →ₗ[ℂ] B)
  (A : G → (ι → ℂ) →ₗ[ℂ] (ι → ℂ))

/-- The contraction, as a linear map on the coefficient space with its standard inner
  product. -/
noncomputable def contractₗ : EuclideanSpace ℂ ι →ₗ[ℂ] B where
  toFun c := ∑ i, c.ofLp i • T i
  map_add' c c' := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
      smul_smul]

/-- The action on coefficients, on the coefficient space with its standard inner
  product. -/
noncomputable def actₗ (g : G) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun c := WithLp.toLp 2 (A g c.ofLp)
  map_add' c c' := by simp only [WithLp.ofLp_add, map_add, WithLp.toLp_add]
  map_smul' z c := by
    simp only [WithLp.ofLp_smul, map_smul, RingHom.id_apply, WithLp.toLp_smul]

/-- For an action by real matrices, `A g⁻¹` being the transpose of `A g` and `A g`
  commuting with conjugation make `A g⁻¹` the adjoint of `A g`. -/
lemma sum_star_mul_of_transpose
    (hA : ∀ g (c d : ι → ℂ), ∑ i, A g c i * d i = ∑ i, c i * A g⁻¹ d i)
    (hstar : ∀ g (c : ι → ℂ), A g (star c) = star (A g c)) (g : G) (c d : ι → ℂ) :
    ∑ i, star (c i) * A g d i = ∑ i, star (A g⁻¹ c i) * d i := by
  have h := hA g d (star c)
  rw [hstar] at h
  simp only [Pi.star_apply] at h
  calc ∑ i, star (c i) * A g d i = ∑ i, A g d i * star (c i) := by simp_rw [mul_comm]
    _ = ∑ i, d i * star (A g⁻¹ c i) := h
    _ = ∑ i, star (A g⁻¹ c i) * d i := by simp_rw [mul_comm]

open scoped InnerProductSpace in
/-- The adjoint property, read on the coefficient space with its standard inner product. -/
lemma inner_actₗ
    (hA : ∀ g (c d : ι → ℂ), ∑ i, star (c i) * A g d i = ∑ i, star (A g⁻¹ c i) * d i)
    (g : G) (a b : EuclideanSpace ℂ ι) :
    ⟪a, actₗ A g b⟫_ℂ = ⟪actₗ A g⁻¹ a, b⟫_ℂ := by
  have h := hA g a.ofLp b.ofLp
  simp only [PiLp.inner_apply, RCLike.inner_apply, actₗ, LinearMap.coe_mk, AddHom.coe_mk,
    Complex.star_def] at h ⊢
  rw [Finset.sum_congr rfl fun i _ => mul_comm (A g b.ofLp i) _, h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- An invariant of the span of a family is the contraction of an invariant coefficient
  function, provided the transformations act on coefficients by a unitary action. -/
theorem exists_invariant_coeff
    (hφ : ∀ g (c : ι → ℂ), φ g (∑ i, c i • T i) = ∑ i, A g c i • T i)
    (hA : ∀ g (c d : ι → ℂ), ∑ i, star (c i) * A g d i = ∑ i, star (A g⁻¹ c i) * d i)
    {x : B} (hx : x ∈ ⨆ i, ℂ ∙ T i) (hinv : ∀ g, φ g x = x) :
    ∃ c : ι → ℂ, x = ∑ i, c i • T i ∧ ∀ g, A g c = c := by
  obtain ⟨c, rfl⟩ := (mem_iSup_span_singleton_iff T x).1 hx
  have hΦ : ∀ (g : G) (u : EuclideanSpace ℂ ι),
      contractₗ T (actₗ A g u) = φ g (contractₗ T u) := fun g u => (hφ g u.ofLp).symm
  set K := LinearMap.ker (contractₗ T) with hK
  have hKstab : ∀ g, ∀ u ∈ K, actₗ A g u ∈ K := by
    intro g u hu
    rw [hK, LinearMap.mem_ker] at hu ⊢
    rw [hΦ, hu, map_zero]
  obtain ⟨k, hk, k', hk', hkk'⟩ := K.exists_add_mem_mem_orthogonal (WithLp.toLp 2 c)
  have hx' : ∑ i, c i • T i = contractₗ T k' := by
    have h := congrArg (contractₗ T) hkk'
    rw [map_add, LinearMap.mem_ker.1 hk, zero_add] at h
    exact h
  refine ⟨k'.ofLp, hx', fun g => ?_⟩
  have h1 : actₗ A g k' - k' ∈ K := by
    rw [hK, LinearMap.mem_ker, map_sub, sub_eq_zero, hΦ, ← hx', hinv]
  have h2 : actₗ A g k' ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [inner_actₗ A hA]
    exact Submodule.inner_right_of_mem_orthogonal (hKstab _ u hu) hk'
  have h3 : actₗ A g k' - k' ∈ K ⊓ Kᗮ := ⟨h1, Submodule.sub_mem _ h2 hk'⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at h3
  exact congrArg WithLp.ofLp h3

end Complement

/-!

## C. Peeling a family off a stable submodule

A submodule `S` stable under the transformations carries the induced maps
`S.mapQ S (φ g) _` on the quotient, and the classes of the components form a family in the
quotient. When the invariants of that family are known to be the classes of a submodule `W`
of invariant vectors, typically the multiples of one contraction `v`, an invariant of the
span joined with `S` lies in `W` up to a remainder in `S`, and the remainder is invariant for
free, being the difference of two invariants. Stability of `S` cannot be dropped: an unstable
line has no invariant but `0`, while its sum with the span may well carry invariants outside
the span.

-/

/-- Peeling one family off a stable submodule, when its invariants in the quotient are
  known to be the classes of a submodule `W` of invariant vectors. -/
theorem exists_mem_add_of_mem_sup {G : Type*} (T : ι → B) (φ : G → B →ₗ[ℂ] B)
    (S : Submodule ℂ B) (hS : ∀ g, ∀ y ∈ S, φ g y ∈ S) (W : Submodule ℂ B)
    (hW : ∀ w ∈ W, ∀ g, φ g w = w)
    (hclass : ∀ x : B ⧸ S, x ∈ (⨆ i, ℂ ∙ S.mkQ (T i)) →
      (∀ g, S.mapQ S (φ g) (hS g) x = x) → x ∈ W.map S.mkQ)
    {x : B} (hx : x ∈ (⨆ i, ℂ ∙ T i) ⊔ S) (hinv : ∀ g, φ g x = x) :
    ∃ w ∈ W, ∃ y ∈ S, x = w + y ∧ ∀ g, φ g y = y := by
  have hmk : S.mkQ x ∈ ⨆ i, ℂ ∙ S.mkQ (T i) := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (mem_iSup_span_singleton_iff T u).1 hu
    refine (mem_iSup_span_singleton_iff _ _).2 ⟨c, ?_⟩
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  obtain ⟨w, hw, hwx⟩ := hclass _ hmk fun g => by
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, hinv]
  refine ⟨w, hw, x - w, ?_, by abel, fun g => ?_⟩
  · have hker : x - w ∈ LinearMap.ker S.mkQ := by
      rw [LinearMap.mem_ker, map_sub, hwx, sub_self]
    rwa [Submodule.ker_mkQ] at hker
  · rw [map_sub, hinv g, hW w hw g]

/-- Peeling one family off a stable submodule, when its invariants in the quotient are
  known to be the multiples of the class of an invariant vector `v`. -/
theorem exists_smul_add_of_mem_sup {G : Type*} (T : ι → B) (φ : G → B →ₗ[ℂ] B)
    (S : Submodule ℂ B) (hS : ∀ g, ∀ y ∈ S, φ g y ∈ S) (v : B) (hv : ∀ g, φ g v = v)
    (hclass : ∀ x : B ⧸ S, x ∈ (⨆ i, ℂ ∙ S.mkQ (T i)) →
      (∀ g, S.mapQ S (φ g) (hS g) x = x) → ∃ c : ℂ, x = c • S.mkQ v)
    {x : B} (hx : x ∈ (⨆ i, ℂ ∙ T i) ⊔ S) (hinv : ∀ g, φ g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • v + y ∧ ∀ g, φ g y = y := by
  obtain ⟨w, hw, y, hyS, hxy, hyinv⟩ := exists_mem_add_of_mem_sup T φ S hS (ℂ ∙ v)
    (fun w hw g => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul, hv])
    (fun x hx hinv => by
      obtain ⟨c, hc⟩ := hclass x hx hinv
      exact ⟨c • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
        by rw [map_smul, hc]⟩) hx hinv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  exact ⟨c, y, hyS, hxy, hyinv⟩

end Family

end StandardModel
