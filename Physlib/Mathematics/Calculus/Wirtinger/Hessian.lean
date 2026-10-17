/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Physlib.Mathematics.Calculus.Wirtinger.Coordinate

/-!

# The mixed Wirtinger Hessian

The mixed Wirtinger Hessian, and its block-diagonal form for a sum of sector functions.

## i. Overview

In an `N = 1` supersymmetric theory the kinetic terms of the complex scalar fields `φ^I` are
weighted by the Kähler metric

  `g_{IJ̄}(φ) = ∂_I ∂̄_J K(φ)`,   `∂_I = ∂/∂φ^I`,   `∂̄_J = ∂/∂φ̄^J`,

of the real Kähler potential `K`. The metric is Hermitian, `(g_{JĪ})^* = g_{IJ̄}`, so the kinetic
term is real.

Suppose the fields split into sectors `k`, with fields `φ_k = (φ_k^a)` in sector `k`, and the
Kähler potential is a sum of sector potentials with no term mixing two sectors:

  `K(φ) = ∑_k K_k(φ_k)`,

as for several moduli `T_k` with `K = -∑_k n_k log(T_k + T̄_k)` and positive constants `n_k`.
Then the metric is block-diagonal and the sectors have no kinetic mixing:

  `∂²K / ∂φ_k^a ∂φ̄_l^b = δ_{kl} ∂²K_k / ∂φ_k^a ∂φ̄_k^b`.

Each `K_k` need only be `C²` at the point considered, so potentials defined on a proper
subdomain, such as `log`, are covered.

In Lean, the fields of sector `k` are labelled by a finite type `ι k`, and the field `φ_k^a`
by the pair `⟨k, a⟩ : Σ k, ι k`. A point `φ` in field space is a function
`q : (Σ k, ι k) → ℂ` with `q ⟨k, a⟩ = φ_k^a`, and the sector fields `φ_k` are
`q ∘ Sigma.mk k`, the function `a ↦ q ⟨k, a⟩`. The sector potentials `K_k` are `f k`. The
metric `g_{IJ̄}(φ)` is `hessianMatrixOfR K q`, or `hessianMatrixOf` for a complex-valued
function. At a point `u`, the block-diagonal statement reads

  `hessianMatrixOf (fun q => ∑ k, f k (q ∘ Sigma.mk k)) u`
  `  = blockDiagonal' (fun k => hessianMatrixOf (f k) (u ∘ Sigma.mk k))`.

The two-sector case over `ι₁ ⊕ ι₂` is stated with `Matrix.fromBlocks`.

## ii. Key results

- `Physlib.Wirtinger.hessianMatrixOf` : the mixed Wirtinger Hessian.
- `Physlib.Wirtinger.hessianMatrixOfR` : the same for a real-valued function.
- `Physlib.Wirtinger.hessianMatrixOfR_isHermitian` : the Hessian of a real `C²` function is
    Hermitian.
- `Physlib.Wirtinger.dWirtingerAntiCoord_block_sum` : `∂̄` of a sum of sector functions along a
    sector-`k` coordinate is the `∂̄` of the sector-`k` function; `dWirtingerCoord_block_sum` is
    the same for `∂`.
- `Physlib.Wirtinger.hessianMatrixOf_sum_eq_blockDiagonal'` : the Hessian of a sum of sector
    functions is block-diagonal.
- `Physlib.Wirtinger.hessianMatrixOf_comp_equiv` : relabelling the coordinates by `ε` reindexes
    the Hessian by `ε`.
- `Physlib.Wirtinger.hessianMatrixOf_add_eq_fromBlocks` : the two-sector case, as
    `Matrix.fromBlocks`.

## iii. Table of contents

- A. The mixed Wirtinger Hessian
- B. Block-diagonal Hessian of a sum over sectors
- C. Coordinate reindexing of the Hessian
- D. Two sectors

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.Wirtinger

open Matrix

/-! ## A. The mixed Wirtinger Hessian

For a real Kähler potential `K` the mixed Wirtinger Hessian is the Kähler metric `g_{IJ̄}`.
Reality of `K` and Schwarz's theorem make it Hermitian. -/

section Hessian

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The mixed Wirtinger Hessian of `f` at `u`: the matrix with `(I, J)` entry `∂_I ∂̄_J f`. -/
noncomputable def hessianMatrixOf (f : (ι → ℂ) → ℂ) (u : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun I J => dWirtingerCoord (fun p => dWirtingerAntiCoord f J p) I u

/-- The mixed Wirtinger Hessian of a real-valued `K`, through `Complex.ofReal`. An `abbrev`, so
lemmas about `hessianMatrixOf` apply to it. -/
noncomputable abbrev hessianMatrixOfR (K : (ι → ℂ) → ℝ) (u : ι → ℂ) : Matrix ι ι ℂ :=
  hessianMatrixOf (Complex.ofReal ∘ K) u

/-- The mixed Wirtinger Hessian of a real function `C²` at `u` is Hermitian,
`(g_{JĪ})^* = g_{IJ̄}`. -/
lemma hessianMatrixOfR_isHermitian {K : (ι → ℂ) → ℝ} {u : ι → ℂ} (hK : ContDiffAt ℝ 2 K u) :
    Matrix.IsHermitian (hessianMatrixOfR K u) := by
  set F : (ι → ℂ) → ℂ := Complex.ofReal ∘ K with hFdef
  have hF : ContDiffAt ℝ 2 F u := Complex.ofRealCLM.contDiff.contDiffAt.comp u hK
  -- `F` is real, so `star (∂̄_I F) = ∂_I F` wherever `F` is differentiable, in particular near `u`
  have hev : ∀ I : ι, (fun w => star (dWirtingerAntiCoord F I w))
      =ᶠ[nhds u] fun w => dWirtingerCoord F I w :=
    fun I => (hF.eventually (by simp)).mono fun w hw => by
      dsimp only
      rw [← dWirtingerCoord_star_comp_apply (hw.differentiableAt (by norm_num)) I]
      congr 1
      funext v
      simp [hFdef]
  ext I J
  rw [Matrix.conjTranspose_apply]
  simp only [hessianMatrixOfR, hessianMatrixOf, Matrix.of_apply]
  rw [← dWirtingerAntiCoord_star_comp_apply (differentiableAt_dWirtingerAntiCoord hF I) J,
    dWirtingerAntiCoord_congr_of_eventuallyEq_apply (hev I) J,
    ← dWirtingerCoord_dWirtingerAntiCoord_comm hF I J]

end Hessian

/-! ## B. Block-diagonal Hessian of a sum over sectors

The fields are labelled by `Σ k, ι k`, with `ι k` labelling the fields of sector `k`. A potential
that is a sum of sector potentials has a block-diagonal Hessian. -/

section SectorBlocks

variable {K : Type} [Fintype K] [DecidableEq K]
variable {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]

/-- The restriction `q ↦ q ∘ Sigma.mk k` to sector `k`, as a continuous ℝ-linear map. -/
noncomputable def restrict (k : K) : ((Σ k, ι k) → ℂ) →L[ℝ] (ι k → ℂ) :=
  ContinuousLinearMap.pi (fun a => ContinuousLinearMap.proj (R := ℝ) (⟨k, a⟩ : Σ k, ι k))

omit [Fintype K] [DecidableEq K] [(k : K) → Fintype (ι k)] [(k : K) → DecidableEq (ι k)] in
@[simp] lemma restrict_apply (k : K) (q : (Σ k, ι k) → ℂ) : restrict k q = q ∘ Sigma.mk k := rfl

omit [Fintype K] [(k : K) → Fintype (ι k)] in
/-- `restrict k` sends the basis vector of field `⟨k, a'⟩` to the basis vector of field `a'`. -/
lemma restrict_single_same (k : K) (a' : ι k) (z : ℂ) :
    restrict k (Pi.single (⟨k, a'⟩ : Σ k, ι k) z) = Pi.single a' z := by
  funext a
  rw [restrict_apply, Function.comp_apply, Pi.single_apply, Pi.single_apply]
  simp

omit [Fintype K] [(k : K) → Fintype (ι k)] in
/-- `restrict k` sends the basis vector of a field of another sector to zero. -/
lemma restrict_single_ne {k k' : K} (h : k ≠ k') (a' : ι k') (z : ℂ) :
    restrict k (Pi.single (⟨k', a'⟩ : Σ k, ι k) z) = 0 := by
  funext a
  rw [restrict_apply, Function.comp_apply, Pi.single_apply, ite_eq_right, Pi.zero_apply]
  exact fun heq => h (congrArg Sigma.fst heq)

/-- `∂_⟨k, a⟩` of a function of sector `k` alone is its `∂_a`. -/
lemma dWirtingerCoord_block_own {k : K} (g : (ι k → ℂ) → ℂ) (a : ι k)
    (u : (Σ k, ι k) → ℂ) (hg : DifferentiableAt ℝ g (u ∘ Sigma.mk k)) :
    dWirtingerCoord (fun q => g (q ∘ Sigma.mk k)) (⟨k, a⟩ : Σ k, ι k) u
      = dWirtingerCoord g a (u ∘ Sigma.mk k) :=
  dWirtingerCoord_comp_clm_col (restrict k) g ⟨k, a⟩ a u hg
    (restrict_single_same k a 1) (restrict_single_same k a Complex.I)

/-- `∂_⟨k, a⟩` of a function of another sector vanishes. -/
lemma dWirtingerCoord_block_ne {k k' : K} (h : k ≠ k') (g : (ι k' → ℂ) → ℂ) (a : ι k)
    (u : (Σ k, ι k) → ℂ) (hg : DifferentiableAt ℝ g (u ∘ Sigma.mk k')) :
    dWirtingerCoord (fun q => g (q ∘ Sigma.mk k')) (⟨k, a⟩ : Σ k, ι k) u = 0 :=
  dWirtingerCoord_comp_clm_zero (restrict k') g ⟨k, a⟩ u hg
    (restrict_single_ne h.symm a 1) (restrict_single_ne h.symm a Complex.I)

/-- Anti-holomorphic mirror of `dWirtingerCoord_block_own`. -/
lemma dWirtingerAntiCoord_block_own {k : K} (g : (ι k → ℂ) → ℂ) (a : ι k)
    (u : (Σ k, ι k) → ℂ) (hg : DifferentiableAt ℝ g (u ∘ Sigma.mk k)) :
    dWirtingerAntiCoord (fun q => g (q ∘ Sigma.mk k)) (⟨k, a⟩ : Σ k, ι k) u
      = dWirtingerAntiCoord g a (u ∘ Sigma.mk k) :=
  dWirtingerAntiCoord_comp_clm_col (restrict k) g ⟨k, a⟩ a u hg
    (restrict_single_same k a 1) (restrict_single_same k a Complex.I)

/-- Anti-holomorphic mirror of `dWirtingerCoord_block_ne`. -/
lemma dWirtingerAntiCoord_block_ne {k k' : K} (h : k ≠ k') (g : (ι k' → ℂ) → ℂ) (a : ι k)
    (u : (Σ k, ι k) → ℂ) (hg : DifferentiableAt ℝ g (u ∘ Sigma.mk k')) :
    dWirtingerAntiCoord (fun q => g (q ∘ Sigma.mk k')) (⟨k, a⟩ : Σ k, ι k) u = 0 :=
  dWirtingerAntiCoord_comp_clm_zero (restrict k') g ⟨k, a⟩ u hg
    (restrict_single_ne h.symm a 1) (restrict_single_ne h.symm a Complex.I)

/-- `∂_⟨k₀, a⟩` of a sum of sector functions is the `∂_a` of the sector-`k₀` function. -/
lemma dWirtingerCoord_block_sum (f : ∀ k, (ι k → ℂ) → ℂ) (k₀ : K) (a : ι k₀)
    (u : (Σ k, ι k) → ℂ) (hf : ∀ k, DifferentiableAt ℝ (f k) (u ∘ Sigma.mk k)) :
    dWirtingerCoord (fun q => ∑ k, f k (q ∘ Sigma.mk k)) ⟨k₀, a⟩ u
      = dWirtingerCoord (f k₀) a (u ∘ Sigma.mk k₀) := by
  rw [dWirtingerCoord_fun_sum_apply (F := fun k q => f k (q ∘ Sigma.mk k))
      (fun k _ => (hf k).comp u (restrict k).differentiableAt) ⟨k₀, a⟩,
    Finset.sum_eq_single k₀]
  · exact dWirtingerCoord_block_own (f k₀) a u (hf k₀)
  · exact fun k _ hk => dWirtingerCoord_block_ne (Ne.symm hk) (f k) a u (hf k)
  · exact absurd (Finset.mem_univ k₀)

/-- `∂̄_⟨k₀, a⟩` of a sum of sector functions is the `∂̄_a` of the sector-`k₀` function. -/
lemma dWirtingerAntiCoord_block_sum (f : ∀ k, (ι k → ℂ) → ℂ) (k₀ : K) (a : ι k₀)
    (u : (Σ k, ι k) → ℂ) (hf : ∀ k, DifferentiableAt ℝ (f k) (u ∘ Sigma.mk k)) :
    dWirtingerAntiCoord (fun q => ∑ k, f k (q ∘ Sigma.mk k)) ⟨k₀, a⟩ u
      = dWirtingerAntiCoord (f k₀) a (u ∘ Sigma.mk k₀) := by
  rw [dWirtingerAntiCoord_fun_sum_apply (F := fun k q => f k (q ∘ Sigma.mk k))
      (fun k _ => (hf k).comp u (restrict k).differentiableAt) ⟨k₀, a⟩,
    Finset.sum_eq_single k₀]
  · exact dWirtingerAntiCoord_block_own (f k₀) a u (hf k₀)
  · exact fun k _ hk => dWirtingerAntiCoord_block_ne (Ne.symm hk) (f k) a u (hf k)
  · exact absurd (Finset.mem_univ k₀)

/-- The Hessian of a sum of sector functions is the block-diagonal matrix of the sector
Hessians. -/
lemma hessianMatrixOf_sum_eq_blockDiagonal' (f : ∀ k, (ι k → ℂ) → ℂ) (u : (Σ k, ι k) → ℂ)
    (hf : ∀ k, ContDiffAt ℝ 2 (f k) (u ∘ Sigma.mk k)) :
    hessianMatrixOf (fun q => ∑ k, f k (q ∘ Sigma.mk k)) u
      = blockDiagonal' (fun k => hessianMatrixOf (f k) (u ∘ Sigma.mk k)) := by
  -- each `f k` stays `C²` near its sector point, so near `u` the inner anti-derivative of the
  -- sum routes to a single sector
  have hnear : ∀ᶠ w in nhds u, ∀ k, ContDiffAt ℝ 2 (f k) (w ∘ Sigma.mk k) :=
    Filter.eventually_all.mpr fun k =>
      ((restrict k).continuous.tendsto u).eventually ((hf k).eventually (by simp))
  have hev : ∀ (k' : K) (a' : ι k'),
      (fun w => dWirtingerAntiCoord (fun q => ∑ k, f k (q ∘ Sigma.mk k)) ⟨k', a'⟩ w)
        =ᶠ[nhds u] fun w => dWirtingerAntiCoord (f k') a' (w ∘ Sigma.mk k') :=
    fun k' a' => hnear.mono fun w hw =>
      dWirtingerAntiCoord_block_sum f k' a' w fun k => (hw k).differentiableAt (by norm_num)
  ext ⟨k, a⟩ ⟨k', a'⟩
  by_cases hkk : k = k'
  · subst hkk
    rw [blockDiagonal'_apply_eq]
    simp only [hessianMatrixOf, Matrix.of_apply]
    rw [dWirtingerCoord_congr_of_eventuallyEq_apply (hev k a') ⟨k, a⟩]
    exact dWirtingerCoord_block_own (fun w => dWirtingerAntiCoord (f k) a' w) a u
      (differentiableAt_dWirtingerAntiCoord (hf k) a')
  · rw [blockDiagonal'_apply_ne _ _ _ hkk]
    simp only [hessianMatrixOf, Matrix.of_apply]
    rw [dWirtingerCoord_congr_of_eventuallyEq_apply (hev k' a') ⟨k, a⟩]
    exact dWirtingerCoord_block_ne hkk (fun w => dWirtingerAntiCoord (f k') a' w) a u
      (differentiableAt_dWirtingerAntiCoord (hf k') a')

end SectorBlocks

/-! ## C. Coordinate reindexing of the Hessian

Relabelling the fields by a bijection `ε` permutes the rows and columns of the Hessian. -/

section Reindex

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- The relabelling `q ↦ q ∘ ε.symm` along `ε`, as a continuous ℝ-linear map. -/
noncomputable def precompEquiv (ε : ι ≃ ι') : (ι → ℂ) →L[ℝ] (ι' → ℂ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (R := ℝ) (ε.symm j))

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
@[simp] private lemma precompEquiv_apply (ε : ι ≃ ι') (q : ι → ℂ) :
    precompEquiv ε q = q ∘ ε.symm := rfl

omit [Fintype ι] [Fintype ι'] in
/-- `precompEquiv ε` sends the basis vector of field `c` to the basis vector of field `ε c`. -/
lemma precompEquiv_single (ε : ι ≃ ι') (c : ι) (z : ℂ) :
    precompEquiv ε (Pi.single c z) = Pi.single (ε c) z := by
  funext j
  simp only [precompEquiv_apply, Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]

/-- Relabelling the coordinates by `ε` reindexes the Hessian by `ε`. -/
lemma hessianMatrixOf_comp_equiv (ε : ι ≃ ι') (H : (ι' → ℂ) → ℂ) (u : ι → ℂ)
    (hH : ContDiffAt ℝ 2 H (u ∘ ε.symm)) :
    hessianMatrixOf (fun q => H (q ∘ ε.symm)) u
      = (hessianMatrixOf H (u ∘ ε.symm)).submatrix ε ε := by
  -- `H` stays `C²` near `u ∘ ε.symm`, so the inner anti-derivative routes through `ε` near `u`.
  have hnear : ∀ᶠ w in nhds u, ContDiffAt ℝ 2 H (w ∘ ε.symm) :=
    ((precompEquiv ε).continuous.tendsto u).eventually (hH.eventually (by simp))
  have hev : ∀ J : ι, (fun w => dWirtingerAntiCoord (fun q => H (q ∘ ε.symm)) J w)
      =ᶠ[nhds u] fun w => dWirtingerAntiCoord H (ε J) (w ∘ ε.symm) :=
    fun J => hnear.mono fun w hw => dWirtingerAntiCoord_comp_clm_col (precompEquiv ε) H J (ε J) w
      (hw.differentiableAt (by norm_num)) (precompEquiv_single ε J 1)
      (precompEquiv_single ε J Complex.I)
  ext I J
  rw [Matrix.submatrix_apply]
  simp only [hessianMatrixOf, Matrix.of_apply]
  rw [dWirtingerCoord_congr_of_eventuallyEq_apply (hev J) I]
  exact dWirtingerCoord_comp_clm_col (precompEquiv ε) (fun p => dWirtingerAntiCoord H (ε J) p)
    I (ε I) u (differentiableAt_dWirtingerAntiCoord hH (ε J))
    (precompEquiv_single ε I 1) (precompEquiv_single ε I Complex.I)

end Reindex

/-! ## D. Two sectors

Two sectors with fields indexed by `ι₁ ⊕ ι₂`, obtained from §B by relabelling with §C. -/

section TwoSectors

variable {ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁]
variable {ι₂ : Type} [Fintype ι₂] [DecidableEq ι₂]

/-- The restriction `q ↦ q ∘ Sum.inl` to the first sector, as a continuous ℝ-linear map. -/
noncomputable def restrictInl : (ι₁ ⊕ ι₂ → ℂ) →L[ℝ] (ι₁ → ℂ) :=
  ContinuousLinearMap.pi (fun a => ContinuousLinearMap.proj (R := ℝ) (Sum.inl a))

/-- The restriction `q ↦ q ∘ Sum.inr` to the second sector, as a continuous ℝ-linear map. -/
noncomputable def restrictInr : (ι₁ ⊕ ι₂ → ℂ) →L[ℝ] (ι₂ → ℂ) :=
  ContinuousLinearMap.pi (fun b => ContinuousLinearMap.proj (R := ℝ) (Sum.inr b))

omit [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
@[simp] lemma restrictInl_apply (q : ι₁ ⊕ ι₂ → ℂ) :
    restrictInl (ι₁ := ι₁) (ι₂ := ι₂) q = q ∘ Sum.inl := rfl

omit [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
@[simp] lemma restrictInr_apply (q : ι₁ ⊕ ι₂ → ℂ) :
    restrictInr (ι₁ := ι₁) (ι₂ := ι₂) q = q ∘ Sum.inr := rfl

/-- The Hessian of `f₁ (q ∘ Sum.inl) + f₂ (q ∘ Sum.inr)` is `fromBlocks` of the two sector
Hessians. -/
lemma hessianMatrixOf_add_eq_fromBlocks
    (f₁ : (ι₁ → ℂ) → ℂ) (f₂ : (ι₂ → ℂ) → ℂ) (u : ι₁ ⊕ ι₂ → ℂ)
    (hf₁ : ContDiffAt ℝ 2 f₁ (u ∘ Sum.inl)) (hf₂ : ContDiffAt ℝ 2 f₂ (u ∘ Sum.inr)) :
    hessianMatrixOf (fun q => f₁ (q ∘ Sum.inl) + f₂ (q ∘ Sum.inr)) u
      = Matrix.fromBlocks (hessianMatrixOf f₁ (u ∘ Sum.inl)) 0 0
          (hessianMatrixOf f₂ (u ∘ Sum.inr)) := by
  -- Relabel the two sectors as a `Bool`-indexed family `M`, `g`.
  let M : Bool → Type := fun b => bif b then ι₂ else ι₁
  let : ∀ b, Fintype (M b) := Bool.rec ‹Fintype ι₁› ‹Fintype ι₂›
  let : ∀ b, DecidableEq (M b) := Bool.rec ‹DecidableEq ι₁› ‹DecidableEq ι₂›
  let g : ∀ b, (M b → ℂ) → ℂ := Bool.rec f₁ f₂
  let ε : ι₁ ⊕ ι₂ ≃ Σ b, M b := Equiv.sumEquivSigmaBool ι₁ ι₂
  let H : ((Σ b, M b) → ℂ) → ℂ := fun p => ∑ b, g b (p ∘ Sigma.mk b)
  have hfb : ∀ b, ContDiffAt ℝ 2 (g b) ((u ∘ ε.symm) ∘ Sigma.mk b) := fun b => by
    cases b; exacts [hf₁, hf₂]
  -- `H` is `C²` at the relabelled point, each summand being a sector function after `restrict`.
  have hHC : ContDiffAt ℝ 2 H (u ∘ ε.symm) :=
    ContDiffAt.sum fun b _ =>
      (hfb b).comp (u ∘ ε.symm) (restrict (ι := M) b).contDiff.contDiffAt
  -- The combined sector function is `H` pulled back along the relabelling `ε`.
  have hfun : (fun q : ι₁ ⊕ ι₂ → ℂ => f₁ (q ∘ Sum.inl) + f₂ (q ∘ Sum.inr))
      = (fun q => H (q ∘ ε.symm)) := by
    funext q
    show f₁ (q ∘ Sum.inl) + f₂ (q ∘ Sum.inr) = ∑ b, g b ((q ∘ ε.symm) ∘ Sigma.mk b)
    rw [Fintype.sum_bool]; exact add_comm _ _
  rw [hfun, hessianMatrixOf_comp_equiv ε H u hHC,
    (hessianMatrixOf_sum_eq_blockDiagonal' g (u ∘ ε.symm) hfb :
      hessianMatrixOf H (u ∘ ε.symm) = _)]
  -- The reindexed block-diagonal is the two-block `fromBlocks` matrix.
  ext (a | a) (b | b) <;> simp [ε, Equiv.sumEquivSigmaBool, Matrix.blockDiagonal'_apply] <;> rfl

end TwoSectors

end Physlib.Wirtinger

end
