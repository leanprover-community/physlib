/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Calculus.Wirtinger.Coordinate

/-!

# The mixed Wirtinger Hessian

The mixed Wirtinger Hessian, and its block-diagonal form for a sum of sector functions.

## i. Overview

The mixed Wirtinger Hessian `hessianMatrixOf f u` of `f : (ι → ℂ) → ℂ` is the matrix with
`(I, J)` entry `∂_I ∂̄_J f` at `u`. For a real Kähler potential `K` it is the Kähler metric
`g_{IJ̄}`.

If `F` is a sum of sector functions, `F q = ∑ k, f k (q ∘ Sigma.mk k)` with each `f k` reading
only the coordinates of sector `k`, the Hessian is block-diagonal:

  `hessianMatrixOf F u = blockDiagonal' (fun k => hessianMatrixOf (f k) (u ∘ Sigma.mk k))`

Each `f k` need only be `C²` on an open set containing `u ∘ Sigma.mk k`, so functions defined on
a proper subdomain, such as `log`, are covered. The two-sector case over `ι₁ ⊕ ι₂` is stated with
`Matrix.fromBlocks`.

## ii. Key results

- `Physlib.Wirtinger.hessianMatrixOf` : the mixed Wirtinger Hessian.
- `Physlib.Wirtinger.hessianMatrixOfR` : the same for a real-valued function.
- `Physlib.Wirtinger.hessianMatrixOf_sigma_block` : the Hessian of a sum of sector functions is
    block-diagonal.
- `Physlib.Wirtinger.hessianMatrixOf_comp_equiv` : relabelling the coordinates by `ε` reindexes
    the Hessian by `ε`.
- `Physlib.Wirtinger.hessianMatrixOf_sum_block` : the two-sector case, as `Matrix.fromBlocks`.

## iii. Table of contents

- A. The mixed Wirtinger Hessian
- B. Sector split over a finite family of blocks
- C. Coordinate reindexing of the Hessian
- D. Two-sector special case

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace Physlib.Wirtinger

open Matrix

/-! ## A. The mixed Wirtinger Hessian -/

section Hessian

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The mixed Wirtinger Hessian of `f` at `u`: the matrix with `(I, J)` entry `∂_I ∂̄_J f`. -/
noncomputable def hessianMatrixOf (f : (ι → ℂ) → ℂ) (u : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun I J => dWirtingerCoord (fun p => dWirtingerAntiCoord f J p) I u

/-- The mixed Wirtinger Hessian of a real-valued `K`, through `Complex.ofReal`. An `abbrev`, so
lemmas about `hessianMatrixOf` apply to it. -/
noncomputable abbrev hessianMatrixOfR (K : (ι → ℂ) → ℝ) (u : ι → ℂ) : Matrix ι ι ℂ :=
  hessianMatrixOf (Complex.ofReal ∘ K) u

end Hessian

/-! ## B. Sector split over a finite family of blocks -/

section Sigma

variable {K : Type} [Fintype K] [DecidableEq K]
variable {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]

/-- The restriction `q ↦ q ∘ Sigma.mk k` to sector `k`, as a continuous ℝ-linear map. -/
noncomputable def restrict (k : K) : ((Σ k, ι k) → ℂ) →L[ℝ] (ι k → ℂ) :=
  ContinuousLinearMap.pi (fun a => ContinuousLinearMap.proj (R := ℝ) (⟨k, a⟩ : Σ k, ι k))

omit [Fintype K] [DecidableEq K] [(k : K) → Fintype (ι k)] [(k : K) → DecidableEq (ι k)] in
@[simp] lemma restrict_apply (k : K) (q : (Σ k, ι k) → ℂ) : restrict k q = q ∘ Sigma.mk k := rfl

omit [Fintype K] [(k : K) → Fintype (ι k)] in
/-- Restricting to sector `k` keeps a column of sector `k`. -/
lemma restrict_single_same (k : K) (a' : ι k) (z : ℂ) :
    restrict k (Pi.single (⟨k, a'⟩ : Σ k, ι k) z) = Pi.single a' z := by
  funext a
  rw [restrict_apply, Function.comp_apply, Pi.single_apply, Pi.single_apply]
  simp

omit [Fintype K] [(k : K) → Fintype (ι k)] in
/-- Restricting to sector `k` kills a column of another sector. -/
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

/-- The Hessian of a sum of sector functions is the block-diagonal of the sector Hessians. Each
`f k` need only be `C²` on an open set `s k` containing `u ∘ Sigma.mk k`. -/
lemma hessianMatrixOf_sigma_block
    (f : ∀ k, (ι k → ℂ) → ℂ) (s : ∀ k, Set (ι k → ℂ)) (hs : ∀ k, IsOpen (s k))
    (hf : ∀ k, ∀ v ∈ s k, ContDiffAt ℝ 2 (f k) v)
    (u : (Σ k, ι k) → ℂ) (hu : ∀ k, (u ∘ Sigma.mk k) ∈ s k) :
    hessianMatrixOf (fun q => ∑ k, f k (q ∘ Sigma.mk k)) u
      = blockDiagonal' (fun k => hessianMatrixOf (f k) (u ∘ Sigma.mk k)) := by
  set F : ((Σ k, ι k) → ℂ) → ℂ := fun q => ∑ k, f k (q ∘ Sigma.mk k) with hF
  set S : Set ((Σ k, ι k) → ℂ) := ⋂ k, (restrict k) ⁻¹' (s k) with hS
  have hScol : ∀ k, ∀ w ∈ S, (w ∘ Sigma.mk k) ∈ s k := fun k w hw => by
    have := Set.mem_iInter.mp hw k; rwa [Set.mem_preimage, restrict_apply] at this
  have hSopen : IsOpen S := isOpen_iInter_of_finite fun k => (hs k).preimage (restrict k).continuous
  have huS : u ∈ S := Set.mem_iInter.mpr fun k => by
    rw [Set.mem_preimage, restrict_apply]; exact hu k
  have hSnhds : S ∈ nhds u := hSopen.mem_nhds huS
  -- differentiability of each sector lift on `S`
  have hd : ∀ k, ∀ w ∈ S, DifferentiableAt ℝ (fun q => f k (q ∘ Sigma.mk k)) w := fun k w hw =>
    ((hf k (w ∘ Sigma.mk k) (hScol k w hw)).differentiableAt (by norm_num)).comp w
      (restrict k).differentiableAt
  -- the inner anti-derivative of the sum routes to a single sector on `S`
  have hev : ∀ (k₀ : K) (a' : ι k₀) (w : (Σ k, ι k) → ℂ), w ∈ S →
      dWirtingerAntiCoord F ⟨k₀, a'⟩ w = dWirtingerAntiCoord (f k₀) a' (w ∘ Sigma.mk k₀) := by
    intro k₀ a' w hw
    show dWirtingerAntiCoord (fun v => ∑ k, (fun q => f k (q ∘ Sigma.mk k)) v) ⟨k₀, a'⟩ w = _
    rw [dWirtingerAntiCoord_fun_sum_apply (fun k _ => hd k w hw) ⟨k₀, a'⟩,
      Finset.sum_eq_single k₀]
    · exact dWirtingerAntiCoord_block_own (f k₀) a' w
        ((hf k₀ _ (hScol k₀ w hw)).differentiableAt (by norm_num))
    · exact fun k _ hk => dWirtingerAntiCoord_block_ne (Ne.symm hk) (f k) a' w
        ((hf k _ (hScol k w hw)).differentiableAt (by norm_num))
    · exact absurd (Finset.mem_univ k₀)
  ext ⟨k, a⟩ ⟨k', a'⟩
  by_cases hkk : k = k'
  · subst hkk
    rw [blockDiagonal'_apply_eq]
    simp only [hessianMatrixOf, Matrix.of_apply]
    rw [dWirtingerCoord_congr_of_eventuallyEq_apply
        (Filter.eventually_of_mem hSnhds fun w hw => hev k a' w hw) ⟨k, a⟩]
    exact dWirtingerCoord_block_own (fun w => dWirtingerAntiCoord (f k) a' w) a u
      (differentiableAt_dWirtingerAntiCoord (hf k _ (hu k)) a')
  · rw [blockDiagonal'_apply_ne _ _ _ hkk]
    simp only [hessianMatrixOf, Matrix.of_apply]
    rw [dWirtingerCoord_congr_of_eventuallyEq_apply
        (Filter.eventually_of_mem hSnhds fun w hw => hev k' a' w hw) ⟨k, a⟩]
    exact dWirtingerCoord_block_ne hkk (fun w => dWirtingerAntiCoord (f k') a' w) a u
      (differentiableAt_dWirtingerAntiCoord (hf k' _ (hu k')) a')

end Sigma

/-! ## C. Coordinate reindexing of the Hessian -/

section Reindex

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- The relabelling `q ↦ q ∘ ε.symm` along `ε`, as a continuous ℝ-linear map. -/
noncomputable def precompEquiv (ε : ι ≃ ι') : (ι → ℂ) →L[ℝ] (ι' → ℂ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (R := ℝ) (ε.symm j))

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
@[simp] private lemma precompEquiv_apply (ε : ι ≃ ι') (q : ι → ℂ) :
    precompEquiv ε q = q ∘ ε.symm := rfl

omit [Fintype ι] [Fintype ι'] in
/-- Relabelling along `ε` carries the column `c` to the column `ε c`. -/
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

/-! ## D. Two-sector special case -/

section Sum

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
Hessians. `f₁` and `f₂` need only be `C²` on open sets containing `u ∘ Sum.inl` and
`u ∘ Sum.inr`. -/
lemma hessianMatrixOf_sum_block
    (f₁ : (ι₁ → ℂ) → ℂ) (f₂ : (ι₂ → ℂ) → ℂ)
    (s₁ : Set (ι₁ → ℂ)) (s₂ : Set (ι₂ → ℂ))
    (hs₁ : IsOpen s₁) (hs₂ : IsOpen s₂)
    (hf₁ : ∀ v ∈ s₁, ContDiffAt ℝ 2 f₁ v) (hf₂ : ∀ v ∈ s₂, ContDiffAt ℝ 2 f₂ v)
    (u : ι₁ ⊕ ι₂ → ℂ) (hu₁ : (u ∘ Sum.inl) ∈ s₁) (hu₂ : (u ∘ Sum.inr) ∈ s₂) :
    hessianMatrixOf (fun q => f₁ (q ∘ Sum.inl) + f₂ (q ∘ Sum.inr)) u
      = Matrix.fromBlocks (hessianMatrixOf f₁ (u ∘ Sum.inl)) 0 0
          (hessianMatrixOf f₂ (u ∘ Sum.inr)) := by
  -- Relabel the two sectors as a `Bool`-indexed family `M`, `g`, `sb`.
  let M : Bool → Type := fun b => bif b then ι₂ else ι₁
  let : ∀ b, Fintype (M b) := Bool.rec ‹Fintype ι₁› ‹Fintype ι₂›
  let : ∀ b, DecidableEq (M b) := Bool.rec ‹DecidableEq ι₁› ‹DecidableEq ι₂›
  let g : ∀ b, (M b → ℂ) → ℂ := Bool.rec f₁ f₂
  let sb : ∀ b, Set (M b → ℂ) := Bool.rec s₁ s₂
  let ε : ι₁ ⊕ ι₂ ≃ Σ b, M b := Equiv.sumEquivSigmaBool ι₁ ι₂
  let H : ((Σ b, M b) → ℂ) → ℂ := fun p => ∑ b, g b (p ∘ Sigma.mk b)
  have hsb : ∀ b, IsOpen (sb b) := fun b => by cases b; exacts [hs₁, hs₂]
  have hfb : ∀ b, ∀ v ∈ sb b, ContDiffAt ℝ 2 (g b) v := fun b => by cases b; exacts [hf₁, hf₂]
  have hu_sig : ∀ b, ((u ∘ ε.symm) ∘ Sigma.mk b) ∈ sb b := fun b => by cases b; exacts [hu₁, hu₂]
  -- `H` is `C²` at the relabelled point, each summand being a sector function after `restrict`.
  have hHC : ContDiffAt ℝ 2 H (u ∘ ε.symm) :=
    ContDiffAt.sum fun b _ =>
      (hfb b _ (hu_sig b)).comp (u ∘ ε.symm) (restrict (ι := M) b).contDiff.contDiffAt
  -- The combined sector function is `H` pulled back along the relabelling `ε`.
  have hfun : (fun q : ι₁ ⊕ ι₂ → ℂ => f₁ (q ∘ Sum.inl) + f₂ (q ∘ Sum.inr))
      = (fun q => H (q ∘ ε.symm)) := by
    funext q
    show f₁ (q ∘ Sum.inl) + f₂ (q ∘ Sum.inr) = ∑ b, g b ((q ∘ ε.symm) ∘ Sigma.mk b)
    rw [Fintype.sum_bool]; exact add_comm _ _
  rw [hfun, hessianMatrixOf_comp_equiv ε H u hHC,
    (hessianMatrixOf_sigma_block g sb hsb hfb (u ∘ ε.symm) hu_sig :
      hessianMatrixOf H (u ∘ ε.symm) = _)]
  -- The reindexed block-diagonal is the two-block `fromBlocks` matrix.
  ext (a | a) (b | b) <;> simp [ε, Equiv.sumEquivSigmaBool, Matrix.blockDiagonal'_apply] <;> rfl

end Sum

end Physlib.Wirtinger

end
