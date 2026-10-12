/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.ElementalUncertainty
public import PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.ProductState
/-!

# The open tight binding cube

## i. Overview

Three open tight binding chains `Tx`, `Ty`, `Tz` along the axes of a cube give the sites
`(nx, ny, nz)` and the Hilbert space `𝓗[Fin Nx × Fin Ny × Fin Nz]`. Each observable of a chain
acts on its own axis and leaves the other two in place. Observables of different axes commute:
only the Hamiltonian and the position of the same axis fail to commute.

In the maximal current state of the cube, the product of the maximal current states of the three
chains, each axis carries the constant `C_Nava` of its own chain. The energy–position uncertainty
relation of an axis is an equality exactly when that axis has `2` or `3` sites, and it is strict
from `4` sites on, on the three axes at once.

The six observables `(H, X)` of the three axes satisfy Robertson's relation `|det Ω| ≤ det Σ` in
every state of the cube. Since different axes commute, `Ω` is block diagonal and `|det Ω|` is the
product of the squared brackets of the three axes. In the maximal current state `Σ` is block
diagonal too, and `det Σ / |det Ω|` is the product of the squares of the three constants
`C_Nava`, so the relation is strict from `4 × 4 × 4` on.

## ii. Key results

- `alongX`, `alongY`, `alongZ` : an observable of a chain acting on its axis of the cube.
- `bracket_alongX_alongY`, `bracket_alongX_alongZ`, `bracket_alongY_alongZ` : different axes
  commute.
- `maxCurrentCubeState` : the maximal current state of the cube.
- `CNava_alongX`, `CNava_alongY`, `CNava_alongZ` : each axis carries its own `C_Nava`.
- `centeredGramDefect_alongX_eq_zero_iff` (and `Y`, `Z`) : saturation on an axis iff it has `2`
  or `3` sites.
- `nava_robertson_schrodinger_cube` : from `4 × 4 × 4` on, strict on the three axes.
- `cubePairs` : the six observables `(H, X)` of the three axes.
- `bracketMatrix_cubePairs` : in every state `Ω` is block diagonal, one block per axis.
- `robertson_det_cube` : Robertson's relation for the six observables, in every state.
- `covarianceMatrix_maxCurrentCubeState` : in the maximal current state `Σ` is block diagonal.
- `det_covarianceMatrix_maxCurrentCubeState` : `det Σ = (C_Nava(x) C_Nava(y) C_Nava(z))² |det Ω|`.
- `robertson_det_maxCurrentCubeState_strict` : from `4 × 4 × 4` on, `|det Ω| < det Σ`.

## iii. Table of contents

- A. Observables along the axes
- B. Different axes commute
- C. The maximal current state of the cube
- D. The uncertainty relation along each axis
- E. Robertson's relation for the six observables of the cube
- F. Robertson's relation in the maximal current state of the cube

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open scoped ComplexOrder selfAdjoint QuantumMechanics.FiniteHilbertSpace
open ProbabilisticTheory
open QuantumMechanics FiniteHilbertSpace UnitalPositiveLinearMap
variable (Tx Ty Tz : TightBindingChain)

/-!

## A. Observables along the axes

-/

/-- The Hilbert space of the cube: states on the sites `(nx, ny, nz)`. -/
abbrev CubeHilbertSpace := 𝓗[Fin Tx.N × Fin Ty.N × Fin Tz.N]

/-- The operators on the Hilbert space of the cube. -/
abbrev CubeOperators := Tx.CubeHilbertSpace Ty Tz →L[ℂ] Tx.CubeHilbertSpace Ty Tz

/-- An observable of the chain `Tx` acting on the `x` axis of the cube. -/
noncomputable abbrev alongX (a : Observable (Tx.HilbertSpace →L[ℂ] Tx.HilbertSpace)) :
    Observable (Tx.CubeOperators Ty Tz) :=
  onFstObservable a

/-- An observable of the chain `Ty` acting on the `y` axis of the cube. -/
noncomputable abbrev alongY (b : Observable (Ty.HilbertSpace →L[ℂ] Ty.HilbertSpace)) :
    Observable (Tx.CubeOperators Ty Tz) :=
  onSndObservable (onFstObservable b)

/-- An observable of the chain `Tz` acting on the `z` axis of the cube. -/
noncomputable abbrev alongZ (c : Observable (Tz.HilbertSpace →L[ℂ] Tz.HilbertSpace)) :
    Observable (Tx.CubeOperators Ty Tz) :=
  onSndObservable (onSndObservable c)

/-!

## B. Different axes commute

-/

/-- Commuting observables have a vanishing bracket. -/
private lemma bracket_eq_zero_of_mul_comm {A : Type*} [CStarAlgebra A]
    {a b : Observable A} (h : (a : A) * b = b * a) : ⁅a, b⁆ = 0 := by
  apply Subtype.ext
  rw [selfAdjoint.coe_bracket, h, sub_self, smul_zero]
  rfl

/-- Observables of the `x` and `y` axes commute. -/
lemma bracket_alongX_alongY (a : Observable (Tx.HilbertSpace →L[ℂ] Tx.HilbertSpace))
    (b : Observable (Ty.HilbertSpace →L[ℂ] Ty.HilbertSpace)) :
    ⁅Tx.alongX Ty Tz a, Tx.alongY Ty Tz b⁆ = 0 :=
  bracket_eq_zero_of_mul_comm <| ContinuousLinearMap.ext fun Ψ =>
    LinearMap.congr_fun (onFst_comp_onSnd _ _) Ψ

/-- Observables of the `x` and `z` axes commute. -/
lemma bracket_alongX_alongZ (a : Observable (Tx.HilbertSpace →L[ℂ] Tx.HilbertSpace))
    (c : Observable (Tz.HilbertSpace →L[ℂ] Tz.HilbertSpace)) :
    ⁅Tx.alongX Ty Tz a, Tx.alongZ Ty Tz c⁆ = 0 :=
  bracket_eq_zero_of_mul_comm <| ContinuousLinearMap.ext fun Ψ =>
    LinearMap.congr_fun (onFst_comp_onSnd _ _) Ψ

/-- Observables of the `y` and `z` axes commute. -/
lemma bracket_alongY_alongZ (b : Observable (Ty.HilbertSpace →L[ℂ] Ty.HilbertSpace))
    (c : Observable (Tz.HilbertSpace →L[ℂ] Tz.HilbertSpace)) :
    ⁅Tx.alongY Ty Tz b, Tx.alongZ Ty Tz c⁆ = 0 :=
  bracket_eq_zero_of_mul_comm <| ContinuousLinearMap.ext fun Ψ => by
    have h := congrArg (onSnd (α := Fin Tx.N)) (onFst_comp_onSnd
      (β := Fin Tz.N) (b : Ty.HilbertSpace →L[ℂ] Ty.HilbertSpace).toLinearMap
      (c : Tz.HilbertSpace →L[ℂ] Tz.HilbertSpace).toLinearMap)
    rw [onSnd_comp, onSnd_comp] at h
    exact LinearMap.congr_fun h Ψ

/-!

## C. The maximal current state of the cube

-/

/-- The maximal current state of the cube, the product of those of the three chains. -/
noncomputable def maxCurrentCubeState : Tx.CubeHilbertSpace Ty Tz :=
  prodVec Tx.maxCurrentState (prodVec Ty.maxCurrentState Tz.maxCurrentState)

lemma norm_maxCurrentCubeState : ‖Tx.maxCurrentCubeState Ty Tz‖ = 1 :=
  norm_prodVec_eq_one Tx.norm_maxCurrentState
    (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState)

/-- The maximal current state of the cube as a state on its operators. -/
noncomputable abbrev maxCurrentCubeVectorState : 𝓢[ℂ, Tx.CubeOperators Ty Tz] :=
  ofVec (Tx.norm_maxCurrentCubeState Ty Tz)

/-!

## D. The uncertainty relation along each axis

-/

section Statistics

variable (a b : Observable (Tx.HilbertSpace →L[ℂ] Tx.HilbertSpace))
  (b' c' : Observable (Ty.HilbertSpace →L[ℂ] Ty.HilbertSpace))
  (b'' c'' : Observable (Tz.HilbertSpace →L[ℂ] Tz.HilbertSpace))

/-- Along `x`, the cube sees the statistics of the chain `Tx`. -/
lemma variance_alongX :
    variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongX Ty Tz a) =
      variance Tx.maxCurrentVectorState a :=
  variance_onFstObservable Tx.norm_maxCurrentState
    (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) a

lemma centeredGramDefect_alongX :
    centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongX Ty Tz a)
      (Tx.alongX Ty Tz b) = centeredGramDefect Tx.maxCurrentVectorState a b :=
  centeredGramDefect_onFstObservable Tx.norm_maxCurrentState
    (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) a b

/-- Along `y`, the cube sees the statistics of the chain `Ty`. -/
lemma variance_alongY :
    variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongY Ty Tz b') =
      variance Ty.maxCurrentVectorState b' :=
  (variance_onSndObservable Tx.norm_maxCurrentState
      (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _).trans
    (variance_onFstObservable Ty.norm_maxCurrentState Tz.norm_maxCurrentState b')

lemma centeredGramDefect_alongY :
    centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongY Ty Tz b')
      (Tx.alongY Ty Tz c') = centeredGramDefect Ty.maxCurrentVectorState b' c' :=
  (centeredGramDefect_onSndObservable Tx.norm_maxCurrentState
    (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _ _).trans
    (centeredGramDefect_onFstObservable Ty.norm_maxCurrentState Tz.norm_maxCurrentState b' c')

/-- Along `z`, the cube sees the statistics of the chain `Tz`. -/
lemma variance_alongZ :
    variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongZ Ty Tz b'') =
      variance Tz.maxCurrentVectorState b'' :=
  (variance_onSndObservable Tx.norm_maxCurrentState
      (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _).trans
    (variance_onSndObservable Ty.norm_maxCurrentState Tz.norm_maxCurrentState b'')

lemma centeredGramDefect_alongZ :
    centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongZ Ty Tz b'')
      (Tx.alongZ Ty Tz c'') = centeredGramDefect Tz.maxCurrentVectorState b'' c'' :=
  (centeredGramDefect_onSndObservable Tx.norm_maxCurrentState
    (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _ _).trans
    (centeredGramDefect_onSndObservable Ty.norm_maxCurrentState Tz.norm_maxCurrentState b'' c'')

end Statistics

/-- The `x` axis of the cube carries the constant `C_Nava` of the chain `Tx`. -/
lemma CNava_alongX :
    √(variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongX Ty Tz Tx.openHamiltonianObservable) *
      variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongX Ty Tz Tx.positionObservable)) /
        |Tx.a * Tx.t * Real.cos (Real.pi / (Tx.N + 1))| = Tx.CNava := by
  rw [variance_alongX, variance_alongX, CNava]

/-- The `y` axis of the cube carries the constant `C_Nava` of the chain `Ty`. -/
lemma CNava_alongY :
    √(variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongY Ty Tz Ty.openHamiltonianObservable) *
      variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongY Ty Tz Ty.positionObservable)) /
        |Ty.a * Ty.t * Real.cos (Real.pi / (Ty.N + 1))| = Ty.CNava := by
  rw [variance_alongY, variance_alongY, CNava]

/-- The `z` axis of the cube carries the constant `C_Nava` of the chain `Tz`. -/
lemma CNava_alongZ :
    √(variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongZ Ty Tz Tz.openHamiltonianObservable) *
      variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongZ Ty Tz Tz.positionObservable)) /
        |Tz.a * Tz.t * Real.cos (Real.pi / (Tz.N + 1))| = Tz.CNava := by
  rw [variance_alongZ, variance_alongZ, CNava]

/-- Along `x`, the centered Gram defect vanishes, that is the uncertainty relation is an
equality, iff the axis has `2` or `3` sites. -/
lemma centeredGramDefect_alongX_eq_zero_iff (ht : Tx.t ≠ 0) (hN : 2 ≤ Tx.N) :
    centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz)
      (Tx.alongX Ty Tz Tx.openHamiltonianObservable) (Tx.alongX Ty Tz Tx.positionObservable) = 0 ↔
      Tx.N = 2 ∨ Tx.N = 3 := by
  rw [centeredGramDefect_alongX]
  exact centeredGramDefect_maxCurrentState_eq_zero_iff Tx ht hN

/-- Along `y`, the uncertainty relation is an equality iff the axis has `2` or `3` sites. -/
lemma centeredGramDefect_alongY_eq_zero_iff (ht : Ty.t ≠ 0) (hN : 2 ≤ Ty.N) :
    centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz)
      (Tx.alongY Ty Tz Ty.openHamiltonianObservable) (Tx.alongY Ty Tz Ty.positionObservable) = 0 ↔
      Ty.N = 2 ∨ Ty.N = 3 := by
  rw [centeredGramDefect_alongY]
  exact centeredGramDefect_maxCurrentState_eq_zero_iff Ty ht hN

/-- Along `z`, the uncertainty relation is an equality iff the axis has `2` or `3` sites. -/
lemma centeredGramDefect_alongZ_eq_zero_iff (ht : Tz.t ≠ 0) (hN : 2 ≤ Tz.N) :
    centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz)
      (Tx.alongZ Ty Tz Tz.openHamiltonianObservable) (Tx.alongZ Ty Tz Tz.positionObservable) = 0 ↔
      Tz.N = 2 ∨ Tz.N = 3 := by
  rw [centeredGramDefect_alongZ]
  exact centeredGramDefect_maxCurrentState_eq_zero_iff Tz ht hN

/-- **Nava–Robertson–Schrödinger on the cube.** From `4 × 4 × 4` on, the uncertainty relation of
the maximal current state is strict on the three axes at once: the centered Gram defect of each
axis is positive. -/
theorem nava_robertson_schrodinger_cube (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    0 < centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongX Ty Tz Tx.openHamiltonianObservable) (Tx.alongX Ty Tz Tx.positionObservable) ∧
      0 < centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongY Ty Tz Ty.openHamiltonianObservable) (Tx.alongY Ty Tz Ty.positionObservable) ∧
      0 < centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongZ Ty Tz Tz.openHamiltonianObservable) (Tx.alongZ Ty Tz Tz.positionObservable) := by
  refine ⟨(centeredGramDefect_nonneg _ _ _).lt_of_ne fun h => ?_,
    (centeredGramDefect_nonneg _ _ _).lt_of_ne fun h => ?_,
    (centeredGramDefect_nonneg _ _ _).lt_of_ne fun h => ?_⟩
  · rcases (Tx.centeredGramDefect_alongX_eq_zero_iff Ty Tz hx (by omega)).mp h.symm with h | h <;>
      omega
  · rcases (Tx.centeredGramDefect_alongY_eq_zero_iff Ty Tz hy (by omega)).mp h.symm with h | h <;>
      omega
  · rcases (Tx.centeredGramDefect_alongZ_eq_zero_iff Ty Tz hz (by omega)).mp h.symm with h | h <;>
      omega

/-!

## E. Robertson's relation for the six observables of the cube

-/

open Matrix

/-- The conjugate pair of a chain: its Hamiltonian and its position. -/
noncomputable def conjugatePair (T : TightBindingChain) :
    Fin 2 → Observable (T.HilbertSpace →L[ℂ] T.HilbertSpace) :=
  ![T.openHamiltonianObservable, T.positionObservable]

/-- The six observables of the cube, the conjugate pair `(H, X)` of each axis: `(j, k)` is the
`j`-th member of the pair of the axis `k`. -/
noncomputable def cubePairs : Fin 2 × Fin 3 → Observable (Tx.CubeOperators Ty Tz) :=
  fun p => ![Tx.alongX Ty Tz (Tx.conjugatePair p.1), Tx.alongY Ty Tz (Ty.conjugatePair p.1),
    Tx.alongZ Ty Tz (Tz.conjugatePair p.1)] p.2

/-- The expectation `ω⟨⁅H, X⁆⟩` of the bracket of the pair of the axis `k`. -/
noncomputable def axisBracket (ω : 𝓢[ℂ, Tx.CubeOperators Ty Tz]) (k : Fin 3) : ℝ :=
  ω⟨⁅Tx.cubePairs Ty Tz (0, k), Tx.cubePairs Ty Tz (1, k)⁆⟩

@[simp]
lemma cubePairs_x (j : Fin 2) :
    Tx.cubePairs Ty Tz (j, 0) = Tx.alongX Ty Tz (Tx.conjugatePair j) := rfl

@[simp]
lemma cubePairs_y (j : Fin 2) :
    Tx.cubePairs Ty Tz (j, 1) = Tx.alongY Ty Tz (Ty.conjugatePair j) := rfl

@[simp]
lemma cubePairs_z (j : Fin 2) :
    Tx.cubePairs Ty Tz (j, 2) = Tx.alongZ Ty Tz (Tz.conjugatePair j) := rfl

/-- Swapping a bracket flips its sign. -/
private lemma bracket_swap {A : Type*} [CStarAlgebra A] (a b : Observable A) :
    ⁅b, a⁆ = -⁅a, b⁆ := by
  rw [selfAdjoint.bracket_def, selfAdjoint.lieMul_swap, ← selfAdjoint.bracket_def]

private lemma bracket_swap_eq_zero {A : Type*} [CStarAlgebra A] {a b : Observable A}
    (h : ⁅a, b⁆ = 0) : ⁅b, a⁆ = 0 := by
  rw [bracket_swap, h, neg_zero]

/-- Observables of different axes of the cube commute. -/
lemma bracket_cubePairs_of_ne {p q : Fin 2 × Fin 3} (h : p.2 ≠ q.2) :
    ⁅Tx.cubePairs Ty Tz p, Tx.cubePairs Ty Tz q⁆ = 0 := by
  obtain ⟨j, k⟩ := p
  obtain ⟨j', k'⟩ := q
  match k, k', h with
  | 0, 0, hne => exact absurd rfl hne
  | 1, 1, hne => exact absurd rfl hne
  | 2, 2, hne => exact absurd rfl hne
  | 0, 1, _ => exact Tx.bracket_alongX_alongY Ty Tz _ _
  | 0, 2, _ => exact Tx.bracket_alongX_alongZ Ty Tz _ _
  | 1, 2, _ => exact Tx.bracket_alongY_alongZ Ty Tz _ _
  | 1, 0, _ => exact bracket_swap_eq_zero (Tx.bracket_alongX_alongY Ty Tz _ _)
  | 2, 0, _ => exact bracket_swap_eq_zero (Tx.bracket_alongX_alongZ Ty Tz _ _)
  | 2, 1, _ => exact bracket_swap_eq_zero (Tx.bracket_alongY_alongZ Ty Tz _ _)

private lemma expectation_zero {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ω : 𝓢[ℂ, A]) : ω⟨(0 : Observable A)⟩ = 0 :=
  Complex.ofReal_injective <| by rw [← apply_observable_eq_expectation]; simp

private lemma expectation_neg {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ω : 𝓢[ℂ, A]) (a : Observable A) : ω⟨-a⟩ = -ω⟨a⟩ :=
  Complex.ofReal_injective <| by
    rw [Complex.ofReal_neg, ← apply_observable_eq_expectation, ← apply_observable_eq_expectation]
    simp

/-- In every state of the cube the bracket matrix `Ω` of the six observables is block diagonal,
one antisymmetric `2 × 2` block per axis. -/
lemma bracketMatrix_cubePairs (ω : 𝓢[ℂ, Tx.CubeOperators Ty Tz]) :
    bracketMatrix ω (Tx.cubePairs Ty Tz) =
      blockDiagonal fun k => !![0, Tx.axisBracket Ty Tz ω k; -Tx.axisBracket Ty Tz ω k, 0] := by
  ext ⟨j, k⟩ ⟨j', k'⟩
  rw [bracketMatrix, of_apply, blockDiagonal_apply]
  split_ifs with h
  · simp only at h
    subst h
    have hself (i : Fin 2) : ω⟨⁅Tx.cubePairs Ty Tz (i, k), Tx.cubePairs Ty Tz (i, k)⁆⟩ = 0 := by
      rw [selfAdjoint.bracket_def, selfAdjoint.lieMul_self, expectation_zero]
    match j, j' with
    | 0, 0 => exact hself 0
    | 0, 1 => rfl
    | 1, 0 => exact (congrArg _ (bracket_swap _ _)).trans (expectation_neg _ _)
    | 1, 1 => exact hself 1
  · rw [Tx.bracket_cubePairs_of_ne Ty Tz h, expectation_zero]

/-- **Robertson's relation on the cube.** In every state of the cube the volume `det Σ` of the
dispersion of the six observables is at least the product of the squared brackets of the three
axes. -/
theorem robertson_det_cube (ω : 𝓢[ℂ, Tx.CubeOperators Ty Tz]) :
    (Tx.axisBracket Ty Tz ω 0 * Tx.axisBracket Ty Tz ω 1 * Tx.axisBracket Ty Tz ω 2) ^ 2 ≤
      (covarianceMatrix ω (Tx.cubePairs Ty Tz)).det := by
  have h := robertson_det ω (Tx.cubePairs Ty Tz)
  rw [bracketMatrix_cubePairs, det_blockDiagonal, Fin.prod_univ_three] at h
  simp only [det_fin_two_of, zero_mul, zero_sub, mul_neg, neg_neg] at h
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
    (mul_self_nonneg _))] at h
  linarith

/-!

## F. Robertson's relation in the maximal current state of the cube

-/

section MaxCurrent

variable (a b : Observable (Tx.HilbertSpace →L[ℂ] Tx.HilbertSpace))
  (b' c' : Observable (Ty.HilbertSpace →L[ℂ] Ty.HilbertSpace))
  (b'' c'' : Observable (Tz.HilbertSpace →L[ℂ] Tz.HilbertSpace))

lemma covariance_alongX :
    covariance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongX Ty Tz a) (Tx.alongX Ty Tz b) =
      covariance Tx.maxCurrentVectorState a b :=
  covariance_onFstObservable Tx.norm_maxCurrentState
    (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) a b

lemma covariance_alongY :
    covariance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongY Ty Tz b') (Tx.alongY Ty Tz c') =
      covariance Ty.maxCurrentVectorState b' c' :=
  (covariance_onSndObservable Tx.norm_maxCurrentState
    (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _ _).trans
    (covariance_onFstObservable Ty.norm_maxCurrentState Tz.norm_maxCurrentState b' c')

lemma covariance_alongZ :
    covariance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongZ Ty Tz b'') (Tx.alongZ Ty Tz c'') =
      covariance Tz.maxCurrentVectorState b'' c'' :=
  (covariance_onSndObservable Tx.norm_maxCurrentState
    (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _ _).trans
    (covariance_onSndObservable Ty.norm_maxCurrentState Tz.norm_maxCurrentState b'' c'')

/-- In the maximal current state of the cube the `x` and `y` axes are uncorrelated. -/
lemma covariance_alongX_alongY :
    covariance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongX Ty Tz a) (Tx.alongY Ty Tz b') = 0 :=
  covariance_onFstObservable_onSndObservable Tx.norm_maxCurrentState
    (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _ _

/-- In the maximal current state of the cube the `x` and `z` axes are uncorrelated. -/
lemma covariance_alongX_alongZ :
    covariance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongX Ty Tz a) (Tx.alongZ Ty Tz b'') = 0 :=
  covariance_onFstObservable_onSndObservable Tx.norm_maxCurrentState
    (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _ _

/-- In the maximal current state of the cube the `y` and `z` axes are uncorrelated. -/
lemma covariance_alongY_alongZ :
    covariance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongY Ty Tz b') (Tx.alongZ Ty Tz b'') =
      0 :=
  (covariance_onSndObservable Tx.norm_maxCurrentState
    (norm_prodVec_eq_one Ty.norm_maxCurrentState Tz.norm_maxCurrentState) _ _).trans
    (covariance_onFstObservable_onSndObservable Ty.norm_maxCurrentState
      Tz.norm_maxCurrentState b' b'')

end MaxCurrent

/-- In the maximal current state of the cube the covariance matrix `Σ` of the six observables is
block diagonal, the block of each axis being the covariance matrix of its chain. -/
lemma covarianceMatrix_maxCurrentCubeState :
    covarianceMatrix (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz) =
      blockDiagonal ![covarianceMatrix Tx.maxCurrentVectorState Tx.conjugatePair,
        covarianceMatrix Ty.maxCurrentVectorState Ty.conjugatePair,
        covarianceMatrix Tz.maxCurrentVectorState Tz.conjugatePair] := by
  ext ⟨j, k⟩ ⟨j', k'⟩
  rw [covarianceMatrix, of_apply, blockDiagonal_apply]
  split_ifs with h
  · simp only at h
    subst h
    match k with
    | 0 => exact Tx.covariance_alongX Ty Tz _ _
    | 1 => exact Tx.covariance_alongY Ty Tz _ _
    | 2 => exact Tx.covariance_alongZ Ty Tz _ _
  · match k, k', h with
    | 0, 0, hne => exact absurd rfl hne
    | 1, 1, hne => exact absurd rfl hne
    | 2, 2, hne => exact absurd rfl hne
    | 0, 1, _ => exact Tx.covariance_alongX_alongY Ty Tz _ _
    | 0, 2, _ => exact Tx.covariance_alongX_alongZ Ty Tz _ _
    | 1, 2, _ => exact Tx.covariance_alongY_alongZ Ty Tz _ _
    | 1, 0, _ => exact (covariance_comm _ _ _).trans (Tx.covariance_alongX_alongY Ty Tz _ _)
    | 2, 0, _ => exact (covariance_comm _ _ _).trans (Tx.covariance_alongX_alongZ Ty Tz _ _)
    | 2, 1, _ => exact (covariance_comm _ _ _).trans (Tx.covariance_alongY_alongZ Ty Tz _ _)

/-- In the maximal current state of a chain, `det Σ = C_Nava² (a t cos (π / (N + 1)))²` for the
pair `(H, X)`. -/
lemma det_covarianceMatrix_conjugatePair (T : TightBindingChain) (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    (covarianceMatrix T.maxCurrentVectorState T.conjugatePair).det =
      T.CNava ^ 2 * (T.a * T.t * Real.cos (Real.pi / (T.N + 1))) ^ 2 := by
  rw [det_fin_two, covarianceMatrix, of_apply, of_apply, of_apply, of_apply]
  change variance _ _ * variance _ _ - covariance _ T.openHamiltonianObservable
    T.positionObservable * covariance _ T.positionObservable T.openHamiltonianObservable = _
  rw [covariance_comm _ T.positionObservable, covariance_maxCurrentState, mul_zero, sub_zero,
    CNava, div_pow, Real.sq_sqrt (mul_nonneg (variance_nonneg _ _) (variance_nonneg _ _)),
    sq_abs, div_mul_cancel₀ _ (pow_ne_zero 2 (T.bound_ne_zero ht hN))]
  rfl

/-- In the maximal current state of the cube, the bracket of each axis is that of its chain,
`± a t cos (π / (N + 1))`. -/
lemma sq_axisBracket_maxCurrentCubeState :
    (Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 0 *
        Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 1 *
        Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 2) ^ 2 =
      (Tx.a * Tx.t * Real.cos (Real.pi / (Tx.N + 1)) *
        (Ty.a * Ty.t * Real.cos (Real.pi / (Ty.N + 1))) *
        (Tz.a * Tz.t * Real.cos (Real.pi / (Tz.N + 1)))) ^ 2 := by
  have hx := robertson_gap_decomposition (Tx.maxCurrentCubeVectorState Ty Tz)
    (Tx.alongX Ty Tz Tx.openHamiltonianObservable) (Tx.alongX Ty Tz Tx.positionObservable)
  have hy := robertson_gap_decomposition (Tx.maxCurrentCubeVectorState Ty Tz)
    (Tx.alongY Ty Tz Ty.openHamiltonianObservable) (Tx.alongY Ty Tz Ty.positionObservable)
  have hz := robertson_gap_decomposition (Tx.maxCurrentCubeVectorState Ty Tz)
    (Tx.alongZ Ty Tz Tz.openHamiltonianObservable) (Tx.alongZ Ty Tz Tz.positionObservable)
  rw [variance_alongX, variance_alongX, centeredGramDefect_alongX, covariance_alongX,
    covariance_maxCurrentState, variance_mul_variance_maxCurrentState] at hx
  rw [variance_alongY, variance_alongY, centeredGramDefect_alongY, covariance_alongY,
    covariance_maxCurrentState, variance_mul_variance_maxCurrentState] at hy
  rw [variance_alongZ, variance_alongZ, centeredGramDefect_alongZ, covariance_alongZ,
    covariance_maxCurrentState, variance_mul_variance_maxCurrentState] at hz
  have ex : Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 0 ^ 2 =
      (Tx.a * Tx.t * Real.cos (Real.pi / (Tx.N + 1))) ^ 2 := by
    change (Tx.maxCurrentCubeVectorState Ty Tz)⟨⁅Tx.alongX Ty Tz Tx.openHamiltonianObservable,
      Tx.alongX Ty Tz Tx.positionObservable⁆⟩ ^ 2 = _
    linarith
  have ey : Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 1 ^ 2 =
      (Ty.a * Ty.t * Real.cos (Real.pi / (Ty.N + 1))) ^ 2 := by
    change (Tx.maxCurrentCubeVectorState Ty Tz)⟨⁅Tx.alongY Ty Tz Ty.openHamiltonianObservable,
      Tx.alongY Ty Tz Ty.positionObservable⁆⟩ ^ 2 = _
    linarith
  have ez : Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 2 ^ 2 =
      (Tz.a * Tz.t * Real.cos (Real.pi / (Tz.N + 1))) ^ 2 := by
    change (Tx.maxCurrentCubeVectorState Ty Tz)⟨⁅Tx.alongZ Ty Tz Tz.openHamiltonianObservable,
      Tx.alongZ Ty Tz Tz.positionObservable⁆⟩ ^ 2 = _
    linarith
  rw [mul_pow, mul_pow, ex, ey, ez]
  ring

/-- In the maximal current state of the cube, `det Σ = C_Nava(x)² C_Nava(y)² C_Nava(z)² |det Ω|`:
the ratio of the two sides of Robertson's relation is the product of the constants of the three
axes. -/
lemma det_covarianceMatrix_maxCurrentCubeState (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) :
    (covarianceMatrix (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz)).det =
      (Tx.CNava * Ty.CNava * Tz.CNava) ^ 2 *
        (Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 0 *
          Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 1 *
          Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 2) ^ 2 := by
  rw [sq_axisBracket_maxCurrentCubeState, covarianceMatrix_maxCurrentCubeState,
    det_blockDiagonal, Fin.prod_univ_three]
  simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons]
  rw [det_covarianceMatrix_conjugatePair Tx hx hNx, det_covarianceMatrix_conjugatePair Ty hy hNy,
    det_covarianceMatrix_conjugatePair Tz hz hNz]
  ring

/-- **Robertson's relation is strict in the maximal current state of the cube.** From
`4 × 4 × 4` on, `|det Ω| < det Σ` for the six observables of the cube. -/
theorem robertson_det_maxCurrentCubeState_strict (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0)
    (hz : Tz.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    |(bracketMatrix (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz)).det| <
      (covarianceMatrix (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz)).det := by
  rw [Tx.det_covarianceMatrix_maxCurrentCubeState Ty Tz hx hy hz (by omega) (by omega)
    (by omega), bracketMatrix_cubePairs, det_blockDiagonal, Fin.prod_univ_three]
  simp only [det_fin_two_of, zero_mul, zero_sub, mul_neg, neg_neg]
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
    (mul_self_nonneg _))]
  have hpos : 0 < (Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 0 *
      Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 1 *
      Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 2) ^ 2 := by
    rw [sq_axisBracket_maxCurrentCubeState]
    exact (sq_nonneg _).lt_of_ne (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero
      (Tx.bound_ne_zero hx (by omega)) (Ty.bound_ne_zero hy (by omega)))
      (Tz.bound_ne_zero hz (by omega)))).symm
  have hC : 1 < (Tx.CNava * Ty.CNava * Tz.CNava) ^ 2 :=
    one_lt_pow₀ (one_lt_mul_of_lt_of_le (one_lt_mul_of_lt_of_le (Tx.one_lt_CNava hx hNx)
      (Ty.one_le_CNava hy (by omega))) (Tz.one_le_CNava hz (by omega))) two_ne_zero
  nlinarith

end TightBindingChain
end CondensedMatter
