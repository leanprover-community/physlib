/-
Copyright (c) 2026 Keith Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.MeanInequalities
public meta import ProofWidgets.Component.HtmlDisplay
public meta import ProofWidgets.Component.Recharts
/-!

# The composition law for transition amplitudes

Inserting a complete set of intermediate states between two unitary evolutions.

## i. Overview

If a system evolves from `ψ` by a unitary `U₁` and then by a unitary `U₂`, the transition
amplitude to `φ` can be computed by summing over a complete orthonormal set of intermediate
states `e i`:
`⟨φ| U₂ U₁ |ψ⟩ = ∑ i, ⟨φ| U₂ |e i⟩ ⟨e i| U₁ |ψ⟩`.
This is the composition law behind the gluing of path integrals in time.

The sum converges absolutely, with `∑ i, |⟨φ| U₂ |e i⟩ ⟨e i| U₁ |ψ⟩| ≤ ‖φ‖ ‖ψ‖`, by Bessel's
inequality and the Cauchy-Schwarz inequality for sums. The bound uses nothing about the dynamics
except that `U₁` and `U₂` are unitary: it holds for every pair of unitaries on every Hilbert
space, finite or infinite dimensional. In particular, absolute convergence of the sum over
intermediate states is automatic once time evolution is unitary, and carries no information about
ultraviolet behaviour.

## ii. Key results

- `summable_norm_inner_mul_inner`: for any orthonormal family the products are absolutely
  summable.
- `tsum_norm_inner_mul_inner_le`: their sum is at most `‖x‖ ‖y‖`.
- `inner_comp_eq_tsum`: the composition law for two bounded operators and a Hilbert basis.
- `tsum_norm_amplitude_le`: for unitary `U₁`, `U₂` the sum of the moduli of the intermediate
  amplitudes is at most `‖φ‖ ‖ψ‖`.

## iii. Table of contents

- A. Absolute convergence for an orthonormal family
- B. The composition law
- C. Visualization

## iv. References

- R. P. Feynman, A. R. Hibbs, "Quantum Mechanics and Path Integrals", McGraw-Hill (1965),
  section 2-5 (events occurring in succession).
- M. Reed, B. Simon, "Methods of Modern Mathematical Physics I: Functional Analysis",
  Academic Press (1980), section II.3 (Bessel's inequality and orthonormal bases).

-/

@[expose] public section

namespace QuantumMechanics

namespace CompositionLaw

open scoped InnerProductSpace

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-!

## A. Absolute convergence for an orthonormal family

-/

/-- Cauchy-Schwarz and Bessel together: for an orthonormal family `v`, the moduli
  `‖⟪x, v i⟫‖ ‖⟪v i, y⟫‖` are summable with sum at most `‖x‖ ‖y‖`. -/
lemma summable_and_tsum_norm_inner_mul_inner_le {v : ι → E} (hv : Orthonormal 𝕜 v) (x y : E) :
    (Summable fun i => ‖⟪x, v i⟫_𝕜 * ⟪v i, y⟫_𝕜‖) ∧
      ∑' i, ‖⟪x, v i⟫_𝕜 * ⟪v i, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ := by
  have hsq : ∀ z : E, Summable fun i => ‖⟪v i, z⟫_𝕜‖ ^ (2 : ℝ) := fun z => by
    simpa [Real.rpow_two] using hv.inner_products_summable z
  have hroot : ∀ z : E, (∑' i, ‖⟪v i, z⟫_𝕜‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ ‖z‖ := fun z => by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq (norm_nonneg z)]
    exact Real.sqrt_le_sqrt (by simpa [Real.rpow_two] using hv.tsum_inner_products_le z)
  have key := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun i => norm_nonneg ⟪v i, x⟫_𝕜) (fun i => norm_nonneg ⟪v i, y⟫_𝕜) (hsq x) (hsq y)
  have heq : (fun i => ‖⟪x, v i⟫_𝕜 * ⟪v i, y⟫_𝕜‖) =
      fun i => ‖⟪v i, x⟫_𝕜‖ * ‖⟪v i, y⟫_𝕜‖ := by
    funext i
    rw [norm_mul, norm_inner_symm]
  rw [heq]
  refine ⟨key.1, key.2.trans ?_⟩
  exact mul_le_mul (hroot x) (hroot y) (by positivity) (norm_nonneg x)

/-- The products of amplitudes against an orthonormal family are absolutely summable. -/
lemma summable_norm_inner_mul_inner {v : ι → E} (hv : Orthonormal 𝕜 v) (x y : E) :
    Summable fun i => ‖⟪x, v i⟫_𝕜 * ⟪v i, y⟫_𝕜‖ :=
  (summable_and_tsum_norm_inner_mul_inner_le hv x y).1

/-- The sum of the moduli of the products of amplitudes is at most `‖x‖ ‖y‖`. -/
lemma tsum_norm_inner_mul_inner_le {v : ι → E} (hv : Orthonormal 𝕜 v) (x y : E) :
    ∑' i, ‖⟪x, v i⟫_𝕜 * ⟪v i, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ :=
  (summable_and_tsum_norm_inner_mul_inner_le hv x y).2

/-!

## B. The composition law

-/

variable [CompleteSpace E]

/-- The composition law: the amplitude `⟨φ| U₂ U₁ |ψ⟩` is the sum over a complete orthonormal
  set of intermediate states of `⟨φ| U₂ |e i⟩ ⟨e i| U₁ |ψ⟩`. -/
lemma inner_comp_eq_tsum (b : HilbertBasis ι 𝕜 E) (U₁ U₂ : E →L[𝕜] E) (φ ψ : E) :
    ⟪φ, U₂ (U₁ ψ)⟫_𝕜 = ∑' i, ⟪φ, U₂ (b i)⟫_𝕜 * ⟪b i, U₁ ψ⟫_𝕜 := by
  have h : ∀ w, ⟪φ, U₂ w⟫_𝕜 = ⟪ContinuousLinearMap.adjoint U₂ φ, w⟫_𝕜 := fun w =>
    (ContinuousLinearMap.adjoint_inner_left U₂ w φ).symm
  simp_rw [h]
  exact (b.tsum_inner_mul_inner _ _).symm

/-- For unitary evolutions the sum over intermediate states converges absolutely, with the sum of
  the moduli at most `‖φ‖ ‖ψ‖`. Only unitarity is used. -/
lemma tsum_norm_amplitude_le (b : HilbertBasis ι 𝕜 E) {U₁ U₂ : E →L[𝕜] E}
    (hU₁ : U₁ ∈ unitary (E →L[𝕜] E)) (hU₂ : U₂ ∈ unitary (E →L[𝕜] E)) (φ ψ : E) :
    ∑' i, ‖⟪φ, U₂ (b i)⟫_𝕜 * ⟪b i, U₁ ψ⟫_𝕜‖ ≤ ‖φ‖ * ‖ψ‖ := by
  have h : ∀ w, ⟪φ, U₂ w⟫_𝕜 = ⟪ContinuousLinearMap.adjoint U₂ φ, w⟫_𝕜 := fun w =>
    (ContinuousLinearMap.adjoint_inner_left U₂ w φ).symm
  simp_rw [h]
  have h₂ : ‖(ContinuousLinearMap.adjoint U₂) φ‖ = ‖φ‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem hU₂) φ
  have h₁ : ‖U₁ ψ‖ = ‖ψ‖ := ContinuousLinearMap.norm_map_of_mem_unitary hU₁ ψ
  rw [← h₁, ← h₂]
  exact tsum_norm_inner_mul_inner_le b.orthonormal _ _

end CompositionLaw

end QuantumMechanics

end

/-!

## C. Visualization

Put the cursor on the `#html` line below. For the normalized states with components
`⟨e k|φ⟩ ∝ 1 / k` and `⟨e k|ψ⟩ ∝ 1 / k ^ (3 / 4)` in an orthonormal basis, the chart shows the
partial sums of `|⟨φ|e k⟩ ⟨e k|ψ⟩|` against the number of intermediate states kept, below the
bound `‖φ‖ ‖ψ‖ = 1` of `tsum_norm_amplitude_le`.

-/

public meta section

open Lean ProofWidgets Recharts

namespace QuantumMechanics.CompositionLaw

/-- `∑ k ≤ n, 1 / k ^ s`, used to normalize the example states. -/
def zetaPartial (s : Float) (n : ℕ) : Float :=
  (List.range n).foldl (fun acc k => acc + 1 / (k + 1).toFloat ^ s) 0

/-- Partial sums of the moduli of the intermediate amplitudes for the example states. -/
def compositionData (nMax : ℕ := 200) (cutoff : ℕ := 100000) : Array Json :=
  let cφ := 1 / Float.sqrt (zetaPartial 2 cutoff)
  let cψ := 1 / Float.sqrt (zetaPartial 1.5 cutoff)
  let (_, out) := (List.range nMax).foldl (init := ((0 : Float), (#[] : Array Json)))
    fun (acc, out) k =>
      let n := (k + 1).toFloat
      let acc := acc + cφ * cψ / (n * n ^ 0.75)
      (acc, out.push (json% {n: $(k + 1), total: $(acc), bound: $((1 : Float))}))
  out

/-- Line chart of the partial sums against the bound. -/
def compositionPlot : ProofWidgets.Html :=
  let caption : ProofWidgets.Html := .text "Partial sums of |⟨φ|e_k⟩⟨e_k|ψ⟩| (blue) against \
    the number of intermediate states, and the bound ‖φ‖‖ψ‖ = 1 (red)."
  jsx%{<div>
    <p>{caption}</p>
    <LineChart width={480} height={320} data={compositionData}>
      <XAxis dataKey?="n" />
      <YAxis domain?={#[toJson 0, toJson 1.1]} />
      <Line type={.linear} dataKey="total" stroke="#1f77b4" dot?={Bool.false} />
      <Line type={.linear} dataKey="bound" stroke="#d62728" dot?={Bool.false} />
    </LineChart>
  </div>}

#html compositionPlot

end QuantumMechanics.CompositionLaw

end
