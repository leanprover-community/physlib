# Mathematics vs Physics

Within Physlib mathematics and physics often intertwine, and it is important to get the separation between them correct. If not someone who is expecting to read results about Physics will be reading results about Mathematics and vice-versa.

## Contents

1. [General physics results in Physlib](#physics-results)
2. [The ./Mathematics directory](#mathematics-directory)
3. [Don't put physics in ./Mathematics](#no-physics-in-mathematics)
4. [Use physics where possible](#use-physics-where-possible)
5. [The ./Mathematics/ForMathlib directory](#formathlib-directory)
6. [Check Mathlib first](#check-mathlib-first)

<a id="physics-results"></a>

## General physics results in Physlib

A result not within the ./Mathematics directory of Physlib should be written in terms of definitions and structures carrying their physical context. To give two examples:

Firstly, in classical mechanics. The following would be acceptable
```lean
lemma energy_conservation_of_equationOfMotion (γ : Trajectory)
    (hγ : ContMDiff 𝓘(ℝ, Time) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞ γ)
    (h : S.EquationOfMotion γ) : ∂ₜ (S.energy γ) = 0
```
whilst the following would not
```lean
lemma deriv_half_mul_sq_add_eq_zero (m k : ℝ) (x : ℝ → ℝ) (hx : ContDiff ℝ ∞ x)
    (h : ∀ t, m * deriv (deriv x) t = - k * x t) :
    deriv (fun t => 1 / 2 * m * (deriv x t) ^ 2 + 1 / 2 * k * (x t) ^ 2) = 0
```

Secondly, in Probabilistic theory. The following would be acceptable
```lean
/-- State–effect evaluation takes values in `[0, 1]`. -/
lemma apply_mem_Icc (ω : 𝓢[ℝ, E]) (e : Effect E) : ω e ∈ Set.Icc 0 1
```
whilst the following would not
```lean
lemma apply_mem_Icc_of_mem_Icc (ω : E →ₚ₁[ℝ] ℝ) {A : E} (hA : A ∈ Set.Icc (0 : E) 1) :
    ω A ∈ Set.Icc (0 : ℝ) 1
```

A file should read like physics. Proofs of results may unfold down to the underlying mathematics.

<a id="mathematics-directory"></a>

## The ./Mathematics directory

(excluding ./ForMathlib, which is discussed in the next [section](#check-mathlib-first))

The ./Mathematics directory is for areas of mathematics that are either used predominantly by physicists, or in which physicists have their own conventions and ways of working. Some mathematics in Mathlib is set up in a form that suits mathematicians but is not directly usable in physics, and cannot easily be adapted to it. This directory is where those results are developed again in the form a physicist would use. It is not a place for one-off lemmas that a single physics proof happened to need. Examples include variational calculus, explicit forms of groups, special functions etc.

The results in ./Mathematics support the physics; they do not replace it. Even written in a physicist's conventions, a result there is still a statement about mathematical objects. Where it is used, it should be stated again in terms of the physical system it describes, with the mathematical result doing the work in the proof.

For the physicists' Hermite polynomials, the following appears in  [Physlib/Mathematics/SpecialFunctions/PhysHermite.lean](../../Physlib/Mathematics/SpecialFunctions/PhysHermite.lean)
```lean
lemma physHermite_orthogonal {n m : ℕ} (hnm : n ≠ m) :
    ∫ x : ℝ, (physHermite n x * physHermite m x) * Real.exp (- x ^ 2) = 0
```
whilst the following appears in [Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Eigenfunction.lean](../../Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Eigenfunction.lean)
```lean
/-- The eigenfunctions are orthonormal within the Hilbert space. -/
lemma eigenfunction_orthonormal :
    Orthonormal ℂ (fun n => HilbertSpace.mk (Q.eigenfunction_memHS n))
```


<a id="formathlib-directory"></a>

## The ./Mathematics/ForMathlib directory


If you’re formalizing a physics result and need mathematical machinery that would fit in Mathlib, ForMathlib gives you a place to put it while it’s being prepared for upstream. The ./Mathematics/ForMathlib directory is only for results that you genuinely expect to be contributed to Mathlib. A result belongs there if it is stated in Mathlib's own language and generality, with no physics in it, and would be accepted upstream as it stands or with minor changes. It is not a holding area for general-looking lemmas that have no other obvious home.

Two rules are checked automatically: a file in ForMathlib may only import other files from ForMathlib (and Mathlib), and every file there must be used somewhere outside the directory. This latter point is to prevent people storing results in Physlib which should really go in Mathlib, and which don't have a use in Physlib. Do not try and get around this by putting such things into ./Mathematics more generally.

<a id="no-physics-in-mathematics"></a>

## Don't put physics in ./Mathematics

A result in ./Mathematics should be a statement about mathematical objects only. It should not mention Time, Space, a physical constant, or a structure describing a physical system such as HarmonicOscillator, and a file there should not import from the physics directories. Someone reading ./Mathematics should be able to follow it without knowing which physical system the result was first needed for.

If a result only makes sense for a particular physical system, it is physics, and belongs with that system.

This is related to [Little math results](Basic.md#little-math-results) in the basics handbook.

<a id="use-physics-where-possible"></a>

## Use physics where possible

Unless you are developing a whole area of mathematics, write every lemma, auxiliary ones included, in terms of the physical quantities involved, in a file outside ./Mathematics. Someone else working on the same physics may need that result, and they should be able to use it as stated rather than first translating it back from the underlying mathematics.




<a id="check-mathlib-first"></a>

## Check Mathlib first

If you are adding a maths result to ./Mathematics make sure it is not already in Mathlib. We live downstream of Mathlib, and do not want to repeat results there.
