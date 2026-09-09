/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Statistics
public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Lie
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.GNS

/-!

# Uncertainty relations

Positivity of a state gives a Cauchy–Schwarz inequality for expectation values. Applied to
centered observables, this yields the Robertson–Schrödinger and Robertson uncertainty relations.

Unlike `StarAlgebra.Statistics`, this file genuinely needs a C⋆-algebra: `gns_cauchy_schwarz`, the
seed of every inequality below, is Cauchy–Schwarz for the sesquilinear form `(x, y) ↦ ω(x⋆y)`, and
the cleanest route to it is through the GNS Hilbert space `ω.GNS` of `CStarAlgebra.GNS` — the
completion needs `CStarAlgebra A`, not just a bare star-ordered ring. We get it from the
already-built `UnitalPositiveLinearMap.gnsRep`/`gnsCyclicVector` API (rather than reaching past
`GNS.lean` into mathlib's raw `PreGNS` machinery) via the identity
`⟪π_ω(x) Ω_ω, π_ω(y) Ω_ω⟫ = ω(x⋆y)`: expand the inner product using that `π_ω` is a
⋆-representation and that `Ω_ω` reproduces `ω` (`inner_gnsCyclicVector_gnsRep_gnsCyclicVector`),
then invoke the general Cauchy–Schwarz inequality `inner_mul_inner_self_le` on the Hilbert space
`ω.GNS`.

The commutator observable used to state the relations is the Lie bracket `⁅a, b⁆` already built in
`StarAlgebra/Lie.lean`; the only fact about it needed here beyond what that file already proves is
that centering leaves it unchanged (`bracket_centered`).

## Main results

- `gns_cauchy_schwarz` : Cauchy–Schwarz for the state-induced sesquilinear form on `A`.
- `robertson_schrodinger` : the Robertson–Schrödinger uncertainty inequality, jointly bounding
  covariance and the commutator's expectation by the product of the spreads.
- `covariance_cauchy_schwarz`, `robertson` : the familiar `|correlation| ≤ σ_a σ_b` and
  Heisenberg-type `|⟨⁅a,b⁆⟩| ≤ σ_a σ_b` relations obtained from it by dropping one term.

-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace
open ContinuousLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped selfAdjoint

namespace UnitalPositiveLinearMap

omit [PartialOrder A] [StarOrderedRing A] in
/-- A real multiple of `1` commutes with everything: the algebraic fact making `commutator`
insensitive to shifting by a constant. -/
private lemma smul_one_comm (r : ℝ) (x : A) : (r • (1 : A)) * x = x * (r • (1 : A)) := by
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- The commutator only sees fluctuations, not means: centering `a` and `b` changes nothing about
how badly they fail to commute, since scalar multiples of `1` commute with everything and so
contribute nothing to `ab - ba`. -/
lemma bracket_centered (ω : 𝓢[A]) (a b : Observable A) :
    ⁅centered ω a, centered ω b⁆ = ⁅a, b⁆ := by
  apply Subtype.ext
  simp only [selfAdjoint.coe_bracket]
  congr 1
  show (centered ω a : A) * centered ω b - (centered ω b : A) * centered ω a =
      (a : A) * b - (b : A) * a
  simp only [centered, AddSubgroup.coe_sub, selfAdjoint.val_smul, selfAdjoint.val_one, mul_sub,
    sub_mul]
  rw [smul_one_comm (ω⟨b⟩) (a : A), smul_one_comm (ω⟨a⟩) (b : A),
    smul_one_comm (ω⟨a⟩) (ω⟨b⟩ • (1 : A))]
  abel

/-- The expectation of a raw product of two fluctuations splits into a real symmetric part
(covariance) and an imaginary antisymmetric part (the commutator's expectation). This is what
turns the Cauchy–Schwarz bound below into simultaneous control on covariance and commutator. -/
lemma apply_centered_mul_centered (ω : 𝓢[A]) (a b : Observable A) :
    ω ((centered ω a : A) * centered ω b) =
      (covariance ω a b : ℂ) + Complex.I * (ω⟨⁅a, b⁆⟩ : ℂ) := by
  set z := ω ((centered ω a : A) * centered ω b) with hz
  have hstar : ω ((centered ω b : A) * centered ω a) = star z := by
    rw [hz, apply_mul_comm_eq_star]
  have hsub : ω ((centered ω a : A) * centered ω b - (centered ω b : A) * centered ω a) =
      (2 * z.im : ℝ) * Complex.I := by
    rw [map_sub, hstar, ← hz, Complex.star_def, Complex.sub_conj]
  have hcomm : (ω⟨⁅a, b⁆⟩ : ℂ) = (z.im : ℂ) := by
    rw [← bracket_centered ω a b, ← apply_observable_eq_expectation, selfAdjoint.coe_bracket,
      map_smul, hsub, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    push_cast
    ring
  rw [hcomm, show covariance ω a b = z.re from rfl, mul_comm, Complex.re_add_im]

/-! ## Cauchy–Schwarz -/

/-- The image of `x`, `y : A` under `π_ω` at the cyclic vector inner-products to `ω(x⋆y)`: the
key identity connecting `A`'s sesquilinear form `(x, y) ↦ ω(x⋆y)` to the genuine inner product on
the GNS Hilbert space `ω.GNS`, using only `gnsRep`, `gnsCyclicVector` and the defining identity
`inner_gnsCyclicVector_gnsRep_gnsCyclicVector` from `CStarAlgebra.GNS`. -/
lemma inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector (ω : 𝓢[A]) (x y : A) :
    ⟪ω.gnsRep x ω.gnsCyclicVector, ω.gnsRep y ω.gnsCyclicVector⟫_ℂ = ω (star x * y) := by
  rw [← ω.inner_gnsCyclicVector_gnsRep_gnsCyclicVector (star x * y), map_mul,
    mul_apply_eq_comp, map_star ω.gnsRep, star_eq_adjoint, adjoint_inner_right]

/-- Cauchy–Schwarz for the positive sesquilinear form induced by a state, via the genuine inner
product on the GNS Hilbert space `ω.GNS`. -/
lemma gns_cauchy_schwarz (ω : 𝓢[A]) (x y : A) :
    ‖ω (star x * y)‖ * ‖ω (star y * x)‖ ≤
      (ω (star x * x)).re * (ω (star y * y)).re := by
  have h := inner_mul_inner_self_le (𝕜 := ℂ)
    (ω.gnsRep x ω.gnsCyclicVector) (ω.gnsRep y ω.gnsCyclicVector)
  rwa [inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector,
    inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector,
    inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector,
    inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector] at h

/-- No state can correlate two fluctuations more strongly than the product of their spreads
allows — the GNS-Cauchy–Schwarz seed of every uncertainty relation below, before splitting the
left side via `apply_centered_mul_centered`. -/
lemma centered_gns_cauchy_schwarz (ω : 𝓢[A]) (a b : Observable A) :
    ‖ω ((centered ω a : A) * centered ω b)‖ *
        ‖ω ((centered ω b : A) * centered ω a)‖ ≤
      variance ω a * variance ω b := by
  rw [variance_eq_re_apply_centered_mul_self, variance_eq_re_apply_centered_mul_self]
  simpa only [(centered ω a).property.star_eq, (centered ω b).property.star_eq] using
    gns_cauchy_schwarz ω (centered ω a : A) (centered ω b : A)

/-- The squared-magnitude form of `centered_gns_cauchy_schwarz`, ready to be split via
`apply_centered_mul_centered` into `robertson_schrodinger`. -/
lemma centered_cauchy_schwarz (ω : 𝓢[A]) (a b : Observable A) :
    Complex.normSq (ω ((centered ω a : A) * centered ω b)) ≤
      variance ω a * variance ω b := by
  calc
    Complex.normSq (ω ((centered ω a : A) * centered ω b)) =
        ‖ω ((centered ω a : A) * centered ω b)‖ *
          ‖ω ((centered ω b : A) * centered ω a)‖ := by
      rw [apply_mul_comm_eq_star]
      simp [Complex.normSq_eq_norm_sq, pow_two]
    _ ≤ _ := centered_gns_cauchy_schwarz ω a b

/-! ## Uncertainty relations -/

/-- The Robertson–Schrödinger uncertainty inequality: the sharpest relation here, jointly bounding
covariance and the commutator's expectation by the product of the individual spreads. Dropping
either term below recovers the more familiar `covariance_cauchy_schwarz` / `robertson`. -/
lemma robertson_schrodinger (ω : 𝓢[A]) (a b : Observable A) :
    covariance ω a b ^ 2 + ω⟨⁅a, b⁆⟩ ^ 2 ≤
      variance ω a * variance ω b := by
  have h := centered_cauchy_schwarz ω a b
  rw [apply_centered_mul_centered, Complex.normSq_apply] at h
  simpa [pow_two] using h

/-- Two observables cannot be more correlated than the product of their uncertainties allows —
the familiar `|correlation| ≤ σ_a · σ_b`, from dropping the commutator term in
`robertson_schrodinger`. -/
lemma covariance_cauchy_schwarz (ω : 𝓢[A]) (a b : Observable A) :
    covariance ω a b ^ 2 ≤ variance ω a * variance ω b := by
  nlinarith [robertson_schrodinger ω a b, sq_nonneg (ω⟨⁅a, b⁆⟩)]

/-- Heisenberg's uncertainty relation: observables that fail to commute cannot both be measured
with arbitrary precision. For position and momentum, `⁅x, p⁆ = iℏ` gives `ΔxΔp ≥ ℏ/2`. Obtained
from `robertson_schrodinger` by dropping the covariance term. -/
lemma robertson (ω : 𝓢[A]) (a b : Observable A) :
    ω⟨⁅a, b⁆⟩ ^ 2 ≤ variance ω a * variance ω b := by
  nlinarith [robertson_schrodinger ω a b, sq_nonneg (covariance ω a b)]

end UnitalPositiveLinearMap
