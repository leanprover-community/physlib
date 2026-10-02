/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Module
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Sphere
/-!

# Configuration space of the simple pendulum

## i. Overview

A simple pendulum is a bob fixed to one end of a rigid massless rod of length `ℓ`, the other end
of which is pinned at a pivot, swinging in a vertical plane under gravity. Its position is fixed by
the angle of the rod from the downward vertical, and two angles that differ by a full turn describe
the same position. The configuration space is therefore a circle.

We record a configuration by its angle modulo `2π`, i.e. by an element of `Real.Angle`, as the
sliding pendulum does (`Physlib.ClassicalMechanics.Pendulum.SlidingPendulum`). The circle carries
the structure of a compact analytic one-dimensional manifold; we obtain it by identifying the
configuration space with Mathlib's unit circle `Circle` and pulling back its charts. The smooth
identification of the configuration space with `Circle` (the analogue of the harmonic oscillator's
`valDiffeomorph`) is deferred to a later module. The real-valued angle that is used to
write down the dynamics is a lift of the configuration along the covering map
`ℝ → ConfigurationSpace`; it is not a chart, and two lifts differing by `2π n` describe the same
configuration. Finally the position of the bob in the plane is recorded by `toSpace ℓ`, which sends
the configuration at angle `θ` to `(ℓ sin θ, -ℓ cos θ)`: the pivot is the origin and the second axis
points upwards.

## ii. Key results

- `ConfigurationSpace` : the configuration space of the planar simple pendulum.
- `ConfigurationSpace.circleHomeomorph` : its identification with the unit circle, with inverse
  `ConfigurationSpace.ofCircle` (`toCircle_ofCircle`, `ofCircle_toCircle`).
- `ConfigurationSpace.instChartedSpace`, `ConfigurationSpace.instIsManifold` : the analytic
  manifold structure, pulled back from `Circle` (`chartAt_source`, `chartAt_target`).
- `ConfigurationSpace.ofAngle` : the angular lift `ℝ → ConfigurationSpace`, periodic with period
  `2π`, continuous, surjective, analytic, and a covering map (`isCoveringMap_ofAngle`).
- `ConfigurationSpace.toSpace` : the position of the bob in `Space 2`, with
  `toSpace_ofAngle` and the rod-length constraint `toSpace_norm`; for `ℓ ≠ 0` it is a closed
  embedding (`toSpace_isClosedEmbedding`).

## iii. Table of contents

- A. The configuration space type
- B. Topology and identification with the unit circle
- C. Manifold structure
- D. The angular lift
- E. Map to physical space

## iv. References

* Landau & Lifshitz, Mechanics, 3rd ed., §5, Problems 1–3 (pendulum configurations).
  [ref: landau_mechanics]
* Mathlib, `Mathlib.Geometry.Manifold.Instances.Sphere` (the manifold structure on `Circle`).
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace ClassicalMechanics
namespace SimplePendulum

/-!

## A. The configuration space type

A configuration is the angle of the rod from the downward vertical, taken modulo a full turn.

-/

/-- The configuration space of the planar simple pendulum: the angle of the rod from the downward
  vertical, modulo `2π`. -/
structure ConfigurationSpace where
  /-- The angle of the rod from the downward vertical, modulo `2π`. -/
  angle : Real.Angle

namespace ConfigurationSpace

/-- Two configurations are equal precisely when their angles are equal. -/
@[ext]
lemma ext {p q : ConfigurationSpace} (h : p.angle = q.angle) : p = q := by
  cases p; cases q; cases h; rfl

/-!

## B. Topology and identification with the unit circle

The topology is that of `Real.Angle`; composing with Mathlib's identification of `Real.Angle`
(the additive circle of period `2π`) with the unit circle `Circle ⊆ ℂ` gives a homeomorphism
`ConfigurationSpace ≃ₜ Circle`, through which the circle's compactness and Hausdorff property
transfer.

-/

/-- The identification of the configuration space with `Real.Angle`. -/
def angleEquiv : ConfigurationSpace ≃ Real.Angle where
  toFun := angle
  invFun φ := ⟨φ⟩
  left_inv q := by cases q; rfl
  right_inv φ := rfl

/-- The topology of the configuration space, induced from `Real.Angle`. -/
instance instTopologicalSpace : TopologicalSpace ConfigurationSpace :=
  TopologicalSpace.induced angle inferInstance

/-- The identification with `Real.Angle` as a homeomorphism. -/
def angleHomeomorph : ConfigurationSpace ≃ₜ Real.Angle where
  toEquiv := angleEquiv
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

/-- The point of the unit circle `e^{iθ}` corresponding to a configuration at angle `θ`. -/
def toCircle (q : ConfigurationSpace) : Circle := q.angle.toCircle

/-- The identification of the configuration space with the unit circle. -/
def circleHomeomorph : ConfigurationSpace ≃ₜ Circle :=
  angleHomeomorph.trans AddCircle.homeomorphCircle'

-- `rfl` proves this because `Real.Angle.toCircle` and `AddCircle.homeomorphCircle'` are the same
-- lift of `Circle.exp`; should that stop holding definitionally, the fallback proof is
-- `Real.Angle.induction_on` with `Real.Angle.toCircle_coe` and
-- `AddCircle.homeomorphCircle'_apply_mk`.
/-- The identification with the unit circle is given by `ConfigurationSpace.toCircle`. -/
lemma circleHomeomorph_apply (q : ConfigurationSpace) : circleHomeomorph q = q.toCircle := rfl

/-- The configuration corresponding to a point of the unit circle. -/
def ofCircle : Circle → ConfigurationSpace := circleHomeomorph.symm

/-- The point of the unit circle of the configuration attached to a point of the unit circle is
  that point. -/
@[simp]
lemma toCircle_ofCircle (z : Circle) : (ofCircle z).toCircle = z :=
  circleHomeomorph.apply_symm_apply z

/-- The configuration attached to the point of the unit circle of a configuration is that
  configuration. -/
@[simp]
lemma ofCircle_toCircle (q : ConfigurationSpace) : ofCircle q.toCircle = q :=
  circleHomeomorph.symm_apply_apply q

/-- The configuration space is Hausdorff, being homeomorphic to the unit circle. -/
instance instT2Space : T2Space ConfigurationSpace := circleHomeomorph.symm.t2Space

/-- The configuration space is compact, being homeomorphic to the unit circle. -/
instance instCompactSpace : CompactSpace ConfigurationSpace := circleHomeomorph.symm.compactSpace

/-- The configuration space is second countable, being homeomorphic to the unit circle. -/
instance instSecondCountableTopology : SecondCountableTopology ConfigurationSpace :=
  circleHomeomorph.secondCountableTopology

/-!

## C. Manifold structure

The unit circle is an analytic one-dimensional manifold modelled on `EuclideanSpace ℝ (Fin 1)`
(Mathlib, via stereographic projection). We pull its atlas back along `circleHomeomorph`: a chart
of the configuration space is the identification with the circle followed by a chart of the circle.
Since the identification cancels in every change of charts, the changes of charts are exactly those
of the circle, hence analytic.

-/

/-- The charts of the configuration space: the identification with the unit circle followed by a
  chart of the circle. -/
instance instChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 1)) ConfigurationSpace where
  atlas := {circleHomeomorph.toOpenPartialHomeomorph.trans e |
    e ∈ atlas (EuclideanSpace ℝ (Fin 1)) Circle}
  chartAt q := circleHomeomorph.toOpenPartialHomeomorph.trans
    (chartAt (EuclideanSpace ℝ (Fin 1)) (circleHomeomorph q))
  mem_chart_source q := by simp
  chart_mem_atlas q := ⟨_, chart_mem_atlas _ _, rfl⟩

/-- The chart at a configuration is the identification with the unit circle followed by the chart
  of the circle at the corresponding point. -/
lemma chartAt_eq (q : ConfigurationSpace) :
    chartAt (EuclideanSpace ℝ (Fin 1)) q =
      circleHomeomorph.toOpenPartialHomeomorph.trans
        (chartAt (EuclideanSpace ℝ (Fin 1)) q.toCircle) := rfl

/-- The domain of the chart at a configuration is the preimage under the identification with the
  unit circle of the domain of the chart of the circle at the corresponding point. -/
lemma chartAt_source (q : ConfigurationSpace) :
    (chartAt (EuclideanSpace ℝ (Fin 1)) q).source =
      circleHomeomorph ⁻¹' (chartAt (EuclideanSpace ℝ (Fin 1)) q.toCircle).source := by
  rw [chartAt_eq, OpenPartialHomeomorph.trans_source]
  simp

/-- The codomain of the chart at a configuration is the codomain of the chart of the circle at the
  corresponding point. -/
lemma chartAt_target (q : ConfigurationSpace) :
    (chartAt (EuclideanSpace ℝ (Fin 1)) q).target =
      (chartAt (EuclideanSpace ℝ (Fin 1)) q.toCircle).target := by
  rw [chartAt_eq, OpenPartialHomeomorph.trans_target]
  simp

/-- The configuration space is an analytic manifold: every change of charts is a change of charts
  of the unit circle. -/
instance instIsManifold : IsManifold (𝓡 1) ω ConfigurationSpace where
  compatible := by
    rintro _ _ ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, rfl⟩
    -- The identification `h` with the circle is global, so `h.symm ≫ₕ h` is the identity.
    have hself : circleHomeomorph.toOpenPartialHomeomorph.symm.trans
        circleHomeomorph.toOpenPartialHomeomorph = OpenPartialHomeomorph.refl Circle := by
      rw [← Homeomorph.symm_toOpenPartialHomeomorph, ← Homeomorph.trans_toOpenPartialHomeomorph,
        Homeomorph.symm_trans_self, Homeomorph.refl_toOpenPartialHomeomorph]
    -- Hence it cancels in the change of charts, which is therefore that of the circle.
    have hcancel : (circleHomeomorph.toOpenPartialHomeomorph.trans e₁).symm.trans
        (circleHomeomorph.toOpenPartialHomeomorph.trans e₂) = e₁.symm.trans e₂ := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
        ← OpenPartialHomeomorph.trans_assoc circleHomeomorph.toOpenPartialHomeomorph.symm,
        hself, OpenPartialHomeomorph.refl_trans]
    rw [hcancel]
    exact HasGroupoid.compatible he₁ he₂

/-!

## D. The angular lift

`ofAngle θ` is the configuration at angle `θ` from the downward vertical. It is the quotient map
`ℝ → ℝ / 2πℤ`, a covering map of the circle: it is continuous, surjective and `2π`-periodic, and
two angles give the same configuration exactly when they differ by a whole number of turns. The
dynamics of the pendulum are written for a real-valued lift of the angle; this section is what
makes different lifts describe the same configuration. In the charts pulled back from the circle
is `Circle.exp`, so it is analytic.

-/

/-- The configuration at angle `θ` (measured from the downward vertical). -/
def ofAngle (θ : ℝ) : ConfigurationSpace := ⟨θ⟩

/-- The angle of the configuration at angle `θ` is `θ` modulo `2π`. -/
@[simp]
lemma ofAngle_angle (θ : ℝ) : (ofAngle θ).angle = θ := rfl

/-- Adding a full turn to the angle leaves the configuration unchanged. -/
lemma ofAngle_add_two_pi (θ : ℝ) : ofAngle (θ + 2 * Real.pi) = ofAngle θ := by
  ext
  simp [Real.Angle.coe_add, Real.Angle.coe_two_pi]

/-- The angular lift is periodic with period `2π`. -/
lemma ofAngle_periodic : Function.Periodic ofAngle (2 * Real.pi) := ofAngle_add_two_pi

/-- Two angles describe the same configuration exactly when they differ by a whole number of
  turns. -/
lemma ofAngle_eq_iff (θ₁ θ₂ : ℝ) :
    ofAngle θ₁ = ofAngle θ₂ ↔ ∃ n : ℤ, θ₂ = θ₁ + n * (2 * Real.pi) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ :=
      Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (congrArg ConfigurationSpace.angle h)
    exact ⟨-k, by push_cast; linarith⟩
  · rintro ⟨n, rfl⟩
    exact ConfigurationSpace.ext
      (Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr ⟨-n, by push_cast; ring⟩)

/-- Every configuration is the configuration at some real angle: the lift is surjective. -/
lemma ofAngle_surjective : Function.Surjective ofAngle := by
  rintro ⟨φ⟩
  induction φ using Real.Angle.induction_on
  next θ => exact ⟨θ, rfl⟩

/-- The angular lift is continuous. -/
@[fun_prop]
lemma continuous_ofAngle : Continuous ofAngle :=
  continuous_induced_rng.mpr Real.Angle.continuous_coe

/-- The angular lift is a covering map. -/
lemma isCoveringMap_ofAngle : IsCoveringMap ofAngle := by
  have h : IsCoveringMap ((↑) : ℝ → Real.Angle) := AddCircle.isCoveringMap_coe (2 * Real.pi)
  have he : ofAngle = ⇑angleHomeomorph.symm ∘ ((↑) : ℝ → Real.Angle) := rfl
  rw [he]
  exact h.homeomorph_comp angleHomeomorph.symm

/-- The configuration at angle `θ` corresponds to the point `e^{iθ}` of the unit circle. -/
@[simp]
lemma toCircle_ofAngle (θ : ℝ) : (ofAngle θ).toCircle = Circle.exp θ := Real.Angle.toCircle_coe θ

/-- The configuration of a point `e^{iθ}` of the unit circle is `ofAngle θ`. -/
@[simp]
lemma ofCircle_circleExp (θ : ℝ) : ofCircle (Circle.exp θ) = ofAngle θ := by
  rw [← toCircle_ofAngle, ofCircle_toCircle]

/-- The angular lift is analytic: read in the charts pulled back from the circle it is
  `Circle.exp`. -/
lemma contMDiff_ofAngle : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ω ofAngle := by
  rw [contMDiff_iff]
  refine ⟨continuous_ofAngle, fun x y => ?_⟩
  have h := (contMDiff_iff.mp (contMDiff_circleExp (m := ω))).2 x y.toCircle
  -- Two goals remain: the map read in the charts, and the domain on which it is read.
  convert h using 2
  · rfl
  · ext θ
    simp [chartAt_eq, circleHomeomorph_apply, toCircle_ofAngle]

/-- The cosine of the angle of a configuration. -/
def cos (q : ConfigurationSpace) : ℝ := Real.Angle.cos q.angle

/-- The sine of the angle of a configuration. -/
def sin (q : ConfigurationSpace) : ℝ := Real.Angle.sin q.angle

/-- The cosine of a configuration is the cosine of its angle. -/
lemma cos_angle (q : ConfigurationSpace) : q.cos = Real.Angle.cos q.angle := rfl

/-- The sine of a configuration is the sine of its angle. -/
lemma sin_angle (q : ConfigurationSpace) : q.sin = Real.Angle.sin q.angle := rfl

/-- The cosine of the configuration at angle `θ` is `cos θ`. -/
@[simp]
lemma cos_ofAngle (θ : ℝ) : (ofAngle θ).cos = Real.cos θ := Real.Angle.cos_coe θ

/-- The sine of the configuration at angle `θ` is `sin θ`. -/
@[simp]
lemma sin_ofAngle (θ : ℝ) : (ofAngle θ).sin = Real.sin θ := Real.Angle.sin_coe θ

/-- The Pythagorean identity for the angle of a configuration. -/
lemma cos_sq_add_sin_sq (q : ConfigurationSpace) : q.cos ^ 2 + q.sin ^ 2 = 1 :=
  Real.Angle.cos_sq_add_sin_sq q.angle

/-- The cosine of the angle depends continuously on the configuration. -/
@[fun_prop]
lemma continuous_cos : Continuous (cos : ConfigurationSpace → ℝ) :=
  Real.Angle.continuous_cos.comp continuous_induced_dom

/-- The sine of the angle depends continuously on the configuration. -/
@[fun_prop]
lemma continuous_sin : Continuous (sin : ConfigurationSpace → ℝ) :=
  Real.Angle.continuous_sin.comp continuous_induced_dom

/-!

## E. Map to physical space

The pivot is the origin of the plane `Space 2`, the first coordinate is horizontal and the second
points upwards. A rod of length `ℓ` at angle `θ` from the downward vertical places the bob at
`(ℓ sin θ, -ℓ cos θ)`; at `θ = 0` the bob hangs straight down at `(0, -ℓ)`. The bob lies on the
circle of radius `|ℓ|` about the pivot — the rod-length constraint — and for `ℓ ≠ 0` the map is
injective, so the configuration is determined by the position.

-/

/-- The position of the bob in the plane, for a rod of length `ℓ`. `ℓ` is not assumed positive; the
  bob is at distance `|ℓ|` from the pivot. -/
def toSpace (ℓ : ℝ) (q : ConfigurationSpace) : Space 2 := ⟨![ℓ * q.sin, -ℓ * q.cos]⟩

/-- The horizontal coordinate of the bob, `ℓ * q.sin`. -/
@[simp]
lemma toSpace_apply_zero (ℓ : ℝ) (q : ConfigurationSpace) :
    toSpace ℓ q 0 = ℓ * q.sin := rfl

/-- The vertical coordinate of the bob, `-(ℓ * q.cos)`. -/
@[simp]
lemma toSpace_apply_one (ℓ : ℝ) (q : ConfigurationSpace) :
    toSpace ℓ q 1 = -(ℓ * q.cos) := neg_mul ℓ q.cos

/-- The position of the bob for the configuration at angle `θ`. -/
@[simp]
lemma toSpace_ofAngle (ℓ θ : ℝ) :
    toSpace ℓ (ofAngle θ) = ⟨![ℓ * Real.sin θ, -ℓ * Real.cos θ]⟩ := by
  simp [toSpace]

/-- The rod-length constraint: the bob is at distance `|ℓ|` from the pivot. -/
@[simp]
lemma toSpace_norm (ℓ : ℝ) (q : ConfigurationSpace) : ‖toSpace ℓ q‖ = |ℓ| := by
  have hq : (ℓ * q.sin) ^ 2 + (-(ℓ * q.cos)) ^ 2 = ℓ ^ 2 := by
    linear_combination ℓ ^ 2 * cos_sq_add_sin_sq q
  rw [Space.norm_eq, Fin.sum_univ_two, toSpace_apply_zero, toSpace_apply_one, hq,
    Real.sqrt_sq_eq_abs]

/-- The position of the bob depends continuously on the configuration. -/
@[fun_prop]
lemma continuous_toSpace (ℓ : ℝ) : Continuous (toSpace ℓ) := by
  refine Space.mk_continuous.comp (continuous_pi fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

/-- For a rod of nonzero length the configuration is determined by the position of the bob. -/
lemma toSpace_injective {ℓ : ℝ} (hℓ : ℓ ≠ 0) : Function.Injective (toSpace ℓ) := by
  -- Equality of angles is detected by their cosine and sine.
  have key : ∀ θ ψ : Real.Angle, θ.cos = ψ.cos → θ.sin = ψ.sin → θ = ψ := by
    intro θ ψ
    induction θ using Real.Angle.induction_on
    induction ψ using Real.Angle.induction_on
    simpa using Real.Angle.cos_sin_inj
  intro q₁ q₂ h
  have h0 : ℓ * q₁.sin = ℓ * q₂.sin := congrArg (fun p : Space 2 => p 0) h
  have h1 : -ℓ * q₁.cos = -ℓ * q₂.cos := congrArg (fun p : Space 2 => p 1) h
  exact ConfigurationSpace.ext
    (key _ _ (mul_left_cancel₀ (neg_ne_zero.mpr hℓ) h1) (mul_left_cancel₀ hℓ h0))

/-- For `ℓ ≠ 0` the position map is a closed embedding of the configuration circle. -/
lemma toSpace_isClosedEmbedding {ℓ : ℝ} (hℓ : ℓ ≠ 0) : Topology.IsClosedEmbedding (toSpace ℓ) :=
  (continuous_toSpace ℓ).isClosedEmbedding (toSpace_injective hℓ)

end ConfigurationSpace
end SimplePendulum
end ClassicalMechanics

end
