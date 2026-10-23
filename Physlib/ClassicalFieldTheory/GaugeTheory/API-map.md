# Gauge theory

## Abstract

A gauge theory is a type of field theory in which the Lagrangian is invariant under certain local transformations. These local transformations are dependent on the spacetime point, and a formally
defined in terms of a principal bundle with the gauge group as its fiber. The matter fields carry
representations of the gauge group, and formally live in associated vector bundles. The gauge
field is a connection on the principal bundle. Common examples include electromagnetism, where the gauge group is `U(1)`, and the Standard Model of particle physics, where the gauge group
is `SU(3) × SU(2) × U(1)`.

## Content (Alpha)

### Geometric formulation

Geometrically a gauge theory is described in terms of a principal bundle with the gauge group as its fiber, and the gauge field is a connection on this principal bundle. [TODO]

### Local formulation

Despite the geometric formulation being global, in practice gauge theories are often described locally. This local formulation is what is commonly used in physics, particularly in the context of electromagnetism and the Standard Model. Here one is much less reliant on certain choices one
has to make regarding for example the regularity of the fields associated with the principal bundle.

We first introduce a general concept called *local gauge data*, which abstractly encapsulates
all the information needed to describe gauge transformations and gauge fields at a
single spacetime point.

#### Local gauge data

If one only cares about local gauge transformations, one can ask what data is needed at a point x.
Let G be the gauge group and 𝔤 its Lie algebra. A local Lagrangian sees a gauge transformation only
through its action on the fields and finitely many of their derivatives at x, and so only through
the Taylor series of the gauge transformation at x. If every smooth function is an allowed gauge
transformation, Borel's theorem shows that every Taylor series compatible with G arises, convergent
or not. These Taylor series, the jets at x, form a group G_J, and their infinitesimal counterparts a
Lie algebra 𝔤_J over ℝ.

So at x, a gauge transformation is replaced by its jet U ∈ G_J, and an infinitesimal gauge
transformation by a jet a ∈ 𝔤_J. The data needed at x is whatever enters the transformation laws. A
gauge field A_μ is Lie algebra valued, and under U it transforms as A_μ ↦ Ad_U A_μ + θ_μ(U). Here
Ad_U is the adjoint action, U A_μ U⁻¹ for a matrix group, and θ_μ(U) = i (∂_μ U) U⁻¹ is the
Maurer–Cartan form, the inhomogeneous term that makes A_μ a gauge field rather than a matter field.
A Lagrangian also involves derivatives of the gauge field, as in the field strength
F_μν = ∂_μ A_ν − ∂_ν A_μ + ⁅A_μ, A_ν⁆ with ⁅A, B⁆ = i (AB − BA), so one needs the spacetime
derivatives ∂_μ of Lie algebra jets, together with multiplication by a coordinate x_μ to build jets
with prescribed derivatives. Finally, a jet can be evaluated at x, giving U(x) ∈ G and a(x) ∈ 𝔤, and
a global gauge transformation g ∈ G, or c ∈ 𝔤, gives a constant jet. We define *local gauge data* to
be exactly this information: G, 𝔤, G_J, 𝔤_J and these operations, subject to the rules that make the
transformation laws consistent. Among them are the Leibniz rules
∂_μ ⁅a, b⁆ = ⁅∂_μ a, b⁆ + ⁅a, ∂_μ b⁆ and ∂_μ (x_ν a) = x_ν ∂_μ a + δ_μν a; the cocycle law
θ_μ(UV) = θ_μ(U) + Ad_U θ_μ(V), which says that transforming A_μ by V and then by U is the same as
transforming by UV; and ∂_μ θ_ν(U) − ∂_ν θ_μ(U) + ⁅θ_μ(U), θ_ν(U)⁆ = 0, which says that a pure-gauge
field has vanishing field strength. [9]

Every g ∈ G is the value at x of its constant jet, so evaluation G_J → G is surjective and the
inclusion of constants G → G_J is injective; the same holds for 𝔤_J → 𝔤 and 𝔤 → 𝔤_J. [10] Applied to
constant jets, the rules for G_J and 𝔤_J show that Ad_g is a Lie algebra automorphism of 𝔤 for every
g ∈ G, and that ∂_μ commutes with Ad_g. [11]

For a multiset s of directions, the iterated derivative ∂_s applies ∂_μ once for each μ in s. It
satisfies ∂_(s + t) = ∂_s ∂_t and the iterated Leibniz rule ∂_s ⁅a, b⁆ = Σ ⁅∂_s₁ a, ∂_s₂ b⁆, the sum
running over the ways of splitting s as s₁ + s₂. If s is non-empty then ∂_s c = 0 for every constant
c ∈ 𝔤, and ∂_s commutes with Ad_g for g ∈ G. [12] The value (∂_s (x_μ a))(x) is the number of times
μ occurs in s, multiplied by (∂_(s − μ) a)(x). [13]

A morphism of local gauge data consists of maps G → G', 𝔤 → 𝔤', G_J → G'_J and 𝔤_J → 𝔤'_J compatible
with all of the operations above. It intertwines Ad on 𝔤 and 𝔤', and commutes with ∂_s. [14]
Morphisms have identities and compose. [15] A homomorphism of Lie groups induces a morphism of local
gauge data. [TODO]

#### The abelian theory

In electromagnetism the gauge field is the electromagnetic potential {1}, a Lorentz-vector-valued
field on spacetime, and its field strength is built from that potential. [2][3] A gauge
transformation shifts the potential by the gradient of a scalar {2}, and the pure-gauge potential is
the shift of zero. [4] Gauge transformations leave the field strength invariant. [5] In particular a
pure-gauge potential has vanishing field strength, and this relies on raising the index of the
gradient with the Minkowski metric: the bare gradient of a scalar can have nonzero field
strength. [6] Gauge transformations compose: the trivial shift is the identity and successive shifts
add. [7] They commute with the action of the Lorentz group. [8]

#### The Standard Model gauge group

The Standard Model gauge group {3} is SU(3) × SU(2) × U(1), with its projections onto the three
factors and a central discrete subgroup of sixth roots of unity. [1]

#### The non-abelian theory

A general gauge theory {4} admits an arbitrary Lie group as its structure group. [TODO] Its gauge
field takes values in the Lie algebra of that group. [TODO] Matter fields carry a gauge-covariant
derivative with a definite transformation law. [TODO] The gauge field has a Yang–Mills
curvature. [TODO] That curvature transforms covariantly under gauge transformations. [TODO]
The Yang–Mills action yields the Yang–Mills field equations. [TODO] A gauge field determines
parallel transport along paths and holonomy around loops. [TODO] Gauge fields are connections on
principal bundles. [TODO] Progress on this API is tracked in a GitHub issue {5}.

## Lean References

1. Physlib/Particles/StandardModel/Basic.lean — `GaugeGroupI`, `GaugeGroupI.toSU3`,
   `GaugeGroupI.toSU2`, `GaugeGroupI.toU1`, `gaugeGroupℤ₆SubGroup`
2. Physlib/Electromagnetism/Kinematics/EMPotential.lean — `ElectromagneticPotential`
3. Physlib/Electromagnetism/Kinematics/FieldStrength.lean — `toFieldStrength`
4. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `ofGradient`,
   `gaugeTransform`, `gaugeTransform_apply`
5. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `toFieldStrength_gaugeTransform`,
   `toFieldStrength_eval_gaugeTransform`
6. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `toFieldStrength_ofGradient`,
   `toFieldStrength_eval_bareGradient_inl_inr`, `toFieldStrength_bareGradient_ne_zero`
7. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `gaugeTransform_zero`,
   `gaugeTransform_gaugeTransform`, `ofGradient_add`, `ofGradient_zero`
8. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `ofGradient_equivariant`,
   `gaugeTransform_equivariant`
9. Physlib/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Basic.lean — `LocalGaugeData`
10. Physlib/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Basic.lean — `LocalGaugeData.eval_surjective`,
   `LocalGaugeData.ofConstant_injective`, `LocalGaugeData.evalLie_surjective`,
   `LocalGaugeData.ofConstantLie_injective`
11. Physlib/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Basic.lean — `LocalGaugeData.adjoint_bracket`,
   `LocalGaugeData.deriv_adjointJ_ofConstant`
12. Physlib/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Basic.lean — `LocalGaugeData.iteratedDeriv`,
   `LocalGaugeData.iteratedDeriv_zero`, `LocalGaugeData.iteratedDeriv_cons`,
   `LocalGaugeData.iteratedDeriv_add`, `LocalGaugeData.iteratedDeriv_singleton`,
   `LocalGaugeData.iteratedDeriv_bracket`, `LocalGaugeData.iteratedDeriv_ofConstantLie_of_ne_zero`,
   `LocalGaugeData.iteratedDeriv_adjointJ_ofConstant`
13. Physlib/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Basic.lean — `LocalGaugeData.evalLie_iteratedDeriv_mulCoord`
14. Physlib/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Basic.lean — `LocalGaugeData.Hom`,
   `LocalGaugeData.Hom.lie_adjoint`, `LocalGaugeData.Hom.lieJ_iteratedDeriv`
15. Physlib/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Basic.lean — `LocalGaugeData.Hom.id`, `LocalGaugeData.Hom.comp`

## References

1. Electromagnetic Potential API map — Physlib/Electromagnetism/Kinematics/API-map.md
2. Wikipedia, Mathematical descriptions of the electromagnetic field, Gauge freedom,
   https://en.wikipedia.org/wiki/Mathematical_descriptions_of_the_electromagnetic_field#Gauge_freedom
3. Standard Model gauge group API map — Physlib/Particles/StandardModel/API-map.md
4. Wikipedia, Gauge theory, https://en.wikipedia.org/wiki/Gauge_theory
5. Physlib GitHub issue #859, https://github.com/leanprover-community/physlib/issues/859
