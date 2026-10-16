# Gauge theory

A general gauge-theory API would be built around a structure group, a gauge field valued in its
Lie algebra, the curvature of that field, the gauge-covariant derivative acting on matter
fields, and the gauge transformations under which the curvature transforms covariantly and the
action is invariant.

This is a tracking map for issue #859. The library has no general, non-abelian gauge-theory
framework. What it has are two disjoint concrete pieces. The first is the abelian case,
realized as gauge transformations of the electromagnetic potential together with the gauge
invariance of the field strength. The second is the Standard Model gauge group as a group
object with its central discrete subgroup, carrying no connection, curvature or
covariant-derivative theory. Everything the general theory needs is therefore still planned.

## Built on

- Electromagnetic potential — `Physlib/Electromagnetism/Kinematics/EMPotential.lean`
- Field strength — `Physlib/Electromagnetism/Kinematics/FieldStrength.lean`
- Standard Model gauge group — `Physlib/Particles/StandardModel/Basic.lean`

## Requirements

The Standard Model gauge group is SU(3) × SU(2) × U(1), with its projections and central
discrete subgroup. [1] In the abelian theory, the electromagnetic potential is a
spacetime-valued Lorentz-vector gauge field, and its field strength is built from that
potential. [2][3] A gauge transformation shifts the potential by the gradient of a scalar; the
pure-gauge potential is obtained by shifting zero. [4] These transformations leave the field
strength invariant; in particular, pure-gauge configurations have vanishing curvature, a
result that depends on the metric contraction used to define the field strength. [5][6] Gauge
transformations compose: the trivial shift acts as identity and successive shifts add. [7] They
are compatible with the Lorentz-group action. [8]

The general non-abelian theory remains planned. It will allow an arbitrary Lie group as the
structure group and define a gauge field valued in its Lie algebra. [planned] It will also define
the gauge-covariant derivative on matter fields and its transformation law, along with the
Yang–Mills curvature and its covariant transformation. [planned] The Yang–Mills action and its
field equations, parallel transport and holonomy, and a formulation of gauge fields as
connections on principal bundles are also planned. [planned]

## Further reading

- https://en.wikipedia.org/wiki/Mathematical_descriptions_of_the_electromagnetic_field#Gauge_freedom
- https://en.wikipedia.org/wiki/Gauge_theory

## Lean declarations

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
