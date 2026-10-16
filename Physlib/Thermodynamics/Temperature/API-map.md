# Temperature

Temperature here is measured from absolute zero and is taken to be nonnegative: no scale used
here places a state below absolute zero, which excludes the negative absolute temperatures a
system with a bounded energy spectrum can carry. A choice of scale is a choice of how large one
degree is, and nothing more, so two such choices differ by a positive ratio, and kelvin is the
scale from which the others here are obtained by rescaling.

In statistical mechanics the quantity that actually appears is not the temperature itself but
its reciprocal, weighted by the Boltzmann constant: the inverse temperature that multiplies an
energy in a Boltzmann factor. On positive temperatures the correspondence is a bijection onto
the positive inverse temperatures and reverses order, so a hot system is one with a small
inverse temperature; the boundary value zero is paired with itself, which is a convention of
the underlying nonnegative reals rather than a physical statement. The limit of large inverse
temperature is the one recorded here: sending the inverse temperature to infinity drives the
temperature to absolute zero, the regime in which a system settles into its lowest energy
states.

Thermodynamic quantities are differentiated with respect to one or the other of these
variables, so the change of variable between them is smooth at positive temperature, and a
derivative in one variable determines the derivative in the other.

## Built on

- Boltzmann constant — `Physlib/StatisticalMechanics/BoltzmannConstant.lean`

## Requirements

The key data structure is defined: an absolute temperature, in an arbitrary scale that puts
absolute zero at zero, with its coercions, its topology, its zero and its extensionality. [1]

A temperature has an inverse temperature, defined through the Boltzmann constant, and a
temperature can be recovered from one. [2]

Passing to the inverse temperature and back is the identity, in both directions. [3]

A strictly positive temperature has a strictly positive inverse temperature. [4]

The temperature is a continuous function of the inverse temperature at positive inverse
temperature, and its real coordinate is differentiable on the positive reals. [5]

In the limit of large inverse temperature the temperature is eventually positive and converges
to absolute zero from above. [6]

A temperature can be built from a nonnegative real, or from a real together with a proof that
it is nonnegative, with the equations defining both. [7]

The derivative of the inverse temperature with respect to the temperature is available at
positive temperature, with the chain rule that converts a derivative in one variable into a
derivative in the other. [8]

The second key data structure is defined: a choice of temperature scale, carrying a positive
scale factor. [9][10]

Two temperature units have a ratio, a nonnegative real, which is positive and behaves
reflexively, symmetrically and multiplicatively along a chain of units. [11]

A temperature unit can be rescaled by a positive real, with the ratios this induces and its
composition law. [12]

Kelvin is the reference temperature unit, and the other units here are obtained from it by
rescaling. [13]

The temperature manifold, diffeomorphic to the nonnegative reals and of which a temperature
unit is a translationally invariant metric, will be defined. [planned]

A temperature value will be convertible between two temperature units. [planned]

Scales whose zero is offset from absolute zero — degrees Celsius and degrees Fahrenheit as
ordinarily used, as against the absolute Fahrenheit-sized degree already present — will be
defined, together with their conversion to absolute scales. [planned]

## Further reading

- L. D. Landau & E. M. Lifshitz, Statistical Physics, Part 1 (§9 temperature, §31 the Gibbs distribution).
- N. F. Ramsey, Thermodynamics and statistical mechanics at negative absolute temperatures, Physical Review 103 (1956), 20-28.

## Lean declarations

1. Physlib/Thermodynamics/Temperature/Basic.lean — `Temperature`, `val`, `toReal`, `ext`,
   `Coe Temperature ℝ≥0`, `Coe Temperature ℝ`, `TopologicalSpace Temperature`,
   `Zero Temperature`
2. Physlib/Thermodynamics/Temperature/Basic.lean — `β`, `β_toReal`, `ofβ`, `ofβ_eq`,
   `ofβ_toReal`
3. Physlib/Thermodynamics/Temperature/Basic.lean — `β_ofβ`, `ofβ_β`
4. Physlib/Thermodynamics/Temperature/Basic.lean — `beta_pos`
5. Physlib/Thermodynamics/Temperature/Basic.lean — `ofβ_continuousOn`, `ofβ_differentiableOn`
6. Physlib/Thermodynamics/Temperature/Basic.lean — `eventually_pos_ofβ`,
   `tendsto_toReal_ofβ_atTop`, `tendsto_ofβ_atTop`
7. Physlib/Thermodynamics/Temperature/Basic.lean — `ofNNReal`, `ofNNReal_val`,
   `coe_ofNNReal_coe`, `coe_ofNNReal_real`, `ofRealNonneg`, `ofRealNonneg_val`
8. Physlib/Thermodynamics/Temperature/Basic.lean — `betaFromReal`, `beta_fun_T_formula`,
   `beta_fun_T_eq_on_Ioi`, `deriv_beta_wrt_T`, `chain_rule_T_beta`
9. Physlib/Thermodynamics/Temperature/TemperatureUnits.lean — `TemperatureUnit`
10. Physlib/Units/PositiveRealUnit.lean — `PositiveRealUnitCore`,
   `PositiveRealUnitCore.val_ne_zero`, `PositiveRealUnitCore.pos`,
   `PositiveRealUnitCore.instInhabited`
11. Physlib/Units/PositiveRealUnit.lean — `PositiveRealUnitCore.instHDiv`,
   `PositiveRealUnitCore.div_eq_val`, `PositiveRealUnitCore.div_ne_zero`,
   `PositiveRealUnitCore.div_pos`, `PositiveRealUnitCore.div_self`,
   `PositiveRealUnitCore.div_symm`, `PositiveRealUnitCore.div_mul_div`,
   `PositiveRealUnitCore.div_mul_div_coe`
12. Physlib/Units/PositiveRealUnit.lean — `PositiveRealUnitCore.scale`,
   `PositiveRealUnitCore.scale_div_self`, `PositiveRealUnitCore.self_div_scale`,
   `PositiveRealUnitCore.scale_one`, `PositiveRealUnitCore.scale_div_scale`,
   `PositiveRealUnitCore.scale_scale`
13. Physlib/Thermodynamics/Temperature/TemperatureUnits.lean — `kelvin`, `nanokelvin`,
   `microkelvin`, `millikelvin`, `absoluteFahrenheit`
