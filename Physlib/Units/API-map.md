# Units

Every physical quantity has a dimension: a rational power of each base dimension, recording how
the numerical value of the quantity changes when the unit of each base quantity is changed. The
LTMCT set has five base dimensions: length, time, mass, charge and temperature, whose initials
give the name; they are written L𝓭, T𝓭, M𝓭, C𝓭 and Θ𝓭. Dimensions multiply by adding exponents
and invert by negating them, so they form a commutative group with a rational power operation.
The International System of Quantities (ISQ) uses a different set of seven base quantities, in
which electric charge is derived as current times time; both sets are available and are related
by a faithful inclusion and a reduction. LTMCT is the set over which the typed unit layer and
the named derived quantities are built, with its own SI choice of units; the ISQ set carries
the coherent SI unit choice over seven base quantities.

A unit system fixes one concrete unit for each base quantity. Changing from one system to
another multiplies a quantity of dimension d by a positive factor: the product, over the base
quantities, of the ratio of the two units raised to the exponent that d assigns to that base
quantity. That factor is multiplicative in the dimension, equals one when the two systems agree,
and composes along a chain, so the value of a quantity in one system determines its value in
every other. The statement is proved once for a general set of base dimensions and specialises
to the LTMCT set and to the ISQ set without being restated.

A value carrying a dimension inherits the additive, order and scalar structure of its underlying
type, while products and quotients add and subtract the exponents. Area, speed, energy, pressure
and momentum appear as named dimensions with concrete units. A statement is dimensionally
correct when its truth does not depend on the unit system in which it is written, which is the
formal content of dimensional analysis; the API expresses that condition for values, functions
and propositions, and proves that the derivative and the integral of a dimensionally correct
quantity are again dimensionally correct.

## Built on

- Time — `Physlib/SpaceAndTime/Time`
- Space — `Physlib/SpaceAndTime/Space`
- Mass — `Physlib/ClassicalMechanics/Mass`
- Charge — `Physlib/Electromagnetism/Charge`
- Temperature — `Physlib/Thermodynamics/Temperature`

## Requirements

A dimension assigns a rational exponent to each base dimension, with extensionality. [1]

Dimensions form a commutative group with a rational power operation. [2]

The exponents of a product, of the unit, of an inverse, of a quotient and of a natural power are
computed. [3]

The base vector at each base dimension is defined, with its exponents. [4]

A change of base-dimension set is a monoid homomorphism of dimensions, either an injective
embedding of one set into another or a surjective reduction of a richer set onto a coarser one,
so a relabelling that does not preserve products, inverses and rational powers is not
expressible. [5]

The LTMCT set of five base dimensions is defined with the exponent projection of each. [6]

A dimension is constructed from its five exponents. [7]

Each of the five exponents is computed under products, units, inverses, quotients and natural
powers. [8]

The named generators L𝓭, T𝓭, M𝓭, C𝓭 and Θ𝓭 are defined and identified with the corresponding
base vectors of the generic algebra. [9]

The seven base quantities of the International System of Quantities are defined. [10]

Electric charge is derived as current times time, with its exponents in current, time and mass.
[11]

Amount of substance and luminous intensity are independent of the other base quantities. [12]

A faithful embedding carries the LTMCT base dimensions into the ISQ set, sending the charge
generator to the derived ISQ charge. [13]

A reduction reads electric current as charge per time and forgets amount of substance and
luminous intensity. [14]

The reduction is a retraction of the embedding, and the composite in the other order is not the
identity. [15]

A unit choice fixes one unit for each of the five LTMCT base quantities, with the SI choice of
metre, second, kilogram, coulomb and kelvin. [16]

A second unit choice rescales each SI base unit by a distinct prime, which serves to refute
dimensional correctness. [17]

The factor by which a quantity of a given dimension rescales under a change of unit choice is a
monoid homomorphism from dimensions to the positive reals. [18]

The rescaling factor is one on the trivial dimension and on a unit system paired with itself.
[19]

The rescaling factor is strictly positive and nonzero, composes along a chain of three unit
choices, and inverts when the two choices are swapped. [20]

Scaling by the rescaling factor is injective. [21]

A type may be assigned a dimension, strengthened to a type on which the positive reals act. [22]

A function from unit choices to a dimension-carrying type is required to rescale by the correct
factor under every change of unit. [23]

The subtype of functions satisfying that condition carries a scalar action. [24]

For each fixed unit choice, a value of a dimension-carrying type is equivalent to a quantity
given in every unit system. [25]

A magnitude layer assigns a positive real to each base dimension, with nonzero ratios. [26]

The scaling homomorphism on the magnitude layer is the product over the base dimensions of the
unit ratio raised to the corresponding exponent, and is transitive. [27]

A catalogue names a type of admissible units and a magnitude for each base dimension, and a unit
system chooses exactly one unit per base dimension. [28]

A unit system projects onto the magnitude layer. [29]

The bespoke five-field unit choice is equivalent to a unit system over the LTMCT base
dimensions, and its hand-written scaling law is the generic product specialised to that set.
[30][31]

Units of electric current, of amount of substance and of luminous intensity are defined, each a
positive magnitude with its quotient by another unit of the same kind. [32][33]

The coherent SI units ampere, mole and candela are named. [34]

A typed unit choice over the seven ISQ base quantities is defined, with the coherent SI choice
of metre, kilogram, second, ampere, kelvin, mole and candela. [35]

The scaling factor over the ISQ base quantities is obtained from the generic product rather than
restated. [36]

The SI unit choice over the five LTMCT base quantities will be computable. A note in the source
records what this needs: the axioms defining the base units have to be replaced. [planned]

The unit types for electric current, amount of substance and luminous intensity will carry the
same rescaling operation as the other five, so that a decimal multiple such as the milliampere
can be named. [37][38]

A unit-dependent type comes with the transformation of its elements induced by a change of unit,
subject to composition along a chain of unit choices and triviality on an unchanged choice. [39]

Strengthenings require that transformation to commute with a scalar action, to be linear, or to
be linear and continuous. [40]

The transformation is packaged as an equivalence, a linear map, a linear equivalence, a
continuous linear map and a continuous linear equivalence. [41]

Instances are given for the unit choices themselves and for every type carrying a dimension.
[42]

Instances for function types act on the argument, on the value, or on both. [43]

Dimensional correctness is the condition that a quantity or a statement be unchanged by a change
of unit system, with its unfolding for functions acting on the argument, on the value and on
both. [44]

The dimension-preserving product of two dimension-carrying types scales as the product of their
dimensions. [45]

The subset of a unit-dependent type consisting of the elements that scale according to a
prescribed dimension itself carries that dimension. [46]

Values of an underlying type may be tagged with a dimension over any set of base dimensions.
[47]

The tagged type inherits zero, addition, negation and subtraction, each computed on the
underlying value. [48]

The tagged type inherits the order relations and the action of the positive reals. [49]

Multiplication and division of real-valued tagged quantities multiply the underlying values and
multiply the dimensions. [50]

Over the LTMCT base dimensions the tagged type carries its dimension and its transformation
under a change of unit is scalar multiplication by the scaling factor. [51]

A tagged quantity of trivial dimension is unchanged by a change of unit. [52]

A cast moves a tagged quantity between two tags whose dimensions are equal, with the equality
discharged automatically. [53]

The dimension-tagged type will inherit further structure from its underlying type:
multiplicative and other non-additive algebraic structure, the rest of the order structure, and
topological structure. [planned]

Area has dimension length squared, with the square metre, square foot, square mile, are, hectare
and acre, their values in SI units, and the identity of one acre with 43560 square feet. [54]

Speed has dimension length over time, with the metre per second, mile per hour, kilometre per
hour, knot and the speed of light, their values in SI units, and the conversions between them.
[55]

Energy has dimension mass times length squared over time squared, with the joule, electronvolt,
calorie and kilowatt hour. [56]

Pressure has dimension mass over length over time squared, with the pascal, millimetre of
mercury, bar, standard atmosphere, torr and pound per square inch. [57]

Momentum has dimension mass times length over time and takes values in d spatial components, the
three-momentum rather than the four-momentum. [58]

The mass of a particle, and its velocity in d spatial dimensions, will be named
dimension-carrying quantities in the manner of momentum. The mass and velocity modules announce
them in their documentation but do not yet declare them. [planned]

The derivative of a dimensionally correct differentiable function is dimensionally correct, with
the explicit rescaling of the derivative at a rescaled point. [59]

The equation giving the derivative in a fixed direction as a quantity of the dimension of the
target divided by the dimension of the source is dimensionally correct. [60]

A measure on a type carrying a dimension is unit-dependent, and the integral of a function whose
dimension is that of its values divided by the dimension of the measure has the dimension of the
values. [61]

A worked example converts a length of 400 metres to miles. [62]

The relations E = m c^2 and F = m a are stated over dimension-tagged reals and shown to be
dimensionally correct. [63]

A speed as distance over time, an expression of mixed dimension in mass, temperature, current,
length and time, and the cosine of an angular frequency times a time are each shown to be
dimensionally correct. [64]

The relation E = m c is shown not to be dimensionally correct by exhibiting a change of unit
that breaks it. [65]

The version of E = m c^2 written with the speed of light in an explicit unit system is proved in
SI units and then transported to every unit system. [66]

The equality of a length with a speed times a time holds propositionally rather than
definitionally, so the two tagged types are bridged by a cast, and the same comparison is
repeated over a set of base dimensions with no physical unit system, namely bits and symbols.
[67]

At a fixed numerical unit representation, dimension-tagged values inherit real-module and
normed-space structures without replacing the existing additive operations or nonnegative-real
action. Explicit coordinate equivalences transport functions and their Frechet derivatives.
[68][69]

The harmonic oscillator example carries the mass and spring constant with their physical
dimensions. Its potential-energy expression is assembled from dimension-tagged quantities,
agrees in coordinates with the existing numerical oscillator, and reuses the generic derivative
transport API. [70]

## Further reading

- International Bureau of Weights and Measures (BIPM), The International System of Units (SI Brochure), 9th edition (2019), Chapter 1 (quantities and units) and Chapter 2 (the defining constants and the seven base units)
- ISO/IEC 80000-1:2009, Quantities and units, Part 1: General, Clauses 3 to 6 (quantities, systems of quantities, dimensions, and systems of units)
- JCGM 200:2012, International vocabulary of metrology (VIM, 3rd edition), Clause 1 (base quantity, derived quantity, quantity dimension, base unit, coherent system of units)
- G. I. Barenblatt, Scaling, Self-similarity, and Intermediate Asymptotics, Cambridge University Press (1996), Chapter 1, Sections 1.1 and 1.2 (dimensions, systems of units, and the change of a quantity under a change of unit)
- Lean Zulip, #Physlib > physical units: https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/topic/physical.20units

## Lean declarations

1. Physlib/Units/Dimension.lean — `Dimension`, `Dimension.ext`
2. Physlib/Units/Dimension.lean — `CommGroup (Dimension B)`, `Dimension.qpow_exponent`
3. Physlib/Units/Dimension.lean — `Dimension.mul_exponent`, `Dimension.one_exponent`,
   `Dimension.inv_exponent`, `Dimension.div_exponent`, `Dimension.npow_exponent`
4. Physlib/Units/Dimension.lean — `Dimension.single`, `Dimension.single_exponent`
5. Physlib/Units/Dimension.lean — `Dimension.extend`, `Dimension.extend_exponent_apply`,
   `Dimension.extendHom`, `Dimension.Embedding`, `Dimension.Projection`,
   `Dimension.Embedding.ofBasis`
6. Physlib/Units/LTMCTDimensionBase.lean — `LTMCTDimensionBase`, `Dimension.length`,
   `Dimension.time`, `Dimension.mass`, `Dimension.charge`, `Dimension.temperature`
7. Physlib/Units/LTMCTDimensionBase.lean — `Dimension.ofLTMCTDimensionBase`
8. Physlib/Units/LTMCTDimensionBase.lean — `Dimension.length_mul`, `Dimension.one_time`,
   `Dimension.inv_mass`, `Dimension.div_charge`, `Dimension.npow_temperature`
9. Physlib/Units/LTMCTDimensionBase.lean — `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`,
   `Dimension.C𝓭`, `Dimension.Θ𝓭`, `Dimension.L𝓭_eq_single`, `Dimension.T𝓭_eq_single`,
   `Dimension.M𝓭_eq_single`, `Dimension.C𝓭_eq_single`, `Dimension.Θ𝓭_eq_single`
10. Physlib/Units/ISQDimensionBase.lean — `ISQDimensionBase`, `ISQDimensionBase.card_eq_seven`
11. Physlib/Units/ISQDimensionBase.lean — `ISQDimensionBase.charge`,
   `ISQDimensionBase.charge_exponent_current`, `ISQDimensionBase.charge_exponent_time`,
   `ISQDimensionBase.charge_exponent_mass`
12. Physlib/Units/ISQDimensionBase.lean — `ISQDimensionBase.single_amount_ne_one`,
   `ISQDimensionBase.single_luminousIntensity_ne_one`
13. Physlib/Units/ISQBridge.lean — `Dimension.toISQFun`, `Dimension.toISQHom`,
   `Dimension.toISQHom_apply`, `Dimension.toISQHom_injective`, `Dimension.ltmctToISQ`,
   `Dimension.toISQHom_C𝓭`
14. Physlib/Units/ISQBridge.lean — `Dimension.fromISQFun`, `Dimension.fromISQHom`,
   `Dimension.fromISQHom_apply`, `Dimension.fromISQHom_surjective`, `Dimension.isqToLTMCT`
15. Physlib/Units/ISQBridge.lean — `Dimension.fromISQHom_comp_toISQHom`,
   `Dimension.isqToLTMCT_comp_ltmctToISQ`
16. Physlib/Units/Basic.lean — `LTMCTUnitChoices`, `LTMCTUnitChoices.SI`,
   `LTMCTUnitChoices.SI_length`, `LTMCTUnitChoices.SI_time`, `LTMCTUnitChoices.SI_mass`,
   `LTMCTUnitChoices.SI_charge`, `LTMCTUnitChoices.SI_temperature`
17. Physlib/Units/Basic.lean — `LTMCTUnitChoices.SIPrimed`,
   `LTMCTUnitChoices.dimScale_SI_SIPrimed`, `LTMCTUnitChoices.dimScale_SIPrimed_SI`
18. Physlib/Units/Basic.lean — `LTMCTUnitChoices.dimScale`, `LTMCTUnitChoices.dimScale_apply`
19. Physlib/Units/Basic.lean — `LTMCTUnitChoices.dimScale_self`, `LTMCTUnitChoices.dimScale_one`
20. Physlib/Units/Basic.lean — `LTMCTUnitChoices.dimScale_ne_zero`,
   `LTMCTUnitChoices.dimScale_pos`, `LTMCTUnitChoices.dimScale_transitive`,
   `LTMCTUnitChoices.dimScale_symm`, `LTMCTUnitChoices.dimScale_mul_symm`,
   `LTMCTUnitChoices.dimScale_coe_mul_symm`, `LTMCTUnitChoices.dimScale_of_inv_eq_swap`
21. Physlib/Units/Basic.lean — `LTMCTUnitChoices.smul_dimScale_injective`
22. Physlib/Units/Basic.lean — `HasDim`, `HasDim.d`, `dim`, `CarriesDimension`
23. Physlib/Units/Basic.lean — `HasDimension`, `hasDimension_iff`
24. Physlib/Units/Basic.lean — `Dimensionful`, `Dimensionful.ext`, `Dimensionful.smul_apply`
25. Physlib/Units/Basic.lean — `CarriesDimension.toDimensionful`,
   `CarriesDimension.toDimensionful_apply_apply`
26. Physlib/Units/ParametricUnits.lean — `UnitScale`, `UnitScale.ratio_ne_zero`
27. Physlib/Units/ParametricUnits.lean — `UnitScale.dimScale`, `UnitScale.dimScale_self`,
   `UnitScale.dimScale_one`, `UnitScale.dimScale_transitive`
28. Physlib/Units/UnitSystem.lean — `UnitMagnitudeCatalog`, `UnitSystem`, `UnitSystem.ext`
29. Physlib/Units/UnitSystem.lean — `UnitSystem.toScale`, `UnitSystem.toScale_scale`
30. Physlib/Units/ParametricUnits.lean — `LTMCTUnitChoices.toScale`
31. Physlib/Units/UnitSystem.lean — `LTMCTUnitChoices.equivUnitSystem`,
   `LTMCTUnitChoices.toScale_equivUnitSystem`, `prod_univ_LTMCTDimensionBase`,
   `LTMCTUnitChoices.dimScale_eq_toScale_dimScale`
32. Physlib/Units/SIUnitChoices.lean — `CurrentUnit`, `AmountUnit`, `LuminousIntensityUnit`
33. Physlib/Units/PositiveRealUnit.lean — `PositiveRealUnitCore`, `PositiveRealUnitCore.pos`,
   `PositiveRealUnitCore.instHDiv`, `PositiveRealUnitCore.ratio`,
   `PositiveRealUnitCore.div_eq_val`
34. Physlib/Units/SIUnitChoices.lean — `CurrentUnit.amperes`, `AmountUnit.moles`,
   `LuminousIntensityUnit.candelas`
35. Physlib/Units/SIUnitChoices.lean — `SIUnitChoices`, `SIUnitChoices.SI`
36. Physlib/Units/SIUnitChoices.lean — `prod_univ_ISQDimensionBase`, `SIUnitChoices.dimScale`,
   `SIUnitChoices.dimScale_self`
37. Physlib/Units/SIUnitChoices.lean — `CurrentUnit.milliamperes`
38. Physlib/Units/PositiveRealUnit.lean — `PositiveRealUnitCore.scale`,
   `PositiveRealUnitCore.scale_div_self`, `PositiveRealUnitCore.self_div_scale`,
   `PositiveRealUnitCore.scale_one`, `PositiveRealUnitCore.scale_div_scale`,
   `PositiveRealUnitCore.scale_scale`
39. Physlib/Units/UnitDependent.lean — `UnitDependent`
40. Physlib/Units/UnitDependent.lean — `MulUnitDependent`, `LinearUnitDependent`,
   `ContinuousLinearUnitDependent`
41. Physlib/Units/UnitDependent.lean — `UnitDependent.scaleUnit_symm_apply`,
   `UnitDependent.scaleUnit_injective`, `UnitDependent.scaleUnitEquiv`,
   `LinearUnitDependent.scaleUnitLinear`, `LinearUnitDependent.scaleUnitLinearEquiv`,
   `ContinuousLinearUnitDependent.scaleUnitContLinear`,
   `ContinuousLinearUnitDependent.scaleUnitContLinearEquiv`
42. Physlib/Units/UnitDependent.lean — `LTMCTUnitChoices.scaleUnit_apply_fst`,
   `LTMCTUnitChoices.dimScale_scaleUnit`, `Dimensionful.of_scaleUnit`, `HasDim.scaleUnit_apply`
43. Physlib/Units/UnitDependent.lean — `UnitDependent.scaleUnit_apply_fun_right`,
   `UnitDependent.scaleUnit_apply_fun_left`, `UnitDependent.scaleUnit_apply_fun`,
   `instUnitDependentTwoSided`, `instUnitDependentTwoSidedMul`,
   `instContinuousLinearUnitDependentMap`
44. Physlib/Units/UnitDependent.lean — `IsDimensionallyCorrect`, `isDimensionallyCorrect_iff`,
   `isDimensionallyCorrect_fun_iff`, `isDimensionallyCorrect_fun_left`,
   `isDimensionallyCorrect_fun_right`
45. Physlib/Units/UnitDependent.lean — `DMul`, `DMul.hMul_scaleUnit`
46. Physlib/Units/UnitDependent.lean — `DimSet`, `DimSet.mem_iff`, `scaleUnit_dimSet_val`
47. Physlib/Units/WithDim/Basic.lean — `WithDim`, `WithDim.ext`, `WithDim.dim_apply`
48. Physlib/Units/WithDim/Basic.lean — `WithDim.val_zero`, `WithDim.val_add`, `WithDim.val_neg`,
   `WithDim.val_sub`
49. Physlib/Units/WithDim/Basic.lean — `WithDim.le_def`, `WithDim.lt_def`, `WithDim.smul_val`
50. Physlib/Units/WithDim/Basic.lean — `WithDim.withDim_hMul_val`, `WithDim.val_mul_eq_mul`,
   `WithDim.val_pow_two_eq_mul`, `WithDim.val_div_val`, `WithDim.div_scaleUnit`
51. Physlib/Units/WithDim/Basic.lean — `WithDim.scaleUnit_val`,
   `WithDim.scaleUnit_val_eq_scaleUnit_val`, `WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq`
52. Physlib/Units/WithDim/Basic.lean — `WithDim.scaleUnit_dim_eq_zero`
53. Physlib/Units/WithDim/Basic.lean — `WithDim.cast`, `WithDim.cast_refl`,
   `WithDim.cast_scaleUnit`
54. Physlib/Units/WithDim/Area.lean — `DimArea`, `DimArea.squareMeter`, `DimArea.squareFoot`,
   `DimArea.squareMile`, `DimArea.are`, `DimArea.hectare`, `DimArea.acre`,
   `DimArea.squareFoot_in_SI`, `DimArea.squareMile_in_SI`, `DimArea.acre_in_SI`,
   `DimArea.acre_eq_mul_squareFeet`
55. Physlib/Units/WithDim/Speed.lean — `DimSpeed`, `DimSpeed.oneMeterPerSecond`,
   `DimSpeed.oneMilePerHour`, `DimSpeed.oneKilometerPerHour`, `DimSpeed.oneKnot`,
   `DimSpeed.speedOfLight`, `DimSpeed.oneMilePerHour_in_SI`, `DimSpeed.speedOfLight_in_SI`,
   `DimSpeed.oneKnot_eq_mul_oneKilometerPerHour`, `DimSpeed.oneKilometerPerHour_eq_mul_oneKnot`,
   `DimSpeed.oneMeterPerSecond_eq_mul_oneMilePerHour`
56. Physlib/Units/WithDim/Energy.lean — `DimEnergy`, `DimEnergy.joule`,
   `DimEnergy.electronVolt`, `DimEnergy.calorie`, `DimEnergy.kilowattHour`
57. Physlib/Units/WithDim/Pressure.lean — `DimPressure`, `DimPressure.pascal`,
   `DimPressure.millimeterOfMercury`, `DimPressure.bar`, `DimPressure.standardAtmosphere`,
   `DimPressure.torr`, `DimPressure.psi`
58. Physlib/Units/WithDim/Momentum.lean — `Momentum`
59. Physlib/Units/FDeriv.lean — `fderiv_apply_scaleUnit`, `fderiv_isDimensionallyCorrect`
60. Physlib/Units/FDeriv.lean — `fderiv_dimension_const_direction`
61. Physlib/Units/Integral.lean — `scaleUnit_measure`, `integral_isDimensionallyCorrect`
62. Physlib/Units/Examples.lean — `UnitExamples.meters400`
63. Physlib/Units/Examples.lean — `UnitExamples.EnergyMassWithDim`,
   `UnitExamples.energyMassWithDim_isDimensionallyCorrect`, `UnitExamples.NewtonsSecondWithDim`,
   `UnitExamples.newtonsSecondWithDim_isDimensionallyCorrect`
64. Physlib/Units/Examples.lean — `UnitExamples.SpeedEq`,
   `UnitExamples.speedEq_isDimensionallyCorrect`, `UnitExamples.OddDimensions`,
   `UnitExamples.oddDimensions_isDimensionallyCorrect`, `UnitExamples.CosDim`,
   `UnitExamples.cosDim_isDimensionallyCorrect`
65. Physlib/Units/Examples.lean — `UnitExamples.EnergyMassWithDimNot`,
   `UnitExamples.energyMassWithDimNot_not_isDimensionallyCorrect`
66. Physlib/Units/Examples.lean — `UnitExamples.EnergyMass`,
   `UnitExamples.energyMass_isDimensionallyCorrect`, `UnitExamples.example1_energyMass`,
   `UnitExamples.example2_energyMass`
67. Physlib/Units/ParametricDimensionExamples.lean — `ParametricDimensionExamples.Info`,
   `ParametricDimensionExamples.bitDim`, `ParametricDimensionExamples.symbolDim`
68. Physlib/Units/WithDim/Basic.lean — `instModuleReal`, `real_smul_val`
69. Physlib/Units/WithDim/Analysis.lean — `toValueAddEquiv`, `toValueLinearEquiv`,
   `instNormedAddCommGroup`, `instNormedSpace`, `toValueLinearIsometryEquiv`, `transport`,
   `transportLinearMap`, `hasFDerivAt_transport`
70. Physlib/ClassicalMechanics/HarmonicOscillator/WithDim.lean — `HarmonicOscillatorWithDim`,
   `HarmonicOscillatorWithDim.toHarmonicOscillator`, `HarmonicOscillatorWithDim.positionNormSq`,
   `HarmonicOscillatorWithDim.potentialEnergy`, `HarmonicOscillatorWithDim.potentialEnergy_val`,
   `HarmonicOscillatorWithDim.potentialEnergy_eq_transport`,
   `HarmonicOscillatorWithDim.hasFDerivAt_potentialEnergy`,
   `HarmonicOscillatorWithDim.continuous_potentialEnergy`
