# Units

## Abstract (Alpha)

Every physical quantity has a dimension: a rational power of each base dimension, recording how
the numerical value of the quantity changes when the unit of each base quantity is changed.
Dimensions multiply by adding exponents and invert by negating them, so they form a commutative
group with a rational power operation. Two sets of base dimensions are in use: the LTMCT set of
length, time, mass, charge and temperature, over which the typed unit layer and the named
derived quantities are built, and the seven base quantities of the International System of
Quantities (ISQ), in which charge is derived as current times time; the two are related by a
faithful inclusion and a reduction. A unit system fixes one unit for each base quantity, and
changing unit system multiplies a quantity of dimension d by a positive factor that is
multiplicative in d, equal to one when the two systems agree and composes along a chain, so the
value of a quantity in one system determines its value in every other. A value carrying a
dimension inherits the additive, order and scalar structure of its underlying type, and a
statement is dimensionally correct when its truth does not depend on the unit system in which it
is written, which is the formal content of dimensional analysis.

## Content (Alpha)

### Dimensions

A dimension assigns a rational exponent to each base dimension, and two dimensions with the same
exponents are equal. [1] Dimensions form a commutative group with a rational power operation.
[2] The exponents of a product, of the unit, of an inverse, of a quotient and of a natural power
follow from the exponents of the factors. [3] Each base dimension has its base vector, whose
exponents are one at that base dimension and zero elsewhere. [4] The vocabulary of base
quantity, derived quantity and quantity dimension is that of ISO/IEC 80000-1 {1} and of the
International vocabulary of metrology {2}. The design of this API is discussed on the Lean
Zulip {3}.

A change of base-dimension set is a monoid homomorphism of dimensions, either an injective
embedding of one set into another or a surjective reduction of a richer set onto a coarser one,
so a relabelling that does not preserve products, inverses and rational powers is not
expressible. [5]

### The LTMCT and ISQ base sets

The LTMCT set has five base dimensions, length, time, mass, charge and temperature, whose
initials give the name, each with its exponent projection. [6] A dimension over this set is
built from its five exponents. [7] Each of the five exponents of a product, a unit, an inverse,
a quotient and a natural power follows from those of the factors. [8] The generators L𝓭, T𝓭,
M𝓭, C𝓭 and Θ𝓭 are the base vectors of the five base dimensions. [9]

The International System of Quantities has seven base quantities. [10] In it electric charge is
derived as current times time, with exponent one in current and in time and zero in mass. [11]
Amount of substance and luminous intensity are base dimensions of their own, distinct from the
trivial dimension. [12]

A faithful embedding carries the LTMCT base dimensions into the ISQ set, sending the charge
generator to the derived ISQ charge. [13] A reduction runs the other way, reading electric
current as charge per time and forgetting amount of substance and luminous intensity. [14] The
reduction is a retraction of the embedding, and the composite in the other order is not the
identity. [15]

### Unit choices and the change of unit

A unit choice fixes one unit for each of the five LTMCT base quantities, with the SI choice of
metre, second, kilogram, coulomb and kelvin. [16] The SI unit choice over the five LTMCT base
quantities is computable, its base units being given without axioms. [TODO] A second unit
choice rescales each SI base unit by a distinct prime, which serves to refute dimensional
correctness. [17]

The factor by which a quantity of a given dimension rescales under a change of unit choice is a
monoid homomorphism from dimensions to the positive reals. [18] It is one on the trivial
dimension and on a unit system paired with itself. [19] It is strictly positive and nonzero,
composes along a chain of three unit choices, and inverts when the two choices are swapped. [20]
Scaling by it is injective. [21] The factor is also available as a strictly positive real, that
is as a unit of the non-negative reals, and it is by this that dimension-carrying quantities are
scaled: no change of unit scales by zero, so the positive reals suffice, and taking them lets a
type whose elements are strictly positive carry a dimension at all. [71] This is the classical
law for the change of a quantity under a change of unit {4}.

### Unit systems over a general base set

The change-of-unit law holds once for a general set of base dimensions and specialises to the
LTMCT set and to the ISQ set without being restated. A magnitude layer assigns a positive real
to each base dimension, with nonzero ratios. [26] On it the scaling homomorphism is the product
over the base dimensions of the unit ratio raised to the corresponding exponent, and it is
transitive. [27] A catalogue names a type of admissible units and a magnitude for each base
dimension, and a unit system chooses exactly one unit per base dimension. [28] A unit system
projects onto the magnitude layer. [29] The five-field LTMCT unit choice is equivalent to a unit
system over the LTMCT base dimensions, and its scaling law is the generic product specialised to
that set. [30][31]

Units of electric current, of amount of substance and of luminous intensity are each a positive
magnitude, with a quotient by another unit of the same kind. [32][33] The coherent SI units are
the ampere, the mole and the candela. [34] These unit types carry the same rescaling operation
as the other five, so that a decimal multiple such as the milliampere exists. [37][38] A unit
choice over the seven ISQ base quantities fixes one unit for each, with the coherent SI choice
of metre, kilogram, second, ampere, kelvin, mole and candela. [35] Its scaling factor is the
generic product over the ISQ base quantities. [36] The SI base units are those of the SI
Brochure {5}.

### Dimension-carrying and unit-dependent types

A type may carry a dimension, and the stronger notion is a type carrying a dimension on which
the positive reals act. [22] A function from unit choices to a dimension-carrying type has a
dimension when it rescales by the factor of that dimension under every change of unit. [23] The
functions with this property form a subtype carrying a scalar action. [24] For each fixed unit
choice, a value of a dimension-carrying type is equivalent to a quantity given in every unit
system. [25]

A unit-dependent type comes with a transformation of its elements under a change of unit, which
composes along a chain of unit choices and is trivial on an unchanged choice. [39] Stronger
versions require that transformation to commute with a scalar action, to be linear, or to be
linear and continuous. [40] The transformation is then an equivalence, a linear map, a linear
equivalence, a continuous linear map or a continuous linear equivalence. [41] The unit choices
themselves and every dimension-carrying type are unit-dependent. [42] Carrying a dimension is
enough for that on its own, whereas compatibility of the transformation with a non-negative
scalar is meaningful only when such a scalar acts, and so is asked for separately. [72] Function
types are unit-dependent, with the transformation acting on the argument, on the value, or on
both. [43]

A quantity or a statement is dimensionally correct when it is unchanged by a change of unit
system; for functions this unfolds into conditions acting on the argument, on the value and on
both. [44] The dimension-preserving product of two dimension-carrying types scales as the
product of their dimensions. [45] The elements of a unit-dependent type that scale according to
a prescribed dimension form a subset which itself carries that dimension. [46]

### Dimension-tagged values

Values of an underlying type may be tagged with a dimension over any set of base dimensions.
[47] The tagged type inherits zero, addition, negation and subtraction, each computed on the
underlying value. [48] It inherits the order relations and the action of the positive reals.
[49] Multiplying or dividing real-valued tagged quantities multiplies or divides the underlying
values and combines the dimensions in the same way. [50] Over the LTMCT base dimensions a tagged
type carries its dimension, and its transformation under a change of unit is scalar
multiplication by the scaling factor. [51] A tagged quantity of trivial dimension is unchanged
by a change of unit. [52] A cast moves a tagged quantity between two tags whose dimensions are
equal, with the equality discharged automatically. [53] A quantity whose elements are strictly
positive is regarded as a dimension-tagged real by recording its magnitude, with the dimension
read off its type so that the two cannot drift apart, and tagging it commutes both with a
rescaling and with a change of unit. [73]

At a fixed numerical unit representation, tagged values form a real module without replacing the
existing additive operations or the action of the nonnegative reals. [68] They also form a
normed space, and explicit coordinate equivalences transport functions and their Fréchet
derivatives. [69] The tagged type inherits further structure from its underlying type:
multiplicative and other non-additive algebraic structure, the rest of the order structure, and
topological structure. [TODO]

### Named quantities

The base quantities themselves are the subject of the APIs for time {6}, space {7} and
temperature {8}, and of the mass and charge modules.
Area has dimension length squared, with the square metre, square foot, square mile, are, hectare
and acre, their values in SI units, and one acre equal to 43560 square feet. [54] Speed has
dimension length over time, with the metre per second, mile per hour, kilometre per hour and
knot, their values in SI units, and the conversions between them. [55] Energy
has dimension mass times length squared over time squared, with the joule, electronvolt, calorie
and kilowatt hour. [56] Pressure has dimension mass over length over time squared, with the
pascal, millimetre of mercury, bar, standard atmosphere, torr and pound per square inch. [57]
Momentum has dimension mass times length over time and takes values in d spatial components:
it is the three-momentum rather than the four-momentum. [58] The mass of a particle is a named
dimension-carrying quantity in the manner of momentum, and so is its velocity in d spatial
dimensions. [TODO]

### Physical constants

A physical constant is not a unit: it is a definite physical quantity, fixed once and for all,
and the number recording it is determined by the unit system in which it is read. It is
therefore recorded as a quantity given in every unit system rather than placed among the units
of the quantity it measures. The speed of light is such a constant. Its type consists of
strictly positive reals, which is why it needs the scaling by a strictly positive factor, and it
carries the dimension of a length over a time; its value in our world is exactly 299792458
metres per second. [74][75] Newton's constant, Planck's constant and the Boltzmann constant are
recorded in the same way. [TODO]

### Calculus and dimensional correctness

The derivative of a dimensionally correct differentiable function is dimensionally correct, and
the derivative at a rescaled point is the explicitly rescaled derivative. [59] The equation
giving the derivative in a fixed direction as a quantity of the dimension of the target divided
by the dimension of the source is dimensionally correct. [60] A measure on a dimension-carrying
type is unit-dependent, and the integral of a function whose dimension is that of its values
divided by the dimension of the measure has the dimension of the values. [61]

### Examples

A length of 400 metres converts to miles. [62] The relations E = m c^2 and F = m a, stated over
dimension-tagged reals, are dimensionally correct. [63] A speed as distance over time, an
expression of mixed dimension in mass, temperature, current, length and time, and the cosine of
an angular frequency times a time are each dimensionally correct. [64] The relation E = m c is
not dimensionally correct: a change of unit breaks it. [65] The version of E = m c^2 written with
the speed of light in an explicit unit system holds in SI units and, by transport, in every unit
system. [66]

The equality of a length with a speed times a time holds propositionally rather than
definitionally, so the two tagged types are bridged by a cast, and the same comparison works
over a set of base dimensions with no physical unit system, namely bits and symbols. [67]

The harmonic oscillator carries its mass and spring constant with their physical dimensions.
Its potential energy is assembled from dimension-tagged quantities, agrees in coordinates with
the numerical oscillator, and has its derivative from the generic transport of derivatives.
[70]

## Lean References

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
   `PositiveRealUnitCore.scale_scale`, `PositiveRealUnitCore.unitsSMul`,
   `PositiveRealUnitCore.instMulActionUnitsNNReal`,
   `PositiveRealUnitCore.units_smul_eq_scale`, `PositiveRealUnitCore.val_units_smul`
39. Physlib/Units/UnitDependent.lean — `UnitDependent`
40. Physlib/Units/UnitDependent.lean — `MulUnitDependent`, `LinearUnitDependent`,
   `ContinuousLinearUnitDependent`
41. Physlib/Units/UnitDependent.lean — `UnitDependent.scaleUnit_symm_apply`,
   `UnitDependent.scaleUnit_injective`, `UnitDependent.scaleUnitEquiv`,
   `LinearUnitDependent.scaleUnitLinear`, `LinearUnitDependent.scaleUnitLinearEquiv`,
   `ContinuousLinearUnitDependent.scaleUnitContLinear`,
   `ContinuousLinearUnitDependent.scaleUnitContLinearEquiv`
42. Physlib/Units/UnitDependent.lean — `LTMCTUnitChoices.scaleUnit_apply_fst`,
   `LTMCTUnitChoices.dimScale_scaleUnit`, `Dimensionful.of_scaleUnit_units`,
   `HasDim.scaleUnit_apply`
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
   `DimSpeed.oneMilePerHour_in_SI`,
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
71. Physlib/Units/Basic.lean — `LTMCTUnitChoices.dimScaleUnits`,
   `LTMCTUnitChoices.dimScaleUnits_coe`, `LTMCTUnitChoices.dimScaleUnits_transitive`,
   `LTMCTUnitChoices.dimScaleUnits_self`, `LTMCTUnitChoices.dimScaleUnits_mul_dim`,
   `LTMCTUnitChoices.dimScaleUnits_smul`,
   `CarriesDimension.toDimensionful_apply_apply_units`, `Dimensionful.smul_apply_units`
72. Physlib/Units/UnitDependent.lean — `HasDim.scaleUnit_apply_units`,
   `LTMCTUnitChoices.dimScaleUnits_scaleUnit`
73. Physlib/Units/WithDim/Basic.lean — `WithDim.smul_val_units`,
   `WithDim.ofPositiveRealUnit`, `WithDim.ofPositiveRealUnit_val`,
   `WithDim.ofPositiveRealUnit_units_smul`, `WithDim.ofPositiveRealUnit_of_scaleUnit`
74. Physlib/Relativity/SpeedOfLight.lean — `SpeedOfLight`,
   `SpeedOfLight.instPositiveRealUnitCore`, `SpeedOfLight.positiveRealUnitCore_val`
75. Physlib/Units/Constants.lean — `HasDim SpeedOfLight`, `speedOfLight`,
   `speedOfLight_in_SI`

## References

1. ISO/IEC 80000-1:2009, *Quantities and units, Part 1: General*, Clauses 3 to 6 (quantities,
   systems of quantities, dimensions, and systems of units).
2. JCGM 200:2012, *International vocabulary of metrology* (VIM, 3rd edition), Clause 1 (base
   quantity, derived quantity, quantity dimension, base unit, coherent system of units).
3. Lean Zulip, #Physlib > physical units,
   https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/topic/physical.20units
4. G. I. Barenblatt, *Scaling, Self-similarity, and Intermediate Asymptotics*, Cambridge
   University Press (1996), Chapter 1, Sections 1.1 and 1.2 (dimensions, systems of units, and
   the change of a quantity under a change of unit).
5. International Bureau of Weights and Measures (BIPM), *The International System of Units (SI
   Brochure)*, 9th edition (2019), Chapter 1 (quantities and units) and Chapter 2 (the defining
   constants and the seven base units).
6. Time API map — Physlib/SpaceAndTime/Time/API-map.md
7. Space API map — Physlib/SpaceAndTime/Space/API-map.md
8. Temperature API map — Physlib/Thermodynamics/Temperature/API-map.md
