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

### Base dimensions

In physics there are certain choices that have to be made, which nothing in the theory fixes. For
example, to measure lengths one must choose a scale on space, and to measure times a scale on time,
that is, a translation-invariant metric on each. The base dimensions correspond to those choices,
one for each independent choice, and every other dimension is derived from them. The vocabulary of
base quantity, derived quantity and quantity dimension is that of ISO/IEC 80000-1 {1} and of the
International vocabulary of metrology {2}. A set of base dimensions is then simply a list of
labels, one for each independent choice, and any such list can be used. [1] Different collections
of choices give different sets of base dimensions, and two are in use. The LTMCT set has five base
dimensions, corresponding to choices for length, time, mass, charge and temperature, whose initials
give the name. [2] The International System of Quantities (ISQ) has seven base quantities: length, mass,
time, electric current, thermodynamic temperature, amount of substance and luminous intensity. [3]

### Dimensions

A dimension assigns a rational exponent to each base dimension, and two dimensions with the same
exponents are equal. [4] Dimensions form a commutative group with a rational power operation. [5]
The exponents of a product, of the unit, of an inverse, of a quotient and of a natural power follow
from the exponents of the factors. [6] Each base dimension has its base vector, whose exponents are
one at that base dimension and zero elsewhere. [7] The design of this API is discussed on the Lean
Zulip {3}.

A dimension over the LTMCT set has an exponent projection for each of its five base dimensions. [8]
It is built from its five exponents. [9] Each of the five exponents of a product, a unit, an
inverse, a quotient and a natural power follows from those of the factors. [10] The generators L𝓭,
T𝓭, M𝓭, C𝓭 and Θ𝓭 are the base vectors of the five base dimensions. [11]

Over the ISQ set electric charge is a derived dimension, current times time, with exponent one in
current and in time and zero in mass. [12] Amount of substance and luminous intensity are base
dimensions of their own, distinct from the trivial dimension. [13]

A change of base-dimension set is a monoid homomorphism of dimensions, either an injective embedding
of one set into another or a surjective reduction of a richer set onto a coarser one, so a
relabelling that does not preserve products, inverses and rational powers is not expressible. [14] A
faithful embedding carries the LTMCT dimensions into the ISQ dimensions, sending the charge
generator to the derived ISQ charge. [15] A reduction runs the other way, reading electric current
as charge per time and forgetting amount of substance and luminous intensity. [16] The reduction is
a retraction of the embedding, and the composite in the other order is not the identity. [17]

### Unit choices

Each unit, such as a unit of length, is a positive magnitude, with a quotient by another unit of the
same kind and a rescaling by a positive real, so that decimal multiples exist. [18][19] A catalogue
names, for each base dimension, a type of admissible units and the magnitude of each, and a unit
system chooses exactly one unit per base dimension. [20] Forgetting the unit types, a unit system
projects onto a magnitude layer, which assigns a positive real to each base dimension, with nonzero
ratios. [21][22] Between two unit systems a quantity of dimension d rescales by the product over the
base dimensions of the unit ratio raised to the exponent of d; this factor is a monoid homomorphism
from dimensions to the positive reals, is one when the two systems agree, and composes along a
chain. [23] This is the classical law for the change of a quantity under a change of unit {4}.

The LTMCT unit choice fixes one unit for each of the five LTMCT base dimensions, with the SI choice
of metre, second, kilogram, coulomb and kelvin. [24] The SI unit choice is computable, its base
units being given without axioms. [TODO] Its change-of-unit factor is a monoid homomorphism from
dimensions to the positive reals. [25] The LTMCT unit choice is equivalent to a unit system over the
LTMCT set, and its factor is the generic product specialised to that set. [26][27] The factor is one
on the trivial dimension and on a unit choice paired with itself. [28] It is strictly positive,
composes along a chain of three unit choices, and inverts when the two choices are swapped. [29]
Scaling by it is injective. [30] A second unit choice rescales each SI base unit by a distinct
prime, which serves to refute dimensional correctness. [31]

Units of electric current, of amount of substance and of luminous intensity are positive magnitudes.
[32] The coherent SI units are the ampere, the mole and the candela. [33] Decimal multiples such as
the milliampere exist. [34] The ISQ unit choice fixes one unit for each of the seven ISQ base
quantities, with the coherent SI choice of metre, kilogram, second, ampere, kelvin, mole and
candela. [35] Its change-of-unit factor is the generic product over the ISQ base quantities. [36]
The SI base units are those of the SI Brochure {5}.

Dimension-carrying and unit-dependent types, described below, are defined over a unit system for any
set of base dimensions, including the ISQ unit choice. [TODO]

### Dimensionful quantities

A type may carry a dimension, and the stronger notion is a type carrying a dimension on which the
positive reals act. [37] A function from LTMCT unit choices to a dimension-carrying type has a
dimension when it rescales by the factor of that dimension under every change of unit. [38] The
functions with this property form a subtype carrying a scalar action. [39] For each fixed unit
choice, a value of a dimension-carrying type is equivalent to a quantity given in every unit system.
[40]

### Unit-dependent types

A unit-dependent type comes with a transformation of its elements under a change of unit, which
composes along a chain of unit choices and is trivial on an unchanged choice. [41] Stronger versions
require that transformation to commute with a scalar action, to be linear, or to be linear and
continuous. [42] The transformation is then an equivalence, a linear map, a linear equivalence, a
continuous linear map or a continuous linear equivalence. [43] The unit choices themselves and every
dimension-carrying type are unit-dependent. [44] Function types are unit-dependent, with the
transformation acting on the argument, on the value, or on both. [45]

A quantity or a statement is dimensionally correct when it is unchanged by a change of unit system;
for functions this unfolds into conditions acting on the argument, on the value and on both. [46]
The dimension-preserving product of two dimension-carrying types scales as the product of their
dimensions. [47] The elements of a unit-dependent type that scale according to a prescribed
dimension form a subset which itself carries that dimension. [48]

### Dimension-tagged values

Values of an underlying type may be tagged with a dimension over any set of base dimensions. [49]
The tagged type inherits zero, addition, negation and subtraction, each computed on the underlying
value. [50] It inherits the order relations and the action of the positive reals. [51] Multiplying
or dividing real-valued tagged quantities multiplies or divides the underlying values and combines
the dimensions in the same way. [52] Over the LTMCT base dimensions a tagged type carries its
dimension, and its transformation under a change of unit is scalar multiplication by the scaling
factor. [53] A tagged quantity of trivial dimension is unchanged by a change of unit. [54] A cast
moves a tagged quantity between two tags whose dimensions are equal, with the equality discharged
automatically. [55]

At a fixed numerical unit representation, tagged values form a real module without replacing the
existing additive operations or the action of the nonnegative reals. [56] They also form a normed
space, and explicit coordinate equivalences transport functions and their Fréchet derivatives. [57]
The tagged type inherits further structure from its underlying type: multiplicative and other
non-additive algebraic structure, the rest of the order structure, and topological structure. [TODO]

### Named quantities

The base quantities themselves are the subject of the APIs for time {6}, space {7} and temperature
{8}, and of the mass and charge modules. Area has dimension length squared, with the square metre,
square foot, square mile, are, hectare and acre, their values in SI units, and one acre equal to
43560 square feet. [58] Speed has dimension length over time, with the metre per second, mile per
hour, kilometre per hour, knot and the speed of light, their values in SI units, and the conversions
between them. [59] Energy has dimension mass times length squared over time squared, with the joule,
electronvolt, calorie and kilowatt hour. [60] Pressure has dimension mass over length over time
squared, with the pascal, millimetre of mercury, bar, standard atmosphere, torr and pound per square
inch. [61] Momentum has dimension mass times length over time and takes values in d spatial
components: it is the three-momentum rather than the four-momentum. [62] The mass of a particle is a
named dimension-carrying quantity in the manner of momentum, and so is its velocity in d spatial
dimensions. [TODO]

### Calculus and dimensional correctness

The derivative of a dimensionally correct differentiable function is dimensionally correct, and the
derivative at a rescaled point is the explicitly rescaled derivative. [63] The equation giving the
derivative in a fixed direction as a quantity of the dimension of the target divided by the
dimension of the source is dimensionally correct. [64] A measure on a dimension-carrying type is
unit-dependent, and the integral of a function whose dimension is that of its values divided by the
dimension of the measure has the dimension of the values. [65]

### Examples

A length of 400 metres converts to miles. [66] The relations E = m c^2 and F = m a, stated over
dimension-tagged reals, are dimensionally correct. [67] A speed as distance over time, an expression
of mixed dimension in mass, temperature, current, length and time, and the cosine of an angular
frequency times a time are each dimensionally correct. [68] The relation E = m c is not
dimensionally correct: a change of unit breaks it. [69] The version of E = m c^2 written with the
speed of light in an explicit unit system holds in SI units and, by transport, in every unit system.
[70]

The equality of a length with a speed times a time holds propositionally rather than definitionally,
so the two tagged types are bridged by a cast, and the same comparison works over a set of base
dimensions with no physical unit system, namely bits and symbols. [71]

The harmonic oscillator carries its mass and spring constant with their physical dimensions. Its
potential energy is assembled from dimension-tagged quantities, agrees in coordinates with the
numerical oscillator, and has its derivative from the generic transport of derivatives. [72]

## Lean References

1. Physlib/Units/Dimension.lean — `DimensionBasis`, `DimensionBasis.pi`
2. Physlib/Units/LTMCTDimensionBase.lean — `LTMCTDimensionBase`
3. Physlib/Units/ISQDimensionBase.lean — `ISQDimensionBase`, `ISQDimensionBase.card_eq_seven`
4. Physlib/Units/Dimension.lean — `Dimension`, `Dimension.ext`
5. Physlib/Units/Dimension.lean — `CommGroup (Dimension B)`, `Dimension.qpow_exponent`
6. Physlib/Units/Dimension.lean — `Dimension.mul_exponent`, `Dimension.one_exponent`,
   `Dimension.inv_exponent`, `Dimension.div_exponent`, `Dimension.npow_exponent`
7. Physlib/Units/Dimension.lean — `Dimension.single`, `Dimension.single_exponent`
8. Physlib/Units/LTMCTDimensionBase.lean — `Dimension.length`, `Dimension.time`, `Dimension.mass`,
   `Dimension.charge`, `Dimension.temperature`
9. Physlib/Units/LTMCTDimensionBase.lean — `Dimension.ofLTMCTDimensionBase`
10. Physlib/Units/LTMCTDimensionBase.lean — `Dimension.length_mul`, `Dimension.one_time`,
   `Dimension.inv_mass`, `Dimension.div_charge`, `Dimension.npow_temperature`
11. Physlib/Units/LTMCTDimensionBase.lean — `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`,
   `Dimension.C𝓭`, `Dimension.Θ𝓭`, `Dimension.L𝓭_eq_single`, `Dimension.T𝓭_eq_single`,
   `Dimension.M𝓭_eq_single`, `Dimension.C𝓭_eq_single`, `Dimension.Θ𝓭_eq_single`
12. Physlib/Units/ISQDimensionBase.lean — `ISQDimensionBase.charge`,
   `ISQDimensionBase.charge_exponent_current`, `ISQDimensionBase.charge_exponent_time`,
   `ISQDimensionBase.charge_exponent_mass`
13. Physlib/Units/ISQDimensionBase.lean — `ISQDimensionBase.single_amount_ne_one`,
   `ISQDimensionBase.single_luminousIntensity_ne_one`
14. Physlib/Units/Dimension.lean — `Dimension.extend`, `Dimension.extend_exponent_apply`,
   `Dimension.extendHom`, `Dimension.Embedding`, `Dimension.Projection`,
   `Dimension.Embedding.ofBasis`
15. Physlib/Units/ISQBridge.lean — `Dimension.toISQFun`, `Dimension.toISQHom`,
   `Dimension.toISQHom_apply`, `Dimension.toISQHom_injective`, `Dimension.ltmctToISQ`,
   `Dimension.toISQHom_C𝓭`
16. Physlib/Units/ISQBridge.lean — `Dimension.fromISQFun`, `Dimension.fromISQHom`,
   `Dimension.fromISQHom_apply`, `Dimension.fromISQHom_surjective`, `Dimension.isqToLTMCT`
17. Physlib/Units/ISQBridge.lean — `Dimension.fromISQHom_comp_toISQHom`,
   `Dimension.isqToLTMCT_comp_ltmctToISQ`
18. Physlib/Units/PositiveRealUnit.lean — `PositiveRealUnitCore`, `PositiveRealUnitCore.pos`,
   `PositiveRealUnitCore.instHDiv`, `PositiveRealUnitCore.ratio`, `PositiveRealUnitCore.div_eq_val`
19. Physlib/Units/PositiveRealUnit.lean — `PositiveRealUnitCore.scale`,
   `PositiveRealUnitCore.scale_div_self`, `PositiveRealUnitCore.self_div_scale`,
   `PositiveRealUnitCore.scale_one`, `PositiveRealUnitCore.scale_div_scale`,
   `PositiveRealUnitCore.scale_scale`
20. Physlib/Units/UnitSystem.lean — `UnitMagnitudeCatalog`, `UnitSystem`, `UnitSystem.ext`
21. Physlib/Units/UnitSystem.lean — `UnitSystem.toScale`, `UnitSystem.toScale_scale`
22. Physlib/Units/ParametricUnits.lean — `UnitScale`, `UnitScale.ratio_ne_zero`
23. Physlib/Units/ParametricUnits.lean — `UnitScale.dimScale`, `UnitScale.dimScale_self`,
   `UnitScale.dimScale_one`, `UnitScale.dimScale_transitive`
24. Physlib/Units/Basic.lean — `LTMCTUnitChoices`, `LTMCTUnitChoices.SI`,
   `LTMCTUnitChoices.SI_length`, `LTMCTUnitChoices.SI_time`, `LTMCTUnitChoices.SI_mass`,
   `LTMCTUnitChoices.SI_charge`, `LTMCTUnitChoices.SI_temperature`
25. Physlib/Units/Basic.lean — `LTMCTUnitChoices.dimScale`, `LTMCTUnitChoices.dimScale_apply`
26. Physlib/Units/ParametricUnits.lean — `LTMCTUnitChoices.toScale`
27. Physlib/Units/UnitSystem.lean — `LTMCTUnitChoices.equivUnitSystem`,
   `LTMCTUnitChoices.toScale_equivUnitSystem`, `prod_univ_LTMCTDimensionBase`,
   `LTMCTUnitChoices.dimScale_eq_toScale_dimScale`
28. Physlib/Units/Basic.lean — `LTMCTUnitChoices.dimScale_self`, `LTMCTUnitChoices.dimScale_one`
29. Physlib/Units/Basic.lean — `LTMCTUnitChoices.dimScale_ne_zero`, `LTMCTUnitChoices.dimScale_pos`,
   `LTMCTUnitChoices.dimScale_transitive`, `LTMCTUnitChoices.dimScale_symm`,
   `LTMCTUnitChoices.dimScale_mul_symm`, `LTMCTUnitChoices.dimScale_coe_mul_symm`,
   `LTMCTUnitChoices.dimScale_of_inv_eq_swap`
30. Physlib/Units/Basic.lean — `LTMCTUnitChoices.smul_dimScale_injective`
31. Physlib/Units/Basic.lean — `LTMCTUnitChoices.SIPrimed`, `LTMCTUnitChoices.dimScale_SI_SIPrimed`,
   `LTMCTUnitChoices.dimScale_SIPrimed_SI`
32. Physlib/Units/SIUnitChoices.lean — `CurrentUnit`, `AmountUnit`, `LuminousIntensityUnit`
33. Physlib/Units/SIUnitChoices.lean — `CurrentUnit.amperes`, `AmountUnit.moles`,
   `LuminousIntensityUnit.candelas`
34. Physlib/Units/SIUnitChoices.lean — `CurrentUnit.milliamperes`
35. Physlib/Units/SIUnitChoices.lean — `SIUnitChoices`, `SIUnitChoices.SI`
36. Physlib/Units/SIUnitChoices.lean — `prod_univ_ISQDimensionBase`, `SIUnitChoices.dimScale`,
   `SIUnitChoices.dimScale_self`
37. Physlib/Units/Basic.lean — `HasDim`, `HasDim.d`, `dim`, `CarriesDimension`
38. Physlib/Units/Basic.lean — `HasDimension`, `hasDimension_iff`
39. Physlib/Units/Basic.lean — `Dimensionful`, `Dimensionful.ext`, `Dimensionful.smul_apply`
40. Physlib/Units/Basic.lean — `CarriesDimension.toDimensionful`,
   `CarriesDimension.toDimensionful_apply_apply`
41. Physlib/Units/UnitDependent.lean — `UnitDependent`
42. Physlib/Units/UnitDependent.lean — `MulUnitDependent`, `LinearUnitDependent`,
   `ContinuousLinearUnitDependent`
43. Physlib/Units/UnitDependent.lean — `UnitDependent.scaleUnit_symm_apply`,
   `UnitDependent.scaleUnit_injective`, `UnitDependent.scaleUnitEquiv`,
   `LinearUnitDependent.scaleUnitLinear`, `LinearUnitDependent.scaleUnitLinearEquiv`,
   `ContinuousLinearUnitDependent.scaleUnitContLinear`,
   `ContinuousLinearUnitDependent.scaleUnitContLinearEquiv`
44. Physlib/Units/UnitDependent.lean — `LTMCTUnitChoices.scaleUnit_apply_fst`,
   `LTMCTUnitChoices.dimScale_scaleUnit`, `Dimensionful.of_scaleUnit`, `HasDim.scaleUnit_apply`
45. Physlib/Units/UnitDependent.lean — `UnitDependent.scaleUnit_apply_fun_right`,
   `UnitDependent.scaleUnit_apply_fun_left`, `UnitDependent.scaleUnit_apply_fun`,
   `instUnitDependentTwoSided`, `instUnitDependentTwoSidedMul`,
   `instContinuousLinearUnitDependentMap`
46. Physlib/Units/UnitDependent.lean — `IsDimensionallyCorrect`, `isDimensionallyCorrect_iff`,
   `isDimensionallyCorrect_fun_iff`, `isDimensionallyCorrect_fun_left`,
   `isDimensionallyCorrect_fun_right`
47. Physlib/Units/UnitDependent.lean — `DMul`, `DMul.hMul_scaleUnit`
48. Physlib/Units/UnitDependent.lean — `DimSet`, `DimSet.mem_iff`, `scaleUnit_dimSet_val`
49. Physlib/Units/WithDim/Basic.lean — `WithDim`, `WithDim.ext`, `WithDim.dim_apply`
50. Physlib/Units/WithDim/Basic.lean — `WithDim.val_zero`, `WithDim.val_add`, `WithDim.val_neg`,
   `WithDim.val_sub`
51. Physlib/Units/WithDim/Basic.lean — `WithDim.le_def`, `WithDim.lt_def`, `WithDim.smul_val`
52. Physlib/Units/WithDim/Basic.lean — `WithDim.withDim_hMul_val`, `WithDim.val_mul_eq_mul`,
   `WithDim.val_pow_two_eq_mul`, `WithDim.val_div_val`, `WithDim.div_scaleUnit`
53. Physlib/Units/WithDim/Basic.lean — `WithDim.scaleUnit_val`,
   `WithDim.scaleUnit_val_eq_scaleUnit_val`, `WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq`
54. Physlib/Units/WithDim/Basic.lean — `WithDim.scaleUnit_dim_eq_zero`
55. Physlib/Units/WithDim/Basic.lean — `WithDim.cast`, `WithDim.cast_refl`, `WithDim.cast_scaleUnit`
56. Physlib/Units/WithDim/Basic.lean — `instModuleReal`, `real_smul_val`
57. Physlib/Units/WithDim/Analysis.lean — `toValueAddEquiv`, `toValueLinearEquiv`,
   `instNormedAddCommGroup`, `instNormedSpace`, `toValueLinearIsometryEquiv`, `transport`,
   `transportLinearMap`, `hasFDerivAt_transport`
58. Physlib/Units/WithDim/Area.lean — `DimArea`, `DimArea.squareMeter`, `DimArea.squareFoot`,
   `DimArea.squareMile`, `DimArea.are`, `DimArea.hectare`, `DimArea.acre`,
   `DimArea.squareFoot_in_SI`, `DimArea.squareMile_in_SI`, `DimArea.acre_in_SI`,
   `DimArea.acre_eq_mul_squareFeet`
59. Physlib/Units/WithDim/Speed.lean — `DimSpeed`, `DimSpeed.oneMeterPerSecond`,
   `DimSpeed.oneMilePerHour`, `DimSpeed.oneKilometerPerHour`, `DimSpeed.oneKnot`,
   `DimSpeed.speedOfLight`, `DimSpeed.oneMilePerHour_in_SI`, `DimSpeed.speedOfLight_in_SI`,
   `DimSpeed.oneKnot_eq_mul_oneKilometerPerHour`, `DimSpeed.oneKilometerPerHour_eq_mul_oneKnot`,
   `DimSpeed.oneMeterPerSecond_eq_mul_oneMilePerHour`
60. Physlib/Units/WithDim/Energy.lean — `DimEnergy`, `DimEnergy.joule`, `DimEnergy.electronVolt`,
   `DimEnergy.calorie`, `DimEnergy.kilowattHour`
61. Physlib/Units/WithDim/Pressure.lean — `DimPressure`, `DimPressure.pascal`,
   `DimPressure.millimeterOfMercury`, `DimPressure.bar`, `DimPressure.standardAtmosphere`,
   `DimPressure.torr`, `DimPressure.psi`
62. Physlib/Units/WithDim/Momentum.lean — `Momentum`
63. Physlib/Units/FDeriv.lean — `fderiv_apply_scaleUnit`, `fderiv_isDimensionallyCorrect`
64. Physlib/Units/FDeriv.lean — `fderiv_dimension_const_direction`
65. Physlib/Units/Integral.lean — `scaleUnit_measure`, `integral_isDimensionallyCorrect`
66. Physlib/Units/Examples.lean — `UnitExamples.meters400`
67. Physlib/Units/Examples.lean — `UnitExamples.EnergyMassWithDim`,
   `UnitExamples.energyMassWithDim_isDimensionallyCorrect`, `UnitExamples.NewtonsSecondWithDim`,
   `UnitExamples.newtonsSecondWithDim_isDimensionallyCorrect`
68. Physlib/Units/Examples.lean — `UnitExamples.SpeedEq`,
   `UnitExamples.speedEq_isDimensionallyCorrect`, `UnitExamples.OddDimensions`,
   `UnitExamples.oddDimensions_isDimensionallyCorrect`, `UnitExamples.CosDim`,
   `UnitExamples.cosDim_isDimensionallyCorrect`
69. Physlib/Units/Examples.lean — `UnitExamples.EnergyMassWithDimNot`,
   `UnitExamples.energyMassWithDimNot_not_isDimensionallyCorrect`
70. Physlib/Units/Examples.lean — `UnitExamples.EnergyMass`,
   `UnitExamples.energyMass_isDimensionallyCorrect`, `UnitExamples.example1_energyMass`,
   `UnitExamples.example2_energyMass`
71. Physlib/Units/ParametricDimensionExamples.lean — `ParametricDimensionExamples.Info`,
   `ParametricDimensionExamples.bitDim`, `ParametricDimensionExamples.symbolDim`
72. Physlib/ClassicalMechanics/HarmonicOscillator/WithDim.lean — `HarmonicOscillatorWithDim`,
   `HarmonicOscillatorWithDim.toHarmonicOscillator`, `HarmonicOscillatorWithDim.positionNormSq`,
   `HarmonicOscillatorWithDim.potentialEnergy`, `HarmonicOscillatorWithDim.potentialEnergy_val`,
   `HarmonicOscillatorWithDim.potentialEnergy_eq_transport`,
   `HarmonicOscillatorWithDim.hasFDerivAt_potentialEnergy`,
   `HarmonicOscillatorWithDim.continuous_potentialEnergy`

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
