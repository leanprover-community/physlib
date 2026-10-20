# Tensors

## Abstract

Tensors appear in one form or another throughout physics. The most common example is the
Lorentz tensors, which in the most general setting also include Weyl fermions, and are associated
with the Lorentz group in the real case and `SL(2, ℂ)` in the complex case. In this API we define
the general framework for working with these tensors, and others, and their corresponding indices.
The goal is to enable physicists to use index notation in a similar way to how they would on
pen and paper.

## Content (Alpha)

### Tensor species

A tensor species consists of a symmetry group, a type of index colors, a representation and a
basis for each color, an involution sending each color to the dual color it may contract with,
and contraction and unit data satisfying coherence conditions. [1] A species may carry a metric:
an invariant tensor for each color whose contraction against the metric of the dual color is the
unit, this condition forming a class of its own. [2] The conditions defining a species also relate
the metrics to the basis vectors. [TODO]

### Tensors and their components

Given a species and a list of colors, the tensors with those indices form the tensor product of
the color representations over the index set, and the pure tensors are the choices of one vector
for each index. [3] A component label assigns a basis index to each tensor index. [4] A
component label of a single index is a basis index of its color, a label of a concatenated index
list is a pair of labels, and a label drops a contracted pair of indices. [5][6][7] A tensor
corresponds to its components in the component basis, and the tensors with no indices are the
scalars. [3]

### Group action and reindexing

The symmetry group acts on pure tensors and on tensors. [8] Indices permute along a
color-preserving map, equivariantly, functorially and injectively. [8] The maps that count as
reindexings are characterized and are closed under inverse and composition; they include the
index maps used by products, evaluation and contraction. [9]

### Products

The tensor product of two pure tensors, or of two tensors, concatenates their index lists. [10]
It has explicit components in the basis, is equivariant, and is compatible with swapping the
factors, permuting either factor, and rebracketing. [10]

### Contraction

A pair of indices of dual color contracts, on pure tensors and on tensors, deleting the pair from
the index list. [11][12][13] Contraction is equivariant, commutes with permutations, is symmetric
in the contracted pair, and contractions of two different pairs commute. [13] Its components in
the basis are sums over the contracted label. [14] Contracting inside one factor of a product
agrees with contracting the product. [15]

One tensor also contracts against another at an addressed slot, either with the result placed at
the end [16] or with the result placed at the slot. [17] For real Lorentz tensors the
result-to-end contraction has explicit components in the standard basis. [18]

### Units, metrics, raising and lowering

The unit tensor of a color is invariant under the group action, has explicit components, and is
the permuted unit tensor of the dual color. [19] The metric tensor of a color is invariant, and
contracting it against the metric tensor of the dual color gives the unit. [20] The unit tensor
is an identity for contraction at a slot, so raising and then lowering an index is a round
trip. [21] Raising or lowering a named index, by contraction with the metric, is an equivariant
linear equivalence. [22]

### Evaluation

One index of a tensor evaluates at a fixed basis label, on pure tensors and on tensors. [23]
Evaluation has explicit components in the basis, and commutes with permutations, with other
evaluations, with contractions and with products in their right factor. [23] A tensor is the sum
over basis labels of the evaluations of its last index, each tensored with the matching rank-one
basis tensor and permuted back into the last slot. [23] Evaluation also commutes with a product
in its left factor and with contraction in the opposite order, and two evaluations of the same
tensor commute. [TODO]

### Constructing tensors

Tensors arise from single vectors, from elements of a tensor product of two or three carriers,
and from invariant maps. [24] They also arise from integer components in the standard
basis. [25] Complex Lorentz tensors arise from Gaussian-integer components, compatibly with
products, contractions and permutations. [26]

### Index notation

An elaborator turns pen-and-paper index expressions into tensor operations. [27] The design follows
Tooby-Smith {1}. A class carries index notation to any type linearly equivalent to a tensor, with
the induced group action, basis and products. [28]

### Conjugation

A species may carry a conjugation: a second involution on colors together with a conjugation of
tensors, which is involutive and commutes with contraction. [29] A componentwise criterion for a
tensor to equal a permutation of its conjugate expresses reality, and gives the Hermitian
condition on a metric slot. [29] Both Lorentz species carry conjugations, so that reality and
Hermiticity conditions apply to real and complex Lorentz tensors. [TODO]

### Real Lorentz tensors

The real Lorentz tensors form a species over the Lorentz group {2} with an upper and a lower color,
each dual to the other; in it, contraction is a sum of evaluations. [30] Its colors are carried by
the contravariant and covariant modules, with their representations of the Lorentz group and their
standard bases. [31][32] The two modules contract invariantly against each other. [33] The species
has metric maps [34] and unit maps. [35] Its metric tensors have the Minkowski matrix as components
in the standard basis, and raising or lowering an index multiplies components by the Minkowski
matrix. [36] Its unit tensor has explicit components. [37] Pairwise tensor products of the two
modules are square matrices. [38] The metrics and units of this species are intertwining maps of the
vector and covector representations, with no preliminary constructions or auxiliary modules.
[TODO]

### Lorentz vectors and covectors

A Lorentz vector is a function on one time index and d space indices. [39] Lorentz vectors carry
module, norm and inner-product structures, a charted-space structure, a standard basis and
coordinate maps, a time component and a spatial part, and a model with corners under which they
form a manifold. [39] The Lorentz group acts on them by matrix-vector multiplication. [40] They
are tensorial, the induced action on the standard basis being the matrix action. [41] Lorentz
covectors carry the same structures [42], the same kind of representation [43], and a tensorial
instance. [44] Vectors and covectors contract invariantly against each other. [45]

### Minkowski product and causality

The Minkowski product of two Lorentz vectors is symmetric, Lorentz invariant and
nondegenerate. [46] Linear maps have adjoints with respect to it, and a linear map preserves it
exactly when its matrix lies in the Lorentz group. [46]

Each vector has a causal character — timelike, lightlike or spacelike — that is invariant under
Lorentz transformations, and the product determines light cones, causal precedence and causal
diamonds. [47] A vector is spacelike exactly when its Minkowski norm squared is negative. [47] It
is timelike exactly when that norm squared is positive, and then its time component dominates its
spatial part. [48] It is lightlike exactly when that norm squared vanishes, and causal precedence
is reflexive. [49] A Lorentz velocity is a future-directed vector of unit Minkowski norm; its time
component is positive and dominates its spatial part, and the velocities form a path-connected
set. [50]

### Levi-Civita tensor

The rank-four Levi-Civita tensor is a real Lorentz tensor in three spatial dimensions whose
components in the standard basis are the Levi-Civita symbol, and it is antisymmetric under each
adjacent transposition of indices. [51] The Euclidean Levi-Civita symbol satisfies the
epsilon-epsilon contraction identities summed over all four index slots, over the last three,
and over the last two. [52] At the level of tensors, contracting the Levi-Civita tensor with
itself over all four index pairs gives −24, and over the first three gives −6 times the unit
tensor of the lower color. [63][64][37] A Euclidean Levi-Civita tensor carries the
epsilon-epsilon contraction identities as identities between tensors. [TODO]

### Complex Lorentz tensors

The complex Lorentz tensors form a species over SL(2, ℂ) with the left- and right-handed Weyl colors
{3}, their duals, and the two Lorentz vector colors. [53] The vector colors are carried by complex
contravariant and covariant modules with their representations of SL(2, ℂ), which contract
invariantly against each other. [54][55] The metric tensors [56] and unit tensors [57] of each color
have several equivalent forms, including Gaussian-integer components, and the units are symmetric.
[58] Pairwise products of complex Lorentz vectors are square matrices. [59] The full contraction of
an antisymmetric tensor with a symmetric one equals its own negative. [60] The complex Levi-Civita
tensor has Gaussian-integer components. [61]

### From real to complex tensors

A canonical injective semilinear map takes real Lorentz tensors to complex ones, sending colors
and component labels to their complex counterparts. [62] It is equivariant for the complexified
Lorentz group and commutes with permutations, products, contractions and evaluations of
indices. [62]

## Lean References

1. Physlib/Relativity/Tensors/TensorSpecies/Basic.lean — `TensorSpecies`, `basisIdxCongr`,
   `τ_τ_apply`, `basis_congr`, `numIndices`
2. Physlib/Relativity/Tensors/TensorSpecies/Basic.lean — `TensorSpecies.WithMetric`,
   `TensorSpecies.metric`, `TensorSpecies.contr_metric`
3. Physlib/Relativity/Tensors/Basic.lean — `Tensor`, `Pure`, `Pure.toTensor`, `Pure.component`,
   `Pure.basisVector`, `Tensor.componentMap`, `ofComponents`, `basis`, `basis_repr_pure`,
   `toScalar`
4. Physlib/Relativity/Tensors/ComponentIdx/Basic.lean — `ComponentIdx`,
   `ComponentIdx.congr_right`, `ComponentIdx.cast`
5. Physlib/Relativity/Tensors/ComponentIdx/Single.lean — `ComponentIdx.single`
6. Physlib/Relativity/Tensors/ComponentIdx/Product.lean — `ComponentIdx.prod`
7. Physlib/Relativity/Tensors/ComponentIdx/Contraction.lean — `ComponentIdx.dropPair`,
   `ComponentIdx.DropPairSection`, `ComponentIdx.DropPairSection.ofFinEquiv`,
   `ComponentIdx.DropPairSection.ofFinEquiv_dropPair`
8. Physlib/Relativity/Tensors/Basic.lean — `actionP`, `actionT`, `Pure.permP`, `permT`,
   `permT_equivariant`, `permT_permT`, `permT_injective`
9. Physlib/Relativity/Tensors/Reindexing.lean — `IsReindexing`, `IsReindexing.toEquiv`,
   `IsReindexing.inv`, `IsReindexing.comp`, `IsReindexing.symm`,
   `IsReindexing.append_congr_left`, `IsReindexing.append_congr_right`,
   `IsReindexing.append_swap`, `IsReindexing.succAbove`, `IsReindexing.succSuccAbove`
10. Physlib/Relativity/Tensors/Product.lean — `Pure.prodP`, `prodT`, `prodT_basis`,
   `prodT_basis_repr_apply`, `tensorEquivProd`, `prodT_equivariant`, `prodT_swap`,
   `prodT_permT_left`, `prodT_permT_right`, `prodT_assoc`, `prodT_assoc'`
11. Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean — `Fin.succSuccAbove`,
   `Fin.predPredAbove`, `Fin.funPredPredAbove`
12. Physlib/Relativity/Tensors/Contraction/Pure.lean — `Pure.dropPair`, `Pure.contrPCoeff`,
   `Pure.contrP`, `Pure.contrPMultilinear`
13. Physlib/Relativity/Tensors/Contraction/Basic.lean — `contrT`, `contrT_pure`,
   `contrT_equivariant`, `contrT_permT`, `contrT_symm`, `contrT_comm`
14. Physlib/Relativity/Tensors/Contraction/Basis.lean — `contrT_basis_repr_apply`,
   `contrT_basis_repr_apply_eq_sum_fin`, `contrT_basis`
15. Physlib/Relativity/Tensors/Contraction/Products.lean — `prodT_contrT_snd`,
   `contrT_prodT_snd`, `prodT_contrT_fst`
16. Physlib/Relativity/Tensors/Contraction/CrossToEnd.lean — `crossToEnd`, `crossToEnd_two`,
   `crossToEnd_equivariant`, `crossToEnd_assoc_rankTwo`, `crossToEnd_permT_left`,
   `crossToEnd_permT_right`
17. Physlib/Relativity/Tensors/Contraction/CrossToSlot.lean — `crossToSlot`,
   `crossToSlot_eq_crossToEnd`, `crossToSlot_basis_repr_apply`, `crossToSlotInv`,
   `crossToSlot_equivariant`
18. Physlib/Relativity/Tensors/RealTensor/Contraction/CrossToEnd.lean — `crossToEnd_basis_repr_apply_eq_fin`
19. Physlib/Relativity/Tensors/UnitTensor.lean — `unitTensor`, `unitTensor_basis_repr`,
   `unitTensor_eq_permT_dual`, `contrT_single_unitTensor`, `unitTensor_invariant`
20. Physlib/Relativity/Tensors/MetricTensor.lean — `metricTensor`, `metricTensor_basis_repr`,
   `metricTensor_invariant`, `contrT_metricTensor_metricTensor`,
   `contrT_metricTensor_metricTensor_eq_dual_unit`
21. Physlib/Relativity/Tensors/Contraction/UnitTensorContraction.lean — `crossToEnd_unitTensor`,
   `crossToEnd_round_trip_of_unit_slot`, `crossToSlot_raise_lower_round_trip`,
   `crossToSlotEquiv`
22. Physlib/Relativity/Tensors/Dual.lean — `toDualMapAtIndex`, `fromDualMapAtIndex`,
   `toDualMapAtIndex_toDualMapAtIndex`, `toDualMapAtIndex_equivariant`, `toDualAtIndex`
23. Physlib/Relativity/Tensors/Evaluation.lean — `Pure.evalPCoeff`, `Pure.evalP`,
   `Pure.evalPMultilinear`, `evalT`, `evalT_basis`, `evalT_permT`, `evalT_evalT`,
   `contrT_evalT`, `evalT_prodT_right`, `eq_sum_evalT`, `ext_of_evalT`
24. Physlib/Relativity/Tensors/Constructors.lean — `Pure.fromSingleP`, `fromSingleT`,
   `fromPairT`, `fromPairTContr`, `fromSingleTContrFromPairT`, `fromConstPair`, `fromTripleT`,
   `fromConstTriple`
25. Physlib/Relativity/Tensors/OfInt.lean — `TensorInt`, `TensorInt.toTensor`,
   `basis_eq_tensorInt`
26. Physlib/Relativity/Tensors/ComplexTensor/OfGaussianInt.lean — `ofGaussianInt`,
   `basis_eq_ofGaussianInt`, `prodT_ofGaussianInt_ofGaussianInt`, `contrT_ofGaussianInt`,
   `permT_ofGaussianInt`
27. Physlib/Relativity/Tensors/Elab.lean — `tensorExprSyntax`, `elaborateTensorNode`,
   `syntaxFull`, `TensorExpressionOperator`
28. Physlib/Relativity/Tensors/Tensorial.lean — `Tensorial`, `Tensorial.self`,
   `Tensorial.numIndices`, `Tensorial.mulAction`, `Tensorial.smulLinearMap`, `Tensorial.prod`,
   `Tensorial.toTensorCLM`, `Tensorial.actionCLM`, `Tensorial.basis_toTensor_apply`,
   `Tensorial.basis_map_prod`
29. Physlib/Relativity/Tensors/Conjugation/Basic.lean — `ConjTensorSpecies`, `conjEquiv`,
   `componentReindex`, `conjT`, `conjT_basis`, `conjT_conjT`, `conjT_contrT`,
   `conjT_eq_permT_iff`, `IsHermitian`
30. Physlib/Relativity/Tensors/RealTensor/Basic.lean — `realLorentzTensor`,
   `realLorentzTensor.Color`, `τ_up_eq_down`, `τ_down_eq_up`, `contrPCoeff_basis`,
   `contrT_eq_sum_evalT`, `contrT_toScalar`
31. Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean — `ContrMod`, `CoMod`,
   `AddCommGroup (ContrMod d)`, `Module ℝ (ContrMod d)`, `AddCommGroup (CoMod d)`,
   `Module ℝ (CoMod d)`, `ContrMod.rep`, `CoMod.rep`, `ContrMod.stdBasis`, `CoMod.stdBasis`
32. Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Basic.lean — `contrBasis`, `coBasis`,
   `contrIsoCo`
33. Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Contraction.lean — `contrCoContract`,
   `coContrContract`, `contrContrContractField`
34. Physlib/Relativity/Tensors/RealTensor/Metrics/Pre.lean — `preContrMetric`, `preCoMetric`
35. Physlib/Relativity/Tensors/RealTensor/Units/Pre.lean — `preContrCoUnit`, `preCoContrUnit`
36. Physlib/Relativity/Tensors/RealTensor/Metrics/Basic.lean — `coMetric`, `contrMetric`,
   `actionT_coMetric`, `actionT_contrMetric`, `coMetric_repr_apply_eq_minkowskiMatrix`,
   `contrMetric_repr_apply_eq_minkowskiMatrix`, `metricTensor_repr_apply_eq_minkowskiMatrix`,
   `toDualMapAtIndex_basis_repr_apply`, `toDualMapAtIndex_basis_repr_apply_eq_mul`
37. Physlib/Relativity/Tensors/RealTensor/Units/Basic.lean — `unitTensor_repr_apply`
38. Physlib/Relativity/Tensors/RealTensor/Matrix/Pre.lean — `contrContrToMatrixRe`,
   `coCoToMatrixRe`, `contrCoToMatrixRe`, `coContrToMatrixRe`
39. Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean — `Lorentz.Vector`,
   `AddCommGroup (Vector d)`, `Module ℝ (Vector d)`, `Norm (Vector d)`,
   `NormedAddCommGroup (Vector d)`, `NormedSpace ℝ (Vector d)`,
   `InnerProductSpace ℝ (Vector d)`, `ChartedSpace (Vector d) (Vector d)`, `Vector.equivEuclid`,
   `Vector.basis`, `Vector.basis_repr_apply`, `Vector.coordCLM`, `Vector.euclidCLE`,
   `Vector.timeComponent`, `Vector.spatialPart`, `Vector.spatialCLM`, `Vector.temporalCLM`,
   `Vector.asSmoothManifold`
40. Physlib/Relativity/Tensors/RealTensor/Vector/Representation.lean — `Vector.rep`,
   `Vector.rep_apply_eq_mulVec`, `Vector.rep_bijective`
41. Physlib/Relativity/Tensors/RealTensor/Vector/Tensorial.lean — `Vector.tensorial`,
   `Vector.smul_eq_mulVec`, `Vector.smul_basis`, `Vector.actionCLM`
42. Physlib/Relativity/Tensors/RealTensor/CoVector/Basic.lean — `Lorentz.CoVector`,
   `AddCommGroup (CoVector d)`, `Module ℝ (CoVector d)`, `Norm (CoVector d)`,
   `NormedAddCommGroup (CoVector d)`, `NormedSpace ℝ (CoVector d)`,
   `InnerProductSpace ℝ (CoVector d)`, `ChartedSpace (CoVector d) (CoVector d)`,
   `CoVector.equivEuclid`, `CoVector.basis`, `CoVector.basis_repr_apply`
43. Physlib/Relativity/Tensors/RealTensor/CoVector/Representation.lean — `CoVector.rep`,
   `CoVector.rep_apply_eq_mulVec`, `CoVector.rep_bijective`
44. Physlib/Relativity/Tensors/RealTensor/CoVector/Tensorial.lean — `CoVector.tensorial`,
   `CoVector.actionCLM`
45. Physlib/Relativity/Tensors/RealTensor/Representation/Contraction.lean — `Vector.contract`,
   `CoVector.contract`, `Vector.contract_rep`, `CoVector.contract_rep`
46. Physlib/Relativity/Tensors/RealTensor/Vector/MinkowskiProduct.lean — `minkowskiProductMap`,
   `minkowskiProduct`, `minkowskiProduct_symm`, `minkowskiProduct_invariant`,
   `minkowskiProduct_basis_left`, `minkowskiProduct_eq_zero_forall_iff`, `adjoint`, `IsLorentz`,
   `isLorentz_iff_toMatrix_mem_lorentzGroup`
47. Physlib/Relativity/Causality/Basic.lean — `CausalCharacter`, `causalCharacter`,
   `causalCharacter_invariant`, `spaceLike_iff_norm_sq_neg`, `interiorFutureLightCone`,
   `interiorPastLightCone`, `causallyPrecedes`, `causalDiamond`, `isFutureDirected`
48. Physlib/Relativity/Causality/TimeLike.lean — `timeLike_iff_norm_sq_pos`,
   `timelike_time_dominates_space`
49. Physlib/Relativity/Causality/LightLike.lean — `lightLike_iff_norm_sq_zero`,
   `causallyPrecedes_refl`
50. Physlib/Relativity/Tensors/RealTensor/Velocity/Basic.lean — `Velocity`,
   `Velocity.timeComponent_pos`, `Velocity.norm_spatialPart_le_timeComponent`,
   `Velocity.isPathConnected`
51. Physlib/Relativity/Tensors/LeviCivita/Basic.lean — `leviCivita`, `notation ε4`,
   `euclidLeviCivita`, `leviCivita_basis_repr_apply`,
   `leviCivita_basis_repr_eq_leviCivitaSymbol`, `leviCivita_antisymm`,
   `leviCivita_antisymm_mid`, `leviCivita_antisymm_last`
52. Physlib/Relativity/Tensors/LeviCivita/Contractions.lean — `euclidLeviCivita_symbol_contract_zero`,
   `euclidLeviCivita_symbol_contract_one`, `euclidLeviCivita_symbol_contract_one_last`,
   `euclidLeviCivita_symbol_contract_two`, `leviCivita_lowered_basis_repr_apply`,
   `leviCivita_basis_contract_self`, `leviCivita_basis_contract_three`,
   `leviCivita_contract_three_basis_repr_apply`, `leviCivita_contract_self_eq_sum`,
   `leviCivita_contract_self`, `leviCivita_contract_three`
53. Physlib/Relativity/Tensors/ComplexTensor/Basic.lean — `complexLorentzTensor`,
   `complexLorentzTensor.Color`, `repDim`, `basis`, `rep`, `contrPCoeff_basis`
54. Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Modules.lean — `ContrℂModule`,
   `CoℂModule`, `ContrℂModule.SL2CRep`, `CoℂModule.SL2CRep`
55. Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Contraction.lean — `contrCoContraction`,
   `coContrContraction`
56. Physlib/Relativity/Tensors/ComplexTensor/Metrics/Basic.lean — `coMetric`, `contrMetric`,
   `leftMetric`, `rightMetric`, `dualLeftMetric`, `dualRightMetric`,
   `coMetric_eq_ofGaussianInt`, `leftMetric_eq_ofGaussianInt`
57. Physlib/Relativity/Tensors/ComplexTensor/Units/Basic.lean — `coContrUnit`, `contrCoUnit`,
   `dualLeftLeftUnit`, `leftDualLeftUnit`, `dualRightRightUnit`, `rightDualRightUnit`
58. Physlib/Relativity/Tensors/ComplexTensor/Units/Symm.lean — `coContrUnit_symm`,
   `dualLeftLeftUnit_symm`
59. Physlib/Relativity/Tensors/ComplexTensor/Matrix/Pre.lean — `contrContrToMatrix`,
   `coCoToMatrix`, `contrCoToMatrix`, `coContrToMatrix`
60. Physlib/Relativity/Tensors/ComplexTensor/Lemmas.lean — `antiSymm_contr_symm`
61. Physlib/Relativity/Tensors/LeviCivita/Complex.lean — `leviCivita`, `notation ε4ℂ`,
   `leviCivita_eq_ofGaussianInt`
62. Physlib/Relativity/Tensors/RealTensor/ToComplex.lean — `colorToComplex`,
   `ComponentIdx.complexify`, `toComplex`, `toComplex_basis`, `toComplex_pure_basisVector`,
   `toComplex_injective`, `toComplex_equivariant`, `permT_toComplex`, `prodT_toComplex`,
   `contrT_toComplex`, `evalT_toComplex`
63. Physlib/Relativity/Tensors/LeviCivita/Contractions.lean — `leviCivita_lowered_basis_repr_apply`,
   `leviCivita_contract_self`, `leviCivita_contract_three`
64. Physlib/Relativity/Tensors/RealTensor/Metrics/Basic.lean — `toDualMapAtIndex_basis_repr_apply`,
   `toDualMapAtIndex_basis_repr_apply_eq_mul`

## References

1. J. Tooby-Smith, *Formalization of physics index notation in Lean 4*, arXiv:2411.07667,
   https://arxiv.org/abs/2411.07667
2. Lorentz Group API map — Physlib/Relativity/LorentzGroup/API-map.md
3. Weyl Fermions API map — Physlib/Relativity/Fermions/Weyl/API-map.md
