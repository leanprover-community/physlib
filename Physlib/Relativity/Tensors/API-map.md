# Tensors

A tensor species packages everything needed to define a type of tensor with index notation: a
symmetry group, a type of index colors, a representation and a basis for each color, an
involution naming the dual color an index may contract with, and the contraction, unit and
metric data for each dual pair. Given a species and a list of colors, there is the type of
tensors with those indices, realized as a tensor product over the index set; the type of pure
tensors; and the type of component labels.

On that base the API builds the operations of ordinary index notation: permutation and
reindexing of indices, tensor products, contraction of a dual pair both within one tensor and
across two, evaluation of an index at a fixed component, raising and lowering against the
metric, and conjugation. An elaborator turns pen-and-paper index expressions into those
operations, and a further class carries index notation over to any type linearly equivalent to
a tensor.

Two species are constructed. The real Lorentz tensors have an upper and a lower color over the
Lorentz group, and support Lorentz vectors and covectors, the Minkowski product, causal
character, velocities, and the rank-four Levi-Civita tensor. The complex Lorentz tensors have
the two Weyl colors and their duals alongside the Lorentz vector colors, over SL(2, ℂ). A
canonical equivariant semilinear map takes the first species into the second, commuting with
permutation, tensor products, contraction of a dual pair and evaluation of an index.

## Built on

- Lorentz Group — `Physlib/Relativity/LorentzGroup`
- Weyl Fermions — `Physlib/Relativity/Fermions/Weyl`

## Requirements

The key data structure is defined: a tensor species, given by a group, a type of index colors,
a representation and a basis for each color, the dual-color involution, and the contraction and
unit data satisfying the coherence conditions. [1]

A species may carry a metric: an invariant tensor for each color whose contraction against the
metric of the dual color is the unit. That condition is a class of its own. [2]

The tensors with a given list of index colors are defined, along with the pure tensors, the
component labels, the passage between a tensor and its components, the component basis, and the
identification of the rank-zero tensors with the scalars. [3][4][5][6][7]

The symmetry group acts on pure tensors and on tensors, indices permute along a color-preserving
map, and the maps that count as reindexings are characterized and shown closed under inverse
and composition, including the index maps used by products, evaluation and
contraction. [8][9]

The tensor product of pure tensors and of tensors is defined, with its components in the basis,
its equivariance, and its behaviour under swapping the factors, permuting either factor, and
rebracketing. [10]

A pair of indices of dual color contracts, on pure tensors and on tensors, with its
equivariance, its components in the basis, and its interaction with permutations and products;
one tensor also contracts against another at an addressed slot, in both the result-to-end and
the result-to-slot conventions. [11][12][13][14][15][16][17][18]

The unit tensor and the metric tensor of a color are defined, invariant under the group action;
a metric contracted against the metric of the dual color collapses, the unit tensor is an
identity for slot contraction, and raising and lowering a named index is a linear
equivalence. [19][20][21][22]

One index of a tensor evaluates at a fixed basis label, with its components in the basis and
its commutation with permutations, other evaluations, contractions and products; and a tensor
is reconstructed as the sum over basis labels of the evaluations of its last index, each
tensored with the matching rank-one basis tensor and permuted back into the last slot. [23]

Tensors can be constructed explicitly: from vectors, from elements of a tensor product of two
or three carriers, from invariant maps, and from integer or rational components in the standard
basis. [24][25][26]

An elaborator turns pen-and-paper index expressions into tensor operations, and a class carries
index notation to any type linearly equivalent to a tensor, with the induced group action,
basis and products. [27][28]

A species may carry a conjugation: a second involution on colors, the conjugation of a tensor,
its involutivity and its commutation with contraction, together with the componentwise
criterion used to state reality and the Hermitian condition on a metric slot. [29]

The species of real Lorentz tensors is constructed, with an upper and a lower color, from the
contravariant and covariant modules, their representations of the Lorentz group, their bases,
and the contraction, metric and unit maps. Its metric tensors are computed in the standard
basis, and the pairwise tensor products of the two modules are identified with square
matrices. [30][31][32][33][34][35][36][37][38]

Lorentz vectors and covectors are functions on one time and d space indices, with their module,
norm and inner-product structures, their charted-space structures, their standard bases, their
representations of the Lorentz group, their tensorial instances and the invariant contraction
between them, together with the coordinate maps, the time and spatial parts of a vector, and
the model with corners under which vectors are treated as a
manifold. [39][40][41][42][43][44][45]

The Minkowski product of two Lorentz vectors is defined, with its symmetry, invariance and
nondegeneracy, the adjoint of a linear map and the characterization of the maps preserving the
product, and the causal structure it determines: causal character and its invariance, the light
cones and causal relations, the norm characterizations of timelike and lightlike vectors, and
the Lorentz velocities. [46][47][48][49][50]

The rank-four Levi-Civita tensor is defined as a real Lorentz tensor in three spatial
dimensions, with its components in the standard basis as a Levi-Civita symbol, its antisymmetry
under each adjacent transposition of indices, and the epsilon-epsilon contraction identities at
the level of the Euclidean symbol — summed over all four index slots, over the last three, and
over the last two. [51][52]

The species of complex Lorentz tensors is constructed, with the left- and right-handed Weyl
colors, their duals and the two Lorentz vector colors over SL(2, ℂ), together with the metric
and unit tensors of each color in several equivalent forms, and the identification of pairwise
products of complex Lorentz vectors with matrices. [53][54][55][56][57][58][59][60][61]

A canonical injective semilinear map takes real Lorentz tensors to complex ones, equivariantly
for the complexified Lorentz group and commuting with permutations, products, contractions and
evaluations of indices. [62]

Both Lorentz species will be extended to conjugation species, so that reality and Hermiticity
conditions can be stated for real and complex Lorentz tensors. [planned]

The metrics and units of the real Lorentz species will be defined as intertwining maps of the
vector and covector representations, replacing the preliminary constructions and the auxiliary
modules used at present. [planned]

Three further commutations will be proved: of evaluation with a product in its left factor, of
evaluation with contraction in the order opposite to the one already available, and of two
evaluations of the same tensor. [planned]

The epsilon-epsilon identities hold at the level of tensors: contracting the Levi-Civita tensor
with itself over all four index pairs gives −24, and over the first three gives −6 times the
unit tensor of the lower color. [63][64][37]

A Euclidean Levi-Civita tensor will be added to carry the epsilon-epsilon contraction
identities, which at present are stated for the Euclidean symbol alone. [planned]

The conditions defining a tensor species will be extended with a relationship between the
metrics and the basis vectors. [planned]

## Further reading

- Formalization of physics index notation in Lean 4, Tooby-Smith. arXiv:2411.07667, https://arxiv.org/abs/2411.07667

## Lean declarations

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
