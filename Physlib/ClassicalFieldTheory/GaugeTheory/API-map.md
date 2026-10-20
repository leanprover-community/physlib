# Gauge theory

## Abstract

A gauge theory is a field theory whose Lagrangian is invariant under transformations that may be
chosen independently at each point of spacetime. Globally such a theory is described by a principal
bundle whose structure group is the gauge group, with the gauge field a connection on that bundle
and the matter fields sections of associated vector bundles carrying representations of the gauge
group. Locally, which is how gauge theories are used in practice, a Lagrangian density sees a gauge
transformation only through its Taylor series at the point in question, so the local content of the
theory is carried by the jets of gauge transformations at a single point, and is built in layers
from them. Both pictures specialize to electromagnetism, with gauge group U(1), and to the Standard
Model, with gauge group SU(3) × SU(2) × U(1).

## Content (Alpha)

### Geometric formulation

Geometrically a gauge theory is a principal bundle whose structure group is the gauge group, with
the gauge field a connection on that bundle and the matter fields sections of associated vector
bundles. [TODO]

### Local formulation

A Lagrangian density at a point x depends on the fields and on finitely many of their derivatives
at x. Whether it is gauge invariant therefore depends on a gauge transformation only through the
Taylor series of that transformation at x, its jet. The local formulation takes these jets as the
primitive notion. It is the formulation used in practice, and it needs none of the choices that the
geometric one does, in particular no regularity class for the fields on a principal bundle.

The local theory is built in layers, each taking the structure of the previous layer as input and
proving its results for an arbitrary instance of that structure. The bottom layer is the gauge data
of the jets at a point, described below. Above it sit the notion of a species of field on which
such data act, with matter fields and the connection as the two instances [16][17]; the field
content of a theory, a finite family of species [18]; the algebra of formal field symbols that a
field content generates, in which a Lagrangian is written [19]; and inside that algebra the
covariant subalgebra, on which gauge jets act through their values alone, so that classifying the
invariants of a given mass dimension becomes ordinary invariant theory [20]. Only the bottom layer
is in Physlib; the layers above it are in PhyslibAlpha, and move into Physlib as they are
reviewed.

### Local gauge data

For U(1) a gauge transformation is u(x) = exp(i θ(x)). Its jet is the power series of u in the
coordinates, a unitary formal series; its value at the base point is u(0) ∈ U(1); and its
Maurer–Cartan form ω_μ = i (∂_μ u) u⁻¹ = −∂_μ θ is exactly the shift of the gauge field,
A_μ ↦ A_μ + ω_μ. For SU(n) the same holds with n × n matrices of formal series, and ω_μ is a
traceless hermitian matrix. Local gauge data abstract this example. [9]

The data consist of four types — the gauge group G, its Lie algebra 𝔤, and their jet counterparts
G_J and 𝔤_J, a Lie algebra over ℝ — together with the maps a transformation law is built from:
evaluation at the base point and the inclusion of constants, on the group and on the Lie algebra;
the formal derivatives ∂_μ and multiplication by the coordinates x_μ on 𝔤_J; the adjoint action
Ad_U of a gauge jet on Lie algebra jets; and the Maurer–Cartan form ω_μ(U). They also record the
rules these maps satisfy in the example, which is what makes everything proved from them hold for
every gauge group at once.

The data are always passed explicitly rather than found by instance search, because the four types
do not determine them: the jets of a second group over the same gauge group would be a second,
equally canonical choice.

### The rules of the gauge data

Among the rules are the Leibniz rules
∂_μ ⁅a, b⁆ = ⁅∂_μ a, b⁆ + ⁅a, ∂_μ b⁆ and ∂_μ (x_ν a) = x_ν ∂_μ a + δ_μν a; the cocycle law
ω_μ(UV) = ω_μ(U) + Ad_U ω_μ(V), which says that transforming A_μ by V and then by U is the same as
transforming it by UV; and ∂_μ ω_ν(U) − ∂_ν ω_μ(U) + ⁅ω_μ(U), ω_ν(U)⁆ = 0, which says that a
pure-gauge field has vanishing field strength. [9]

The rules are what a transformation law needs. A gauge field A_μ is Lie algebra valued and
transforms as A_μ ↦ Ad_U A_μ + ω_μ(U), the inhomogeneous term being what makes it a gauge field
rather than a matter field; a Lagrangian also involves its derivatives, as in the field strength
F_μν = ∂_μ A_ν − ∂_ν A_μ + ⁅A_μ, A_ν⁆ with ⁅A, B⁆ = i (AB − BA), which is why the formal
derivatives and the coordinate multiplications are part of the data. Nothing in the layer mentions
fields or Lagrangians; every later layer takes the data as input.

### Properties of the gauge jets

Every g ∈ G is the value at the base point of its constant jet, so evaluation G_J → G is surjective
and the inclusion of constants G → G_J is injective; the same holds for 𝔤_J → 𝔤 and 𝔤 → 𝔤_J. [10]
Applied to constant jets, the rules show that Ad_g is a Lie algebra automorphism of 𝔤 for every
g ∈ G, and that ∂_μ commutes with the adjoint action of the constant jet of g. [11]

For a multiset s of directions, the iterated derivative ∂_s applies ∂_μ once for each μ in s. It
satisfies ∂_(s + t) = ∂_s ∂_t and the iterated Leibniz rule ∂_s ⁅a, b⁆ = Σ ⁅∂_s₁ a, ∂_s₂ b⁆, the
sum running over the ways of splitting s as s₁ + s₂. If s is non-empty then ∂_s c = 0 for every
constant c ∈ 𝔤, and ∂_s commutes with the adjoint action of a constant jet. [12] The value
(∂_s (x_μ a))(x) is the number of times μ occurs in s, multiplied by (∂_(s − μ) a)(x). [13]

Three consequences of the rules are what the layers above need. The Taylor coefficients of Ad_U
obey a Leibniz formula, which is how a gauge jet moves the derivatives of a field. [21] The
Maurer–Cartan form has a symmetrized counterpart, a smaller family of coefficients from which all
Taylor coefficients of ω can be recovered, and the structural equation holds at the base point to
all orders. [22] The jets agreeing with the identity to order n form a filtration by normal
subgroups, and such a jet shifts only the first n derivatives of the gauge field. [23]

### Faithful and free jets

The rules do not say that G_J really consists of Taylor series, so the two properties that express
this are stated separately. Faithfulness says that a jet is determined by its Taylor coefficients
[24], and in a faithful package the Maurer–Cartan form vanishes exactly on the constant jets [22].
Freeness says in addition that every choice of coefficients is realized by some jet, so that the
symmetrized Maurer–Cartan data are free coordinates on the pure jets. [25] Freeness is what later
shows that the gauge field enters an invariant only through its field strength, as a polynomial in
its covariant derivatives: free gauge jets are rich enough to remove every other combination of
derivatives of A_μ. [34] That the Taylor series of the smooth gauge transformations of U(1) and
SU(n) do form the corresponding jet group, so that these two properties hold of the smooth theory
and not only of the formal one, rests on Borel's theorem for spacetime. [TODO] A constructor taking
local gauge data from a Lie group and its Lie algebra is not yet available. [TODO]

### Concrete gauge groups

Concrete gauge groups come from a presentation by matrices: a statement that the four types sit
inside matrices over the ring of formal series and that every map of the data is the matrix one.
From a presentation the rules, faithfulness and a criterion for freeness are each proved once. [26]
Filling one in gives U(1), as 1 × 1 matrices [27], and SU(n) [28]; the product of two local gauge
data [29] and the data of a list of factor symbols [30] then give any group built from these,
SU(3) × SU(2) × U(1) among them, assembled from a list of three factor symbols. Faithfulness and
freeness pass along all of these constructions, so each assembled group inherits both. [30]

### Factors and morphisms

Charges are read off one factor at a time, as in "a doublet of SU(2) with hypercharge −3". A factor
of local gauge data records how its gauge jets project onto a single U(1) or SU(n); the data of a
list of factor symbols carry a canonical family of them. [31] A morphism of local gauge data
consists of maps G → G', 𝔤 → 𝔤', G_J → G'_J and 𝔤_J → 𝔤'_J compatible with all of the operations
above. It intertwines the adjoint actions on 𝔤 and 𝔤', and commutes with ∂_s. [14] Morphisms have
identities and compose. [15] A factor of the target of a morphism pulls back to one of the
source [31], and the projections of a product are morphisms [29], which is how the factors of
SU(3) × SU(2) × U(1) are obtained from those of its three pieces. A homomorphism of Lie groups
induces a morphism of local gauge data. [TODO]

The Standard Model gauge group is exactly that assembly, and is free because each of its three
factors is. [32] A model contributes only such a list and a table of fields with their charges;
everything else about it is inherited from the layers. [33]

### The abelian theory

In electromagnetism the gauge field is the electromagnetic potential {1}, a Lorentz-vector-valued
field on spacetime, and its field strength is built from that potential. [2][3] A gauge
transformation shifts the potential by the gradient of a scalar {2}, and the pure-gauge potential is
the shift of zero. [4] Gauge transformations leave the field strength invariant. [5] In particular a
pure-gauge potential has vanishing field strength, and this relies on raising the index of the
gradient with the Minkowski metric: the bare gradient of a scalar can have nonzero field
strength. [6] Gauge transformations compose: the trivial shift is the identity and successive shifts
add. [7] They commute with the action of the Lorentz group. [8]

### The Standard Model gauge group

The Standard Model gauge group {3} is SU(3) × SU(2) × U(1), with its projections onto the three
factors and a central discrete subgroup of sixth roots of unity. [1]

### The non-abelian theory

A general gauge theory {4} admits an arbitrary Lie group as its structure group. [TODO] Its gauge
field takes values in the Lie algebra of that group. [TODO] Matter fields carry a gauge-covariant
derivative with a definite transformation law. [TODO] The gauge field has a Yang–Mills
curvature. [TODO] That curvature transforms covariantly under gauge transformations. [TODO]
The Yang–Mills action yields the Yang–Mills field equations. [TODO] A gauge field determines
parallel transport along paths and holonomy around loops. [TODO] Progress on this API is tracked
in a GitHub issue {5}.

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
16. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/MatterField/Basic.lean — `MatterField`,
   `MatterField.PureJetsActTrivially`, `MatterField.GaugeLorentzCompatible`
17. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/GaugeBoson/Realization/Basic.lean —
   `GaugeAlgebraRealization`, `lorentz_apply`, `gauge_apply_deriv`
18. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/GaugeFieldData/Basic.lean — `GaugeFieldData`,
   `GaugeFieldData.FermionValue`, `GaugeFieldData.BosonValue`
19. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalField/Basic.lean —
   `GaugeFieldData.LocalFieldAlgebra`, `GaugeFieldData.adjoin_generators_eq_top`,
   `GaugeFieldData.Assignment`
20. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalCovField/Basic.lean —
   `GaugeFieldData.LocalCovFieldAlgebra`, `LocalCovFieldAlgebra.repJet`,
   `LocalCovFieldAlgebra.repJet_eq_repValue_eval`
21. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/AdjointCoeff.lean —
   `LocalGaugeData.adjointCoeff`, `LocalGaugeData.evalLie_iteratedDeriv_adjointJ`,
   `LocalGaugeData.adjointCoeff_mul`, `LocalGaugeData.adjointDualCoeff`
22. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/MaurerCartan.lean —
   `LocalGaugeData.symmetrizedMaurerCartanForm`,
   `LocalGaugeData.evalLie_iteratedDeriv_maurerCartan_structure`,
   `LocalGaugeData.evalLie_iteratedDeriv_maurerCartan_eq_of_symmetrized_eq_all`,
   `LocalGaugeData.maurerCartan_eq_zero_iff`
23. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Truncation.lean —
   `LocalGaugeData.truncationKer`, `LocalGaugeData.truncationKer_normal`,
   `LocalGaugeData.mem_truncationKer_zero_iff`, `LocalGaugeData.truncationProjZero`,
   `LocalGaugeData.radial`
24. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Basic.lean —
   `LocalGaugeData.Faithful`, `LocalGaugeData.evalLie_iteratedDeriv_bracket_congr`
25. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Truncation.lean —
   `LocalGaugeData.Free`, `LocalGaugeData.symmetrizedMaurerCartanCoeff_injective`,
   `LocalGaugeData.symmetrizedMaurerCartanCoeff_surjective`,
   `LocalGaugeData.mem_truncationKer_iff_symmetrizedMaurerCartanCoeff_eq_zero`
26. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/MatrixJets.lean —
   `LocalGaugeData.MatrixJets`, `LocalGaugeData.MatrixJets.toLocalGaugeData`,
   `LocalGaugeData.MatrixJets.faithful`, `LocalGaugeData.MatrixJets.free`
27. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/U1.lean —
   `LocalGaugeData.u1MatrixJets`, `LocalGaugeData.u1`, `LocalGaugeData.u1Factor`,
   `LocalGaugeData.instFaithfulU1`, `LocalGaugeData.instFreeU1`
28. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/SU/Basic.lean —
   `LocalGaugeData.suMatrixJets`, `LocalGaugeData.su`, `LocalGaugeData.suFactor`,
   `LocalGaugeData.instFaithfulSU`, `LocalGaugeData.instFreeSU`
29. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Prod.lean —
   `LocalGaugeData.prod`, `LocalGaugeData.Hom.fst`, `LocalGaugeData.Hom.snd`,
   `LocalGaugeData.instFaithfulProd`, `LocalGaugeData.instFreeProd`
30. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/OfFactors.lean —
   `LocalGaugeData.FactorSpec`, `LocalGaugeData.ofFactors`, `LocalGaugeData.Factors.factors`,
   `LocalGaugeData.instFreeOfFactors`
31. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/LocalGaugeData/Factor.lean —
   `LocalGaugeData.U1Factor`, `LocalGaugeData.SUFactor`, `LocalGaugeData.Factor`,
   `LocalGaugeData.Factors`, `LocalGaugeData.Factors.comap`
32. PhyslibAlpha/Particles/StandardModel/GaugeGroup/LocalGaugeData.lean —
   `StandardModel.localGaugeData`, `StandardModel.instFreeLocalGaugeData`
33. PhyslibAlpha/Particles/StandardModel/Basic.lean — `StandardModel.Model.gauge`,
   `StandardModel.Model.gaugeData`, `StandardModel.Model.factors`, `StandardModel.Model.table`
34. PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/GaugeBoson/Realization/Symmetrized.lean —
   `GaugeAlgebraRealization.invariant_mem_adjoin_fieldStrength`,
   `GaugeAlgebraRealization.exists_repGauge_symmetrizedDeriv_shift`,
   `GaugeAlgebraRealization.mem_adjoin_symSymbolsLE_of_repGauge_eq`

## References

1. Electromagnetic Potential API map — Physlib/Electromagnetism/Kinematics/API-map.md
2. Wikipedia, Mathematical descriptions of the electromagnetic field, Gauge freedom,
   https://en.wikipedia.org/wiki/Mathematical_descriptions_of_the_electromagnetic_field#Gauge_freedom
3. Standard Model gauge group API map — Physlib/Particles/StandardModel/API-map.md
4. Wikipedia, Gauge theory, https://en.wikipedia.org/wiki/Gauge_theory
5. Physlib GitHub issue #859, https://github.com/leanprover-community/physlib/issues/859
