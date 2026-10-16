# Standard Model gauge group

The gauge group of the Standard Model is SU(3) × SU(2) × U(1), but only up to a quotient: a
finite central subgroup may be divided out, and which one is not settled by the physics known
so far. Both key data structures are therefore here — the full group, and the group obtained
for a given choice of quotient, by the sixth, second or third roots of unity, or by nothing at
all.

The API supplies the projections onto the three factors, the star structure, the embeddings of
the roots of unity as central subgroups, the quotient groups with their common quotient map,
and the characterization of that map's kernel. A separate file gives the U(1) and fundamental
SU(2) actions on the two-dimensional complex space the Higgs sector uses. The Higgs field API
builds on this group.

## Requirements

The key data structure is defined: the full gauge group, with its projections onto the three
factors and extensionality in them. [1]

The star operation on the gauge group is defined, and commutes with the three
projections. [2]

A unitary scalar embeds as a gauge-group element acting on all three factors, with its
projections identified. [3]

The sixth roots of unity embed as a central subgroup, constructed on each factor, with
membership characterized and normality recorded. [4]

The quotient of the gauge group by that subgroup is a group, with its projection. [5]

The subgroup of second roots of unity and its quotient are defined, with the inclusion into the
sixth-roots subgroup. [6]

The subgroup of third roots of unity and its quotient are defined, with the inclusion into the
sixth-roots subgroup. [7]

The second key data structure takes the quotient as a parameter: the type of quotient choices
is defined, and the gauge group, its central subgroup, the normality of that subgroup and its
inclusion into the sixth-roots subgroup are given uniformly in the choice. [8]

The quotient map out of the full gauge group is defined uniformly in that choice, computed on
each central embedding, with its kernel characterized. [9]

The U(1) representation and the fundamental SU(2) action on the two-dimensional complex space
of the Higgs sector are defined, and they commute. [10]

The gauge groups will carry a Lie group structure. Informal statements of both stand in the
source. [11][planned]

The center of the full gauge group will be characterized exactly; at present the central
subgroups are only shown to lie inside it. [planned]

The gauge bundle and the gauge transformations over spacetime will be defined. Informal
statements of both stand in the source. [12][planned]

The unbroken gauge group after electroweak symmetry breaking will be defined, using the Higgs
field. [planned]

The fermionic content of the Standard Model and its representations will be captured in a
structure. [planned]

## Further reading

- D. Tong, Line Operators in the Standard Model, JHEP 07 (2017) 104. https://arxiv.org/abs/1705.01853

## Lean declarations

1. Physlib/Particles/StandardModel/Basic.lean — `GaugeGroupI`, `toSU3`, `toSU2`, `toU1`, `ext`
2. Physlib/Particles/StandardModel/Basic.lean — `star_eq`, `star_toSU3`, `star_toSU2`,
   `star_toU1`
3. Physlib/Particles/StandardModel/Basic.lean — `ofU1Subgroup`, `ofU1Subgroup_toSU3`,
   `ofU1Subgroup_toSU2`, `ofU1Subgroup_toU1`
4. Physlib/Particles/StandardModel/Basic.lean — `gaugeGroupℤ₆UnitaryOfRoot`,
   `gaugeGroupℤ₆SU3OfRoot`, `gaugeGroupℤ₆SU2OfRoot`, `gaugeGroupℤ₆OfRoot`,
   `gaugeGroupℤ₆OfRoot_mem_center`, `gaugeGroupℤ₆Hom`, `gaugeGroupℤ₆SubGroup`,
   `mem_gaugeGroupℤ₆SubGroup_iff`, `gaugeGroupℤ₆SubGroup_le_center`,
   `gaugeGroupℤ₆SubGroup_normal`
5. Physlib/Particles/StandardModel/Basic.lean — `GaugeGroupℤ₆`, `mk`, `mk_gaugeGroupℤ₆OfRoot`
6. Physlib/Particles/StandardModel/Basic.lean — `gaugeGroupℤ₂RootToℤ₆Root`,
   `gaugeGroupℤ₂OfRoot`, `gaugeGroupℤ₂OfRoot_mem_center`, `gaugeGroupℤ₂Hom`,
   `gaugeGroupℤ₂SubGroup`, `mem_gaugeGroupℤ₂SubGroup_iff`,
   `gaugeGroupℤ₂SubGroup_le_gaugeGroupℤ₆SubGroup`, `gaugeGroupℤ₂SubGroup_le_center`,
   `gaugeGroupℤ₂SubGroup_normal`, `GaugeGroupℤ₂`
7. Physlib/Particles/StandardModel/Basic.lean — `gaugeGroupℤ₃RootToℤ₆Root`,
   `gaugeGroupℤ₃OfRoot`, `gaugeGroupℤ₃OfRoot_mem_center`, `gaugeGroupℤ₃Hom`,
   `gaugeGroupℤ₃SubGroup`, `mem_gaugeGroupℤ₃SubGroup_iff`,
   `gaugeGroupℤ₃SubGroup_le_gaugeGroupℤ₆SubGroup`, `gaugeGroupℤ₃SubGroup_le_center`,
   `GaugeGroupℤ₃`
8. Physlib/Particles/StandardModel/Basic.lean — `GaugeGroupQuot`, `GaugeGroup`, `subgroup`,
   `subgroup_le_center`, `subgroup_normal`, `subgroup_le_subgroup_ℤ₆`
9. Physlib/Particles/StandardModel/Basic.lean — `quotientMap`, `quotientMap_I_apply`,
   `quotientMap_ℤ₆_gaugeGroupℤ₆OfRoot`, `quotientMap_ℤ₂_gaugeGroupℤ₂OfRoot`,
   `quotientMap_ℤ₃_gaugeGroupℤ₃OfRoot`, `mem_subgroup_iff_quotientMap_eq_one`,
   `quotientMap_eq_iff`
10. Physlib/Particles/StandardModel/Representations.lean — `repU1Map`, `repU1`,
   `fundamentalSU2`, `repU1_fundamentalSU2_commute`
11. Physlib/Particles/StandardModel/Basic.lean — `gaugeGroupI_lie`, `gaugeGroup_lie`
12. Physlib/Particles/StandardModel/Basic.lean — `gaugeBundleI`, `gaugeTransformI`
