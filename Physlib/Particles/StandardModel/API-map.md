# Standard Model gauge group

## Abstract (Alpha)

The gauge group of the Standard Model is SU(3) × SU(2) × U(1), but only up to a quotient: a finite
central subgroup may be divided out, and which one is not settled by the physics known so far. This
area therefore treats both the full group and the group obtained for a given choice of quotient, by
the sixth, second or third roots of unity, or by nothing at all, together with the projections onto
the three factors, the star structure, the roots of unity as central subgroups, the common quotient
map and its kernel, and the U(1) and fundamental SU(2) actions on the two-dimensional complex space
of the Higgs sector; the Higgs field builds on this group.

## Content (Alpha)

### The full gauge group

The full gauge group is SU(3) × SU(2) × U(1); it projects onto each of its three factors, and an
element is determined by its three projections. [1] Its star operation commutes with the three
projections. [2] A unitary scalar gives a gauge-group element acting on all three factors at
once, whose projections are known explicitly. [3] The gauge groups are Lie groups. [11][TODO]
The gauge bundle over spacetime and its global sections, the gauge transformations, are built
from the full gauge group. [12][TODO]

### Central subgroups and quotients

The sixth roots of unity embed in the gauge group as a central subgroup, built factor by factor;
membership in it has an explicit description, and it is normal. [4] The quotient of the gauge
group by that subgroup is a group, with its projection from the full group. [5] The second roots
of unity form a central subgroup contained in the sixth-roots subgroup, with its own
quotient. [6] So do the third roots of unity. [7] The center of the full gauge group is
characterized exactly, and not merely shown to contain these subgroups. [TODO]

The choice of quotient, which the physics known so far does not settle {1}, is itself a parameter,
ranging over the sixth, second and third roots of unity and the trivial quotient; for each choice
there is a gauge group and a central subgroup, normal and contained in the sixth-roots subgroup. [8]
A single quotient map out of the full gauge group serves every choice: it is computed on each
central embedding, and its kernel is exactly the chosen subgroup. [9]

### Higgs-sector representations and beyond

On the two-dimensional complex space of the Higgs sector {2}, U(1) acts by a representation and
SU(2) by its fundamental action, and the two commute. [10] Electroweak symmetry breaking by the
Higgs field leaves an unbroken gauge group. [TODO] The fermionic content of the Standard Model,
together with its representations of the gauge group, forms a single structure. [TODO]

## Lean References

1. Physlib/Particles/StandardModel/GaugeGroup/Basic.lean — `GaugeGroupI`, `toSU3`, `toSU2`, `toU1`, `ext`
2. Physlib/Particles/StandardModel/GaugeGroup/Basic.lean — `star_eq`, `star_toSU3`, `star_toSU2`,
   `star_toU1`
3. Physlib/Particles/StandardModel/GaugeGroup/Basic.lean — `ofU1Subgroup`, `ofU1Subgroup_toSU3`,
   `ofU1Subgroup_toSU2`, `ofU1Subgroup_toU1`
4. Physlib/Particles/StandardModel/GaugeGroup/Basic.lean — `gaugeGroupℤ₆UnitaryOfRoot`,
   `gaugeGroupℤ₆SU3OfRoot`, `gaugeGroupℤ₆SU2OfRoot`, `gaugeGroupℤ₆OfRoot`,
   `gaugeGroupℤ₆OfRoot_mem_center`, `gaugeGroupℤ₆Hom`, `gaugeGroupℤ₆SubGroup`,
   `mem_gaugeGroupℤ₆SubGroup_iff`, `gaugeGroupℤ₆SubGroup_le_center`,
   `gaugeGroupℤ₆SubGroup_normal`
5. Physlib/Particles/StandardModel/GaugeGroup/Basic.lean — `GaugeGroupℤ₆`, `mk`, `mk_gaugeGroupℤ₆OfRoot`
6. Physlib/Particles/StandardModel/GaugeGroup/Basic.lean — `gaugeGroupℤ₂RootToℤ₆Root`,
   `gaugeGroupℤ₂OfRoot`, `gaugeGroupℤ₂OfRoot_mem_center`, `gaugeGroupℤ₂Hom`,
   `gaugeGroupℤ₂SubGroup`, `mem_gaugeGroupℤ₂SubGroup_iff`,
   `gaugeGroupℤ₂SubGroup_le_gaugeGroupℤ₆SubGroup`, `gaugeGroupℤ₂SubGroup_le_center`,
   `gaugeGroupℤ₂SubGroup_normal`, `GaugeGroupℤ₂`
7. Physlib/Particles/StandardModel/GaugeGroup/Basic.lean — `gaugeGroupℤ₃RootToℤ₆Root`,
   `gaugeGroupℤ₃OfRoot`, `gaugeGroupℤ₃OfRoot_mem_center`, `gaugeGroupℤ₃Hom`,
   `gaugeGroupℤ₃SubGroup`, `mem_gaugeGroupℤ₃SubGroup_iff`,
   `gaugeGroupℤ₃SubGroup_le_gaugeGroupℤ₆SubGroup`, `gaugeGroupℤ₃SubGroup_le_center`,
   `GaugeGroupℤ₃`
8. Physlib/Particles/StandardModel/GaugeGroup/Basic.lean — `GaugeGroupQuot`, `GaugeGroup`, `subgroup`,
   `subgroup_le_center`, `subgroup_normal`, `subgroup_le_subgroup_ℤ₆`
9. Physlib/Particles/StandardModel/GaugeGroup/Basic.lean — `quotientMap`, `quotientMap_I_apply`,
   `quotientMap_ℤ₆_gaugeGroupℤ₆OfRoot`, `quotientMap_ℤ₂_gaugeGroupℤ₂OfRoot`,
   `quotientMap_ℤ₃_gaugeGroupℤ₃OfRoot`, `mem_subgroup_iff_quotientMap_eq_one`,
   `quotientMap_eq_iff`
10. Physlib/Particles/StandardModel/Representations.lean — `repU1Map`, `repU1`,
   `fundamentalSU2`, `repU1_fundamentalSU2_commute`
11. Physlib/Particles/StandardModel/GaugeGroup/Basic.lean — `gaugeGroupI_lie`, `gaugeGroup_lie`
12. Physlib/Particles/StandardModel/GaugeGroup/Basic.lean — `gaugeBundleI`, `gaugeTransformI`

## References

1. D. Tong, *Line Operators in the Standard Model*, JHEP 07 (2017) 104, arXiv:1705.01853,
   https://arxiv.org/abs/1705.01853
2. Higgs field API map — Physlib/Particles/StandardModel/HiggsBoson/API-map.md
