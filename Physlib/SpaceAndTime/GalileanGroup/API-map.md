# Galilean group

## Abstract (Alpha)

The Galilean group is the group of transformations relating the descriptions two observers give
of non-relativistic space and time. An element records a spatial rotation, a boost velocity, a
translation of space and a translation of time, in any spatial dimension; it acts on a pair of
an instant and a point by rotating and boosting first, then translating, and it contains the
Euclidean group, the orthogonal group, the rotations, the space translations and the time
translations as subgroups.

## Content (Alpha)

A Galilean transformation consists of four pieces of data: a rotation, a boost velocity, a
translation of space {1} and a translation of time {2}. [1]
The spatial dimension is arbitrary; nothing is special to three dimensions. [6]

Galilean transformations form a group, with the identity, the composite and the inverse computed
explicitly from the four pieces. [2] This group is a Lie group. [TODO]

The Galilean group acts on time and space together: an element sends a pair of an instant and a
point to the pair obtained by rotating and boosting the point, then translating both. [7]

The Galilean group is assembled from familiar subgroups, each of which includes into it. The
rotations include into the Galilean group, as do the elements of the full orthogonal group. [3]
The space translations include into the Galilean group. [4] The time translations include into
the Galilean group. [5] More generally, the Euclidean group of space, the transformations
combining a rotation and a translation of space, includes into the Galilean group. [8]

## Lean References

1. Physlib/SpaceAndTime/GalileanGroup/Basic.lean — `GalileanGroup`, `rotation`, `velocity`,
   `spaceTranslation`, `timeTranslation`
2. Physlib/SpaceAndTime/GalileanGroup/Basic.lean — `One (GalileanGroup d)`,
   `Mul (GalileanGroup d)`, `Inv (GalileanGroup d)`, `Group (GalileanGroup d)`, `one_rotation`,
   `one_velocity`, `one_spaceTranslation`, `one_timeTranslation`, `mul_rotation`,
   `mul_velocity`, `mul_spaceTranslation`, `mul_timeTranslation`, `inv_rotation`,
   `inv_velocity`, `inv_spaceTranslation`, `inv_timeTranslation`
3. Physlib/SpaceAndTime/GalileanGroup/Basic.lean — `rotation.incl : EuclideanGroup.RotationGroup d →* GalileanGroup d`,
   `orthogonal.incl`, `ofOrthogonal`
4. Physlib/SpaceAndTime/GalileanGroup/Basic.lean — `spaceTranslation.incl`,
   `spaceTranslationGroup.incl`, `ofSpaceTranslation`
5. Physlib/SpaceAndTime/GalileanGroup/Basic.lean — `timeTranslation.incl : Multiplicative Time →* GalileanGroup d`,
   `ofTimeTranslation`
6. Physlib/SpaceAndTime/GalileanGroup/Basic.lean — `GalileanGroup`
7. Physlib/SpaceAndTime/GalileanGroup/Basic.lean — `actSpace`, `act`,
   `MulAction (GalileanGroup d) (Time × Space d)`, `smul_fst`, `smul_snd`, `smul_mk`
8. Physlib/SpaceAndTime/GalileanGroup/Basic.lean — `euclidean.incl : EuclideanGroup d →* GalileanGroup d`,
   `ofEuclidean`

## References

1. Space API map — Physlib/SpaceAndTime/Space/API-map.md
2. Time API map — Physlib/SpaceAndTime/Time/API-map.md
