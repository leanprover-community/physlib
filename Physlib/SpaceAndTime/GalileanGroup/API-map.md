# Galilean group

The Galilean group is the group of transformations relating the descriptions two observers give
of non-relativistic space and time. An element records a spatial rotation, a boost velocity, a
translation of space and a translation of time, in any spatial dimension; it acts on a pair of
an instant and a point by rotating and boosting first, then translating.

The API gives that data structure, its group structure, its action, and the inclusions of the
subgroups it is assembled from: the Euclidean group, the orthogonal group, the rotations, the
space translations and the time translations.

## Built on

- Space — `Physlib/SpaceAndTime/Space`
- Time — `Physlib/SpaceAndTime/Time`
- Euclidean group — `Physlib/SpaceAndTime/Space/EuclideanGroup`

## Requirements

The key data structure is defined: a rotation, a boost velocity, a space translation and a time
translation taken together. [1]

Those transformations form a group, with the composite and the inverse computed componentwise
from the four pieces. [2]

That group will carry the structure of a Lie group. [planned]

The rotations include into the Galilean group. [3]

The space translations include into the Galilean group. [4]

The time translations include into the Galilean group. [5]

Everything is stated for an arbitrary spatial dimension, not only for three. [6]

The Galilean group acts on time and space together. [7]

The Euclidean group includes into the Galilean group. [8]

## Lean declarations

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
