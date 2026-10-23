# TimeAndSpace

## Abstract (Alpha)

Euclidean space-time, the arena of non-relativistic physics, is an instant of time together with
a point of d-dimensional space, and nothing more: in the non-relativistic setting no symmetry the
theory respects mixes the two factors, so the product is the whole story. It has projections onto
the two factors that do not increase distances, an action of the Euclidean group on its points and
on the Schwartz maps out of it, and time and space derivatives that commute, together with the
characterisation of the functions that are constant in one of the two directions.

## Content (Alpha)

A point of Euclidean space-time is a pair of an instant of time {1} and a point of d-dimensional
space {2}. [1] Space-time projects onto its time and its space
factor, continuously and linearly, and each projection moves a pair of points no further apart
than they were. [2]

The Euclidean group of space acts on space-time, each element as an isometry which splits into a
linear part and a translation. [3] That action carries over to the Schwartz maps out of
space-time, where each element acts injectively and surjectively. [4]

Differentiating a function on space-time in time and differentiating it in space commute, and
the time derivative commutes with the curl. [5] A function on space-time whose time derivative
vanishes depends only on the point of space, one whose space derivative vanishes depends only on
the instant, and one with both vanishing is constant. [6]

## Lean References

1. Physlib/SpaceAndTime/TimeAndSpace/Basic.lean — `TimeAndSpace (d : ℕ := 3)`
2. Physlib/SpaceAndTime/TimeAndSpace/Basic.lean — `time`, `space`, `time_apply`, `space_apply`,
   `dist_time_le`, `dist_space_le`
3. Physlib/SpaceAndTime/TimeAndSpace/EuclideanGroup/Action.lean — `smul_mk`, `fst_smul`,
   `snd_smul`, `time_smul`, `space_smul`, `dist_smul`, `isometry_smul`, `antilipschitz_smul`,
   `actionLinearMap`, `actionTranslation`
4. Physlib/SpaceAndTime/TimeAndSpace/EuclideanGroup/SchwartzAction.lean — `schwartzEuclideanAction`,
   `schwartzEuclideanAction_apply`, `schwartzEuclideanAction_mul_apply`,
   `schwartzEuclideanAction_injective`, `schwartzEuclideanAction_surjective`
5. Physlib/SpaceAndTime/TimeAndSpace/Basic.lean — `fderiv_time_commute_fderiv_space`,
   `time_deriv_comm_space_deriv`, `time_deriv_curl_commute`
6. Physlib/SpaceAndTime/TimeAndSpace/Basic.lean — `space_fun_of_time_deriv_eq_zero`,
   `time_fun_of_space_deriv_eq_zero`, `const_of_time_deriv_space_deriv_eq_zero`

## References

1. Time API map — Physlib/SpaceAndTime/Time/API-map.md
2. Space API map — Physlib/SpaceAndTime/Space/API-map.md
