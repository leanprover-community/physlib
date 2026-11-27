# Orbital mechanics

## Abstract (Alpha)

A body of mass m orbits a central body of mass M under Newtonian gravity with constant G. On a
circular orbit of radius r the speed is fixed by the gravitational parameter G M alone,
v² = G M / r, and equals the radius times the angular rate. When both bodies move about their common
barycentre the period follows Kepler's third law with the total mass, P² G (M + m) = 4π² r³, and the
reflex speed of the central body about the barycentre is the radial-velocity semi-amplitude that
reveals a planet on an edge-on circular orbit. The specific orbital energy v² / 2 − G M / r is
negative on a circular orbit, where it equals half the potential energy per unit mass, and vanishes
at the escape speed √(2 G M / r), which exceeds the circular speed by a factor √2.

## Content (Alpha)

### System and configuration

The system is the gravitational constant G, the central mass M and the orbiting mass m, and a
configuration is the orbital radius r. [1] The circular speed, the specific orbital energy and the
escape speed use the gravitational parameter G M of the central body alone, the limit of a test
body with m ≪ M; the two-body period and the reflex motion use the total mass M + m. [1]

### Circular orbits

The circular speed at radius r is √(G M / r), with square G M / r. [2] It equals the radius times
the circular angular rate √(G M / r³). [3]

### The two-body period and the reflex motion

The period of a circular two-body orbit at separation r is 2π √(r³ / (G (M + m))), which satisfies
Kepler's third law P² G (M + m) = 4π² r³ {1}. [4] The central body circles the barycentre at
distance m r / (M + m), and its reflex speed, once round that circle per period, satisfies
K³ = 2π G m³ / (P (M + m)²); for a star with a planet on an edge-on circular orbit this is the
radial-velocity semi-amplitude {2}. [5]

### Energy and the escape speed

The specific orbital energy at speed v and radius r is v² / 2 − G M / r, and on a circular orbit it
is −(G M / r) / 2, half the potential energy per unit mass. [6] The escape speed √(2 G M / r) is
positive, its square is 2 G M / r, and the specific orbital energy vanishes there. [7] It is √2
times the circular speed at the same radius, so a body on a circular orbit moves more slowly than
the escape speed and is bound. [8]

### General orbits

On an orbit of semi-major axis a the vis-viva equation gives v² = G M (2 / r − 1 / a) {1}. [TODO]
The two-body problem reduces to the motion of a single body of reduced mass M m / (M + m) in the
relative coordinate {1}. [TODO] In a planar binary, the relative displacement sweeps out equal
signed areas in equal times within a collision-free interval. Its areal rate is half the signed
angular momentum per unit reduced mass. [9] Bound nonradial orbits are ellipses with the centre of
force at a focus, and their squared periods are proportional to a³ {1}. [TODO]

## Lean References

1. Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean — `VisViva`,
   `VisViva.ConfigurationSpace`
2. Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean — `VisViva.speedCircular`,
   `VisViva.speedCircular_sq`
3. Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean —
   `VisViva.speedCircular_eq_radius_mul_angularRate`
4. Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean — `VisViva.periodTwoBody`,
   `VisViva.periodTwoBody_sq`
5. Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean — `VisViva.reflexRadius`,
   `VisViva.reflexSpeed`, `VisViva.reflexSpeed_pow_three`
6. Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean — `VisViva.specificOrbitalEnergy`,
   `VisViva.specificOrbitalEnergy_speedCircular`
7. Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean — `VisViva.speedEscape`,
   `VisViva.speedEscape_sq`, `VisViva.speedEscape_pos`, `VisViva.specificOrbitalEnergy_speedEscape`
8. Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean —
   `VisViva.speedEscape_eq_sqrt_two_mul_speedCircular`,
   `VisViva.speedEscape_sq_eq_two_mul_speedCircular_sq`, `VisViva.speedCircular_lt_speedEscape`
9. PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/BinaryStar.lean —
   `binarySignedSweptArea_eq_of_gravity`, `binarySignedSweptArea_eq_of_eq_duration`

## References

1. Landau & Lifshitz, *Mechanics*, 3rd ed., Sections 13 and 15.
2. Perryman, *The Exoplanet Handbook*, 2nd ed., Chapter 2.
