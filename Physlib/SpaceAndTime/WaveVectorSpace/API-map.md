# Wavevector space

## Abstract (Alpha)

## Content (Alpha)

### Wavevectors and their basic structure

A wavevector is identified by its $d$ real coordinates. [1]
Wavevector space has a distinguished zero and is a vector space over the reals:
wavevectors may be added, subtracted and multiplied by real numbers. [2]
It has both a norm and inner product structure with which it is isometric
to standard $d$-dimensional Euclidean space. [3]
It has an orthonormal set of basis vectors, and for each basis vector
there is a corresponding coordinate function given by orthogonal projection. [4]
Wavevectors carry units of inverse-length and are rescaled
under a change of inverse-length unit. [TODO]

### Derivatives

Functions from wavevector space into a normed space can be differentiated along
the coordinate directions; the partial derivatives satisfy the usual linearity properties,
product rule and power rule. [5]
The gradient, divergence, laplacian and curl for functions of wavevector are defined. [TODO]

### Duality with Space

There is a natural pairing of wavevector space with spatial displacements in Space {1}:
for a given wavevector $k$ and point in space $x$ the pairing $k\cdot x = \sum_i k_ix^i$
gives the phase difference relative to some fixed reference point. [6]
Fixing a wavevector $k$ gives its dual functional $x \mapsto k\cdot x$ on space and similarly
fixing a displacement $x$ gives its dual functional $k \mapsto k\cdot x$ on wavevector space. [7]
Changing the reference point changes the phase at all points in space by the same amount. [TODO]


## Lean References

1. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `WaveVectorSpace`
2. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `instZero`, `instRealModule`
3. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `instNormedAddCommGroup`,
   `instInnerProductReal`, `equivEuclideanSpace`
4. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `basis`, `coord`, `coordCLM`
5. Physlib/SpaceAndTime/WaveVectorSpace/Derivatives/Basic.lean — `deriv`, `deriv_add`,
   `deriv_const_smul`, `deriv_smul`, `deriv_pow`
6. Physlib/SpaceAndTime/WaveVectorSpace/DualPairing.lean — `pairingCLM`
7. Physlib/SpaceAndTime/WaveVectorSpace/DualPairing.lean — `WaveVectorSpace.dual`, `Space.dual`

## References

1. Space API map — Physlib/SpaceAndTime/Space/API-map.md
