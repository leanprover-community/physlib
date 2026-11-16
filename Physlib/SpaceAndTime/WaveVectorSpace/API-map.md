# Wavevector space

## Abstract (Alpha)

A wavevector describes the spatial variation of a wave’s phase.
Wavevectors form a real vector space, equipped with a norm and an inner product,
in which functions of wavevector can be differentiated.
Physically, wavevector space is reciprocal to position space:
a wavevector pairs with a spatial displacement to give a phase difference.
This pairing connects wavevectors to plane waves and to the Fourier transform,
which expresses a spatial field in terms of its wavevector components.

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
The gradient, divergence, laplacian and curl are defined for functions of wavevector. [TODO]

### Duality with Space

There is a natural pairing of wavevector space with spatial displacements in Space {1}:
for a given wavevector $k$ and point in space $x$ the pairing $k\cdot x = \sum_i k_ix^i$
gives the phase difference relative to some fixed reference point. [6]
Fixing a wavevector $k$ gives its dual functional $x \mapsto k\cdot x$ on space and similarly
fixing a displacement $x$ gives its dual functional $k \mapsto k\cdot x$ on wavevector space. [7]
Changing the reference point changes the phase at all points in space by the same amount. [TODO]

### Fourier transforms

The Fourier transform takes a suitably nice function of space to a function of wavevector,
resolving its spatial dependence into plane-wave components; the inverse Fourier transform
reconstructs the spatial function from those components. [8]
The transform and its inverse have a consistent choice of normalization
and preserve inner products up to the corresponding normalization factor. [TODO]
The Fourier transform maps derivatives with respect to space to multiplication by wavevector
and *vice versa*, under suitable regularity and decay assumptions. [TODO]

## Lean References

1. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `WaveVectorSpace`
2. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `instZero`, `instModuleReal`
3. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `instNormedAddCommGroup`,
   `instInnerProductSpaceReal`, `equivEuclideanSpace`
4. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `basis`, `coord`, `coordCLM`
5. Physlib/SpaceAndTime/WaveVectorSpace/Derivatives/Basic.lean — `deriv`, `deriv_add`,
   `deriv_const_smul`, `deriv_smul`, `deriv_pow`
6. Physlib/SpaceAndTime/WaveVectorSpace/DualPairing.lean — `pairingCLM`
7. Physlib/SpaceAndTime/WaveVectorSpace/DualPairing.lean — `WaveVectorSpace.dual`, `Space.dual`
8. Physlib/SpaceAndTime/WaveVectorSpace/Fourier.lean — `fourierIntegral`, `fourierIntegralInv`

## References

1. Space API map — Physlib/SpaceAndTime/Space/API-map.md
