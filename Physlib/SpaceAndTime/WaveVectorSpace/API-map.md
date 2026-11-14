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

## Lean References

1. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `WaveVectorSpace`
2. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `instZero`, `instRealModule`
3. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `instNormedAddCommGroup`,
   `instInnerProductReal`, `equivEuclideanSpace`
4. Physlib/SpaceAndTime/WaveVectorSpace/Basic.lean — `basis`, `coord`, `coordCLM`

## References
