# Lorentz Group

The Lorentz group is the group of matrices preserving the Minkowski metric, those satisfying
Λ * dual Λ = 1. It is the symmetry group of Minkowski spacetime, and it is used throughout the
library: Lorentz tensors, fermions and the electromagnetic potential are all defined by how
they transform under it.

The API gives the group itself, its realization as a closed subgroup of the general linear
group, the inclusions of boosts and of rotations, several equivalent conditions for membership,
and the distinguished subsets — the proper transformations, the orthochronous ones, and the
restricted Lorentz group where both conditions hold.

## Built on

- Minkowski matrix — `Physlib/Relativity/MinkowskiMatrix.lean`

## Requirements

The key data structure is defined: the Lorentz group, the matrices satisfying
Λ * dual Λ = 1. [1]

Those matrices form a group. [2]

The Lorentz group is a closed subgroup of the general linear group, by a closed
embedding. [3]

The Lorentz group will be a Lie group. This is blocked on Cartan's closed subgroup theorem,
which Mathlib does not yet have. [planned]

The boosts include into the Lorentz group. [4]

The rotations include into the Lorentz group. [5]

Several equivalent conditions for a matrix to be a Lorentz transformation are given. [6]

The proper Lorentz transformations are defined. [7]

The orthochronous Lorentz transformations are defined. [8]

The restricted Lorentz group is defined. [9]

The topological properties of the orthochronous Lorentz group will be proved. [planned]

Every member of the restricted Lorentz group will be shown to be a boost composed with a
rotation. [planned]

## Further reading

- Lorentz Transformations, Rotations, and Boosts, Jaffe. https://cdn.ku.edu.tr/cdn/files/amostafazadeh/phys517_518/phys517_2016f/Handouts/A_Jaffi_Lorentz_Group.pdf

## Lean declarations

1. Physlib/Relativity/LorentzGroup/Basic.lean — `LorentzGroup`
2. Physlib/Relativity/LorentzGroup/Basic.lean — `lorentzGroupIsGroup`
3. Physlib/Relativity/LorentzGroup/Basic.lean — `toGL_isClosedEmbedding`, `toGLSubgroup`,
   `toClosedSubgroup`
4. Physlib/Relativity/LorentzGroup/Boosts/Basic.lean — `boost`
5. Physlib/Relativity/LorentzGroup/Rotations.lean — `Rotations`
6. Physlib/Relativity/LorentzGroup/Basic.lean — `mem_iff_self_mul_dual`,
   `mem_iff_dual_mul_self`, `mem_iff_transpose`, `mem_iff_neg_mem`,
   `mem_iff_transpose_mul_minkowskiMatrix_mul_self`
7. Physlib/Relativity/LorentzGroup/Proper.lean — `IsProper`
8. Physlib/Relativity/LorentzGroup/Orthochronous/Basic.lean — `IsOrthochronous`
9. Physlib/Relativity/LorentzGroup/Restricted/Basic.lean — `restricted`
