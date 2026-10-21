# Lorentz Group

## Abstract (Alpha)

The Lorentz group is the group of real matrices Λ preserving the Minkowski metric η, those
satisfying Λ * dual Λ = 1 where dual Λ = η Λᵀ η. It is the symmetry group of Minkowski spacetime,
and is used throughout the library: Lorentz tensors, Weyl and Dirac fermions, and the
electromagnetic potential are all characterized by how they transform under it. The group sits as a
closed subgroup of the general linear group, contains the boosts and the rotations, admits several
equivalent membership conditions, and has distinguished subsets: the proper transformations, the
orthochronous ones, and the restricted Lorentz group where both conditions hold.

## Content (Alpha)

### The group

A Lorentz transformation is a matrix Λ satisfying Λ * dual Λ = 1, where the dual is taken with
respect to the Minkowski matrix. [1] The Lorentz transformations form a group under matrix
multiplication. [2] Equivalently, Λ is Lorentz exactly when dual Λ * Λ = 1, when its transpose
is Lorentz, when −Λ is Lorentz, or when Λᵀ η Λ = η. [6] The Lorentz group embeds as a closed
subgroup of the general linear group, by a closed embedding. [3] It is a Lie group, by Cartan's
closed subgroup theorem. [TODO] It is the symmetry group of Minkowski spacetime {1}, and Lorentz
tensors {2}, Weyl fermions {3} and Dirac fermions {4} are characterized by how they transform under
it. A standard introduction is Jaffe {5}.

### Boosts and rotations

Every boost is a Lorentz transformation. [4] Every rotation of space is a Lorentz
transformation. [5] Every member of the restricted Lorentz group is a boost composed with a
rotation. [10]

### Proper, orthochronous and restricted transformations

A Lorentz transformation is proper when its determinant is 1. [7] It is orthochronous when it
preserves the direction of time, its time-time component being non-negative. [8] The restricted
Lorentz group consists of the transformations that are both proper and orthochronous. [9] The
orthochronous Lorentz transformations are characterized topologically within the Lorentz group.
[TODO]

## Lean References

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
10. Physlib/Relativity/LorentzGroup/Restricted/FromBoostRotation.lean — `exists_boost_mul_rotation`,
   `toBoostRotation`

## References

1. SpaceTime API map — Physlib/SpaceAndTime/SpaceTime/API-map.md
2. Tensors API map — Physlib/Relativity/Tensors/API-map.md
3. Weyl Fermions API map — Physlib/Relativity/Fermions/Weyl/API-map.md
4. Dirac Fermions API map — Physlib/Relativity/Fermions/Dirac/API-map.md
5. A. Jaffe, *Lorentz Transformations, Rotations, and Boosts*,
   https://cdn.ku.edu.tr/cdn/files/amostafazadeh/phys517_518/phys517_2016f/Handouts/A_Jaffi_Lorentz_Group.pdf
