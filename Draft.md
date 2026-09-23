# Title: Formalization of the Standard Model
authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith

JTS: (Author list alphabetical by last name matching conventions in this area.)

## Abstract

The Standard Model of particle physics is our most successful theory of elementary physics. The key ingredient is the Standard Model Lagrangian. We formalize this in the interactive theorem prover Lean 4. This opens the door to .....

## 1. Introduction

The Standard Model of particle physics consists of the gauge group `G := SU(3) × SU(2) × U(1)` acting on a matter content consisting of 45 Weyl-fermions which collect into 15 irreducible representations of `G`, conventionally written as `Q_i`, `u_i`, `d_i`, `L_i`, and `e_i` for `i ∈ {0, 1, 2}`. The gauge group itself contributes the gauge bosons `G^a_μ`, `W^a_μ` and `B^a_μ`. There is also the Higgs boson `H` which is a complex scalar.

At each point `x` in space the Lagrangian is a polynomial function in the values of these fields at `x` as well as all of their derivatives at `x` which is invariant under the local action of the gauge group and the (global) action of the Lorentz group. The aim of this project is to formally verify that the only terms which can appear in such a Lagrangian are those known to appear in the SM Lagrangian, up-to total derivatives. In this sense we 'formally verify the Standard Model'.

Along the way we will also prove another theorem about the SM Lagrangian. In any oder of an EFT expansion gauge invariance implies that the lagrangian can be written as a polynomial in terms of just the field strengths, the matter fields, including the Higgs and their covariant derivatives. In other words, the gauge bosons must come packaged as a field strength or a covariant derivative. After this, only the global action of the gauge group matters for invariance.

Of course, there is no question of the actual correctness of these theorems. Thus we want the reader of this project to take away two things: 1) That we are now at a stage where we can formally verify the standard model Lagrangian, and 2) That we have built a reusable API so that one can formally verify (with the help of AI or by hand) other similar problems in high-energy physics, such as EFT expansions, or allowed terms in BSM theories.



## 2. Overview


The basic ingredient of a gauge theory is the
underlying gauge group. The full gauge group
of a theory is usually encoded by some class
of functions from spacetime to the global
gauge group `G₀`. Physicists are usually agnostic
about precisely what 'class' should to be considered.
The reason for this, is that physicists usually only
care about the local action of the full gauge group on the fields.
For such a local action, one only needs certain bits of information
about the whole gauge group, and in particular only
can be pretty agnostic about the class of functions used.

The primiary role of the type `LocalGaugeData G 𝔤 G₀ 𝔤J` is to encode exactly this
local gauge data needed. Starting with the input data.
The group `G₀` represents the global gauge group of the theory.
The the Standard Model, this is `SU(3) × SU(2) × U(1)` (here we ignore
the possibility of discrete quotients).  The Lie algebra `𝔤`
is the Lie algebra of the global gauge group `G₀`.

The group `GJ` is slightly more complicated. Locally, at
a point `x` in spacetime, the
full gauge group appears through its action on fields
and finite-order derivatives. This action only
depends on the value of a gauge transformation
and its finite derivatives at the point `x`. In
otherwords, the possible taylor series at the point `x`.
If we assume that all smooth functions are valid gauge transformations
(the only time we make an assumption about the underlying class
of fields), then Borel's theorem tells us that every
possible taylor series (within the
constraints of the group) can arise from some smooth gauge transformation
(even if they have convergence zero). All such taylor
series form a group, which is precisely the local gauge group `GJ`.
How best to define `GJ` best depends on the group `G₀` and thus,
we include it here as input data.

The Lie algebra `𝔤J` is to `𝔤` what `GJ` is to `G₀`.

Let `G₀` be `SU(2)`, so that `𝔤` is the traceless self-adjoint matrices.
Because `SU(2)` is a matrix Lie group, a gauge transformation is a
matrix of functions on spacetime, and its Taylor series at `x` is just
the Taylor series of each of its four entries. The type of all
such (formal) Taylor series is what we call `JetRing`.
Since a Taylor series of a product of functions is the
product of their Taylor series, the traditional group law
carries over unchanged: it is still matrix multiplication, only now
with entries in `JetRing` rather than in `ℂ`. The same goes for the
equations `U† U = 1` and `det U = 1` which cut `SU(2)` out, and reading
them over `JetRing` is what gives us `GJ`. Likewise `𝔤J` is the
traceless self-adjoint matrices over `JetRing`.




## 3. The details

## 4. Future work

- BSM
- EFTs
- Improvements to group theory & algebra
- Symmetry breaking
- Connection to Feynman diagrams
- QED and the connection to EM
- Appropaite inclusion of total derivative removals.
