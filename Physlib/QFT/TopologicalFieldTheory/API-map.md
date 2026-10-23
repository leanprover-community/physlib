# Topological field theory

## Abstract (Alpha)

A topological field theory assigns algebraic data to manifolds in a way that depends only on
their topology. In the Atiyah–Segal formulation, a theory in dimension d is a symmetric monoidal
functor from a category of cobordisms, whose objects are closed oriented (d−1)-manifolds and
whose morphisms are oriented d-dimensional cobordisms between them, to the category of modules
over a fixed commutative ring. The state space of a closed (d−1)-manifold is the value of the
functor on that object, and the partition function of a closed d-manifold is its value on that
manifold read as a cobordism from the empty manifold to itself. No metric on the world-volume
enters, so every number and every space produced this way is an invariant of the underlying
manifold. The one-dimensional world-volume is the time manifold, which carries an orientation
but no metric.

## Content (Alpha)

### Cobordisms and functors

The cobordism category in dimension d has closed oriented (d−1)-manifolds as objects and
oriented cobordisms, taken up to boundary-preserving diffeomorphism, as morphisms, composed by
gluing along a common boundary. [TODO] Disjoint union makes it symmetric monoidal, with the
empty (d−1)-manifold as unit. [TODO] A topological field theory in dimension d is a symmetric
monoidal functor from this category to the modules over a fixed commutative ring. [TODO]
This is the axiomatization of Atiyah {1}, modelled on Segal's definition of conformal field
theory {2}.

### State spaces and partition functions

A closed oriented (d−1)-manifold has a state space, which is finitely generated, and finite
dimensional when the ground ring is a field. [TODO] The state space of a disjoint union is
the tensor product of the state spaces, and the empty manifold has the ground ring as its state
space. [TODO] The map of a cobordism cut along a closed (d−1)-manifold is the composite of
the maps of the two pieces. [TODO] A closed oriented d-manifold has a partition function, an
element of the ground ring invariant under orientation-preserving diffeomorphism. [TODO]

Reversing orientation dualizes: the state space of the reversed manifold is dual to the
original, and the pairing between them coming from the cylinder is nondegenerate. [TODO] A
cylinder induces the identity on the state space, so a topological theory has no time evolution
on a fixed spatial slice. [TODO] The partition function of the product of a closed
(d−1)-manifold with a circle is the rank of the state space of that manifold. [TODO]

### Classification in low dimension

In dimension two, topological field theories valued in vector spaces over a field are
equivalent to commutative Frobenius algebras {3}. [TODO] In dimension one, topological field
theories are equivalent to finitely generated projective modules. [TODO] Topological quantum
mechanics is the one-dimensional case on the time manifold {4}, whose world-volume carries an
orientation but no metric (see issue #877 {5}). [TODO] The general classification programme
is that of Lurie {6}.

### Topological gauge theories

The Chern–Simons action of a connection on a principal bundle over a closed oriented
three-manifold is independent of any metric, gauge invariant up to a shift by an integer
multiple of the level, and has the flat connections as its critical points. [TODO] The BF
action in general dimension is independent of any metric, and its field equations say that the
connection is flat and the second field is covariantly constant. [TODO] Wilson-loop
observables of a topological gauge theory are gauge invariant, and their expectation values give
link invariants. [TODO] These are the ideas of Witten {7}. The Dijkgraaf–Witten
theory of a finite gauge group has as partition function the count of principal bundles over
the manifold weighted by a group cocycle. [TODO]

## Lean References

*None yet.*

## References

1. M. F. Atiyah, *Topological quantum field theories*, Publications Mathématiques de l'IHÉS 68
   (1988), 175–186.
2. G. Segal, *The definition of conformal field theory*, in *Differential Geometrical Methods in
   Theoretical Physics* (1988), 165–171.
3. J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Cambridge University
   Press (2003).
4. Time API map — Physlib/SpaceAndTime/Time/API-map.md
5. Physlib GitHub issue #877, https://github.com/leanprover-community/physlib/issues/877
6. J. Lurie, *On the classification of topological field theories*, Current Developments in
   Mathematics 2008 (2009), 129–280.
7. E. Witten, *Quantum field theory and the Jones polynomial*, Communications in Mathematical
   Physics 121 (1989), 351–399.
