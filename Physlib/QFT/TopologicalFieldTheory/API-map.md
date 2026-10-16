# Topological field theory

A topological field theory assigns algebraic data to manifolds in a way that depends only on
their topology. In the Atiyah–Segal formulation, a theory in dimension d is a symmetric
monoidal functor from a category of cobordisms — whose objects are closed oriented
(d−1)-manifolds and whose morphisms are oriented d-dimensional cobordisms between them — to the
category of modules over a fixed commutative ring. The state space of a closed (d−1)-manifold
is the value of the functor on that object, and the partition function of a closed d-manifold
is its value on that manifold read as a cobordism from the empty manifold to itself. No metric
on the world-volume enters the construction, so every number and every space produced this way
is an invariant of the underlying manifold.

This is a tracking map for issue #877. None of it is formalized: there is no category of
cobordisms, no monoidal functor into modules, and no example theory such as Chern–Simons or BF
theory. The one adjacent piece the library does have is the time manifold — time carrying an
orientation but no metric — which is the one-dimensional world-volume such a theory would be
placed on. Every requirement below is therefore still planned.

## Built on

- Time — `Physlib/SpaceAndTime/Time`

## Requirements

The category of cobordisms in dimension d will be defined, with closed oriented
(d−1)-manifolds as objects and oriented cobordisms taken up to boundary-preserving
diffeomorphism as morphisms, composed by gluing along a common boundary. [planned]

That category will carry the symmetric monoidal structure given by disjoint union, with the
empty (d−1)-manifold as unit. [planned]

The key data structure will be defined: a topological field theory in dimension d, a symmetric
monoidal functor from the cobordism category to the modules over a fixed commutative
ring. [planned]

A closed oriented (d−1)-manifold will be assigned its state space, subject to the finiteness
condition that it is finitely generated — finite dimensional when the ground ring is a
field. [planned]

Multiplicativity will hold: the state space of a disjoint union is the tensor product of the
state spaces, and the empty manifold is assigned the ground ring. [planned]

Gluing will hold: the map assigned to a cobordism cut along a closed (d−1)-manifold is the
composite of the maps assigned to the two pieces. [planned]

A closed oriented d-manifold will have a partition function, an element of the ground ring,
invariant under orientation-preserving diffeomorphism. [planned]

Reversing orientation will dualize: the state space of a manifold with reversed orientation is
dual to the original, and the pairing between them coming from the cylinder is
nondegenerate. [planned]

A cylinder will induce the identity on the state space, so that a topological theory has no
time evolution on a fixed spatial slice. [planned]

The trace formula will hold: the partition function of the product of a closed (d−1)-manifold
with a circle is the rank of the state space of that manifold. [planned]

Dimension two will be classified: topological field theories valued in vector spaces over a
field are equivalent to commutative Frobenius algebras. [planned]

Dimension one will be classified: topological field theories are equivalent to finitely
generated projective modules. [planned]

Topological quantum mechanics will be treated on the time manifold, the one-dimensional case in
which the world-volume carries an orientation but no metric. [planned]

The Chern–Simons action of a connection on a principal bundle over a closed oriented
three-manifold will be defined, with its independence of any metric, its gauge invariance up to
a shift by an integer multiple of the level, and the identification of its critical points with
the flat connections. [planned]

The BF action will be defined in general dimension, with its independence of any metric and its
field equations, which say that the connection is flat and the second field is covariantly
constant. [planned]

Wilson-loop observables of a topological gauge theory will be defined, with their invariance
under gauge transformation and the link invariants their expectation values give. [planned]

The finite gauge group theory of Dijkgraaf and Witten will be worked out as an example, its
partition function counting principal bundles over the manifold weighted by a group
cocycle. [planned]

## Further reading

- M. F. Atiyah, Topological quantum field theories, Publications Mathematiques de l'IHES 68 (1988), 175-186
- G. Segal, The definition of conformal field theory, in Differential Geometrical Methods in Theoretical Physics (1988), 165-171
- E. Witten, Quantum field theory and the Jones polynomial, Communications in Mathematical Physics 121 (1989), 351-399
- J. Kock, Frobenius Algebras and 2D Topological Quantum Field Theories, Cambridge University Press (2003)
- J. Lurie, On the classification of topological field theories, Current Developments in Mathematics 2008 (2009), 129-280

## Lean declarations

*None yet.*
