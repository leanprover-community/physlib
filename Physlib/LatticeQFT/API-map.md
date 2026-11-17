# Lattice QFT

## Abstract (Alpha)

Lattice quantum field theory regularizes a Euclidean quantum field theory by replacing
continuous spacetime with a hypercubic lattice of spacing a, usually periodic so that the
lattice is a finite torus, with matter fields on the sites and gauge fields on the oriented
links as elements of a compact gauge group. On a finite lattice the Euclidean path integral is an
ordinary finite-dimensional integral, Lebesgue measure for scalar fields and Haar measure for
link variables, weighted by the exponential of minus the lattice action; the theory is then a
genuine probability measure on field configurations whose moments are the correlation functions.
The physical questions concern those measures: reflection positivity, the transfer matrix and
the mass gap, confinement through Wilson loops, and the behaviour as the spacing goes to zero
and the volume to infinity. The gauge-field side builds on gauge theory.

## Content (Alpha)

### The lattice and its geometry

The periodic hypercubic lattice in dimension d has L sites per direction and spacing a > 0,
with a finite set of sites and a unit vector in each lattice direction. [TODO]
Nearest-neighbour sites are joined by oriented links, each with a reversed link, and the
elementary squares are oriented plaquettes, whose boundary is a closed loop of four
links. [TODO]

A function on the sites has forward and backward lattice derivatives and a lattice Laplacian;
summation by parts relates them, and for smooth functions they reduce to the continuum
derivatives as the spacing goes to zero. [TODO] The lattice Fourier transform on the periodic
lattice, over the Brillouin zone of lattice momenta, diagonalizes the lattice Laplacian with
eigenvalues (4/a²) Σ_μ sin²(a p_μ / 2). [TODO]

### Scalar fields

A real scalar field configuration is a function from sites to the reals, and the lattice quartic
action is the sum over sites of a^d times the kinetic term, the mass term and the quartic
interaction. [TODO] The Euclidean lattice measure is the product of Lebesgue measures over
sites weighted by the exponential of minus the action, and its partition function is finite and
strictly positive when the coupling is positive, or when it vanishes and the squared mass is
positive. [TODO] Normalizing gives a probability measure on field configurations whose
moments are the n-point Schwinger functions, invariant under lattice translations and the
lattice symmetry group. [TODO] The free lattice scalar field is the centred Gaussian measure
whose covariance inverts the massive Laplacian, with the lattice propagator in momentum
space. [TODO]

### Gauge fields

A link variable assigns an element of a compact gauge group {1} to each oriented link, the reversed
link carrying the inverse; gauge transformations act on link variables by conjugation between the
endpoints, and the plaquette variable is the ordered product of link variables around a
plaquette. [TODO] The Wilson action of a matrix gauge group is invariant under lattice gauge
transformations. [TODO] The lattice gauge-theory measure is the product of Haar measures over
links weighted by the exponential of minus the Wilson action, with a finite, strictly positive
partition function on a finite lattice. [TODO] A site-valued matter field couples to the link
variables gauge-covariantly through the covariant lattice derivative, and the resulting matter
action is gauge invariant. [TODO]

The Wilson loop of a closed lattice path is invariant under lattice gauge transformations, and
the area-law and perimeter-law behaviours of its expectation value are criteria for
confinement. [TODO] By Elitzur's theorem, on a finite lattice the expectation value of an
observable that is not gauge invariant equals that of its gauge-averaged part, so a local gauge
symmetry cannot be spontaneously broken. [TODO] In the strong-coupling regime of lattice
gauge theory with a compact gauge group, Wilson loops obey the area law. [TODO]

### Structural results and the continuum limit

The lattice measure is reflection positive in the sense of Osterwalder and Schrader, for the
scalar field and for the Wilson action, with respect to reflections in lattice
hyperplanes. [TODO] The transfer matrix is a positive operator on the Hilbert space of
time-slice configurations; it determines the lattice Hamiltonian, and the exponential decay rate
of the two-point function in Euclidean time is the spectral gap. [TODO] For a smooth
continuum gauge field, with link variables given by parallel transport along the links, the
Wilson action converges to the Yang–Mills action as the spacing goes to zero, with corrections of
second order in the spacing. [TODO]

### Fermions

Naive lattice fermions suffer the doubling problem, one continuum species for each corner of the
Brillouin zone, and Wilson fermions remove the doublers at the cost of explicitly breaking chiral
symmetry. [TODO] By the Nielsen–Ninomiya theorem, a local, translation-invariant, hermitian
lattice fermion action with exact chiral symmetry has equal numbers of left- and right-handed
species. [TODO]

## Lean References

*None yet.*

## References

1. Gauge theory API map — Physlib/ClassicalFieldTheory/GaugeTheory/API-map.md
