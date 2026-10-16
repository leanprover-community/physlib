# Lattice QFT

Lattice quantum field theory regularizes a Euclidean quantum field theory by replacing
continuous spacetime with a hypercubic lattice of spacing a, usually taken periodic so that the
lattice is a finite torus. Matter fields live on the sites, gauge fields on the oriented links
as elements of a compact gauge group.

On a finite lattice the Euclidean path integral becomes an ordinary finite-dimensional
integral: Lebesgue measure for scalar fields, Haar measure for link variables, weighted by the
exponential of minus the lattice action. The theory is then a genuine probability measure on
field configurations, and the correlation functions are its moments. The physical questions are
the properties of those measures — reflection positivity, the transfer matrix and the mass gap,
confinement through Wilson loops, and the behaviour as the spacing goes to zero and the volume
to infinity.

None of this is formalized: the lattice QFT module is a stub with no declarations, as is the
neighbouring lattice-models module under condensed matter. Every requirement below is therefore
planned. They are ordered roughly as they would be built: the lattice and its geometry, scalar
fields, gauge fields, structural results, and finally fermions and the continuum limit.

## Built on

- Gauge theory — `Physlib/ClassicalFieldTheory/GaugeTheory`

## Requirements

The key data structure will be defined: the periodic hypercubic lattice in dimension d with L
sites per direction and spacing a > 0, together with its finite set of sites and the unit
vectors in each lattice direction. [planned]

The oriented links between nearest-neighbour sites and the oriented plaquettes — the elementary
squares — will be defined, with the reversal of a link and the boundary of a plaquette as a
closed loop of four links. [planned]

The forward and backward lattice derivatives of a function on the sites will be defined, with
the lattice Laplacian, the summation-by-parts identity relating them, and their reduction to
the continuum derivatives as the spacing goes to zero for smooth functions. [planned]

The lattice Fourier transform will be defined on the periodic lattice, with the Brillouin zone
of lattice momenta, diagonalizing the lattice Laplacian with eigenvalues
(4/a²) Σ_μ sin²(a p_μ / 2). [planned]

Real scalar field configurations will be functions from sites to the reals, with the lattice
quartic action: the sum over sites of a^d times the kinetic term, the mass term and the
quartic interaction. [planned]

The Euclidean lattice measure for a scalar field will be the product of Lebesgue measures over
sites weighted by the exponential of minus the action, and its partition function will be shown
finite and strictly positive when the coupling is positive, or when it vanishes and the squared
mass is positive. [planned]

The normalized lattice probability measure on field configurations will be defined, with the
n-point Schwinger functions as its moments, invariant under lattice translations and the
lattice symmetry group. [planned]

The free lattice scalar field will be shown to be the centred Gaussian measure whose covariance
inverts the massive Laplacian, with the lattice propagator in momentum space. [planned]

Link variables will be functions from oriented links to a compact gauge group, with the
reversed link carrying the inverse; the gauge transformations acting on them by conjugation
between the endpoints; and the plaquette variable as the ordered product of link variables
around a plaquette. [planned]

The Wilson action will be defined for a matrix gauge group, and shown invariant under lattice
gauge transformations. [planned]

The lattice gauge-theory measure will be the product of Haar measures over links weighted by
the exponential of minus the Wilson action, with a finite, strictly positive partition function
on a finite lattice. [planned]

A site-valued matter field will be coupled to the link variables gauge-covariantly, through the
covariant lattice derivative, and the resulting matter action shown gauge invariant. [planned]

The Wilson loop of a closed lattice path will be defined, with its invariance under lattice
gauge transformations and the area-law and perimeter-law behaviours of its expectation value as
criteria for confinement. [planned]

Elitzur's theorem will be proved: on a finite lattice the expectation value of an observable
that is not gauge invariant equals that of its gauge-averaged part, so a local gauge symmetry
cannot be spontaneously broken. [planned]

The area law for Wilson loops will be proved in the strong-coupling regime of lattice gauge
theory with a compact gauge group. [planned]

Reflection positivity of the lattice measure, in the sense of Osterwalder and Schrader, will be
proved for the scalar field and for the Wilson action, with respect to reflections in lattice
hyperplanes. [planned]

The transfer matrix will be constructed as a positive operator on the Hilbert space of
time-slice configurations, with the lattice Hamiltonian defined from it and the relation
between the exponential decay rate of the two-point function in Euclidean time and the spectral
gap. [planned]

The Wilson action of a smooth continuum gauge field, with link variables given by parallel
transport along the links, will be shown to converge to the Yang–Mills action as the spacing
goes to zero, with corrections of second order in the spacing. [planned]

Naive lattice fermions will be defined, with the doubling problem — one continuum species for
each corner of the Brillouin zone — and Wilson fermions, which remove the doublers at the cost
of explicitly breaking chiral symmetry. [planned]

The Nielsen–Ninomiya theorem will be proved: a local, translation-invariant, hermitian lattice
fermion action with exact chiral symmetry has equal numbers of left- and right-handed
species. [planned]

## Lean declarations

*None yet.*
