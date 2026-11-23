# Blackbody radiation

## Abstract (Alpha)

An ideal black body in thermal equilibrium emits radiation with a spectrum determined by its
temperature. Planck's law gives the spectral radiance per unit frequency or per unit wavelength,
with a Jacobian relating the two densities. The oscillator model explains the difference between
Planck's law and the classical Rayleigh–Jeans law through their different mean energies per mode.

## Content (Alpha)

### Frequency and wavelength spectra

A black body is specified by its temperature. For positive frequency $\nu$ and temperature $T$,
its spectral radiance per unit frequency is given by Planck's law,
$B_\nu(T)=2h\nu^3/[c^2(\exp(h\nu/(k_B T))-1)]$. This radiance is positive in that domain and
vanishes at zero frequency and at absolute zero. [1]

The wavelength density at $\lambda>0$ measures radiance over an interval in wavelength. At
positive temperature, the change of variable $\nu=c/\lambda$ gives
$B_\lambda(T)=(c/\lambda^2) B_\nu(T)|_{\nu=c/\lambda}$, where $c/\lambda^2$ is the magnitude of the
Jacobian. [2]

### Energy per mode and the classical comparison

A mode of frequency $\nu>0$ is modeled by an oscillator with level spacing $\varepsilon=h\nu$.
In the canonical ensemble {1}, its levels have energies $n\varepsilon$ for nonnegative integers
$n$. At positive temperature, the mean energy is
$\varepsilon/(\exp(\beta\varepsilon)-1)$, with $\beta=1/(k_B T)$. The corresponding classical model
integrates over positive energies with Lebesgue measure and has mean energy $k_B T$. [3]

Multiplying each mean energy by the same factor $2\nu^2/c^2$ gives Planck's spectral radiance and
the Rayleigh–Jeans spectral radiance, respectively. The quantized mean energy is strictly below
the classical one, so Planck's radiance is strictly below Rayleigh–Jeans at every positive
frequency and positive temperature. [4][5]

## Lean References

1. Physlib/QuantumMechanics/Blackbody/PlancksLaw.lean — `BlackBody`,
   `BlackBody.spectralRadiance`, `BlackBody.spectralRadiance_pos`,
   `BlackBody.spectralRadiance_zeroFreq`, `BlackBody.spectralRadiance_absZero`
2. Physlib/QuantumMechanics/Blackbody/PlancksLaw.lean — `BlackBody.spectralRadianceWave`,
   `BlackBody.spectralRadianceWave_eq_spectralRadiance`
3. PhyslibAlpha/QuantumMechanics/Blackbody/RayleighJeans.lean — `BlackBody.quantizedOscillator`,
   `BlackBody.quantizedOscillator_meanEnergy`, `BlackBody.classicalOscillator`,
   `BlackBody.classicalOscillator_meanEnergy`
4. PhyslibAlpha/QuantumMechanics/Blackbody/RayleighJeans.lean — `BlackBody.rayleighJeans`,
   `BlackBody.rayleighJeans_eq_meanEnergy`, `BlackBody.spectralRadiance_eq_meanEnergy`
5. PhyslibAlpha/QuantumMechanics/Blackbody/RayleighJeans.lean —
   `BlackBody.quantizedOscillator_meanEnergy_lt`, `BlackBody.spectralRadiance_lt_rayleighJeans`

## References

1. Canonical ensemble API map — Physlib/StatisticalMechanics/CanonicalEnsemble/API-map.md
