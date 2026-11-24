# Lean formalization of the TSGA

This Lean 4 project accompanies [the manuscript](../tsga.tex). The project pins
the toolchain and mathlib revision. From this directory, with Elan installed, run

```sh
lake exe cache get
lake build
```

Use `import TSGA` to load the development.

## Results checked in Lean

| Manuscript result | Lean source | Scope |
| --- | --- | --- |
| Spin rotations about the third axis | [Spin.lean](TSGA/Spin.lean) | The explicit rotation lies in SU(2), preserves trace and positivity, and multiplies the transverse magnetization by the expected phase. |
| Grand-canonical Coulomb functional, Section 2 | [LevyLieb.lean](TSGA/LevyLieb.lean) | Defines normalized antisymmetric wavefunctions, countable mixtures, the reduced spin density and the constrained search with Hartree subtraction. Proves zero vacuum energy and invariance under changing the density on a null set. |
| Fixed-particle representability, Theorem 2.1 | [Fixed particle sector](TSGA/FixedParticleRepresentability.lean) | Characterizes the spin density of a fixed-N ensemble by positivity, charge N and an H¹ square root. The proof uses one-body marginals, the matrix Hoffmann–Ostenhof inequality, a layer trial and fixed-sector realization of an integer-trace Pauli contraction. |
| Levy–Lieb attainment, Theorem 2.2 | [Attainment](TSGA/LevyLiebAttainment.lean) · [Island construction](TSGA/IslandFockAttainment.lean) | A minimizing sequence has a limit with the prescribed spin density. Fixed-charge subsequence compactness and lower semicontinuity of the many-body energy are explicit inputs. |
| Matrix Hoffmann–Ostenhof inequality, Lemma 4.6 and Appendix A | [HoffmannOstenhof.lean](TSGA/HoffmannOstenhof.lean) · [Sharpness](TSGA/HoffmannOstenhofSharpness.lean) | Proves the coefficient 1/2 for unrestricted nonnegative occupations in every spatial dimension d ≥ 1, using weak square-root calculus and countable Fisher convexity. Finite trace and the domain form of countable Fisher lower semicontinuity give the H¹ square root for the occupied orbital family. A normalized rotating spinor violates every larger coefficient. [Square-root domain](TSGA/SpatialFisherDomain.lean) · [All dimensions](TSGA/SpatialHoffmannOstenhof.lean) · [Sharpness in each dimension](TSGA/SpatialHoffmannOstenhofSharpness.lean) |
| Finite-system energy bounds, Corollaries 4.7 and 4.9 and Theorem 4.8 | [Coulomb corollaries](TSGA/CoulombCorollaries.lean) · [Kinetic trial](TSGA/KineticTrial.lean) · [Layer gradient](TSGA/LayerGradient.lean) | `FiniteEnergyInputs.fisher_lower_bound` combines the matrix Hoffmann–Ostenhof coefficient 1/2 with the model's Lieb–Oxford coefficient. For every d ≥ 1 the layer-cake trial gives the kinetic upper bound with power 1+2/d. Quasi-free realization gives the interacting estimate on the finite-Hartree domain. [Kinetic bound](TSGA/SpatialKineticUpper.lean) · [Interacting bound](TSGA/SpatialCoulombUpper.lean) |
| Finite-system spin spirals, Theorem 4.14 | [Finite Coulomb spirals](TSGA/FiniteCoulombSpirals.lean) | For feasible spin densities, derives corrected concavity and the diagonal lower bound from the actual many-body rotation. Gives the optimized upper bound for a coplanar magnetization and equality for a fixed fully polarized spin direction. |
| Thermodynamic SSW gas, Theorem 3.1 and Proposition 3.2 | [Thermodynamic limit and gas properties](TSGA/SSWGasProperties.lean) | Constructs a common thermodynamic limit from finite-volume localization estimates. Proves the zero-wavevector identity, the vacuum case, isotropy, corrected concavity, both energy bounds and equality at full polarization. |
| Fixed-axis transverse spin-gradient approximation, Theorem 3.3 | [Coulomb theorem](TSGA/CoulombTheorem.lean) · [Integration over centers](TSGA/CoulombLocalToGlobal.lean) | `CoulombModelInputs.fixedAxisTSGA` gives the general estimate and the sharper estimate under a global root-gradient assumption for every ε > 0. |
| Error exponents and rescaling | [Exponents.lean](TSGA/Exponents.lean) | Derives both bulk exponents from the Hölder exponents, bounds the density powers in Young's inequality and checks the scalar balance giving the particle-number exponent 5/6. |
| Azimuthal gradient form, Corollary 3.4 | [Gradient identities](TSGA/GradientForm.lean) · [Coulomb corollaries](TSGA/CoulombCorollaries.lean) | `CoulombModelInputs.azimuthalTSGA` transfers the two estimates to the physical spin density. The phase-gradient identity holds wherever the transverse magnetization is nonzero. |
| Zero-phase reduction, Corollary 3.5 | [Coulomb corollaries](TSGA/CoulombCorollaries.lean) | `CoulombModelInputs.noncollinearLSDA` specializes the general estimate to LSDA at arbitrary polarization. The phase-gradient region is empty, so the estimate needs no global gradient of the matrix power 1/p. |
| Convergence rate for spiral tetrahedra, Proposition D.1 | [SSWRate.lean](TSGA/SSWRate.lean) | Proves the fixed-scale upper rate and the dilation-averaged lower rate from quantitative finite tiling bounds. |
| Matrix Fisher form, Lemma A.1 | [Wigner–Yanase form](TSGA/WignerYanaseMetric.lean) | Identifies the form with the squared Hilbert–Schmidt norm of the Sylvester solution at positive density and its regularized limit at singular density. Proves homogeneity, joint convexity, order monotonicity and convexity after integration using tensor square-root concavity. |
| Localization of a variable spin density, Theorems 4.10 and 4.12 | [Upper localization](TSGA/UpperLocalizationScales.lean) · [Lower localization](TSGA/LowerLocalizationScales.lean) | The upper bound keeps the dilation width, smoothing width and tile length independent, with the logarithmic dilation factor and a separate signed skeleton estimate. The lower bound uses the unshrunk tetrahedra and their translation and frame averages. |
| Local rotations of the spin, Lemma 4.13 | [Coulomb rotation](TSGA/CoulombLocalRotation.lean) · [Sector tensor product](TSGA/LocalSpinTensor.lean) | Rotates each occupied wave and preserves its Coulomb interaction. The supported weak product rule gives the rotated density an H¹ square root. Mixing and minimizing give the operator-norm energy bound. [Rotated density domain](TSGA/RotatedDensityDomain.lean) |
| Density oscillation, Lemma 4.15(iii) | [Charge comparison](TSGA/BallChargeComparison.lean) | At the θ/4 threshold, every charge on the closed ball is at least half its maximum. |
| Local wavevector replacement, Lemma 4.17 | [Weighted replacement](TSGA/ConstantWavevectorRotation.lean) · [Square-root domain](TSGA/WavevectorReplacementDomain.lean) | Proves both energy inequalities with the tapered integral of ρ‖∇φ−q‖² divided by 2ε. The oscillation bound follows by taking a supremum. |
| Freezing on a ball, Lemma 4.18 | [Weighted wavevector estimate](TSGA/WeightedWavevector.lean) | With local Sobolev data on the ball, a minimum of ‖∇φ‖ gives one wavevector for every measurable taper and ε. The finite-error proof uses the local product and Morrey rules. The two gradient errors have coefficients proportional to ℓᵖ/ε and ℓᵖ/ε^(p−1). |
| Comparison of SSW gas energies, Lemma 4.19 | [Matrix and wavevector comparison](TSGA/GasComparison.lean) | Controls simultaneous changes of matrix and wavevector at any positive upper bound for the two traces. |
| Freezing spin density on a tile, Proposition 4.16 | [Comparison matrices](TSGA/ComparisonMatrices.lean) · [Shifted matrices](TSGA/ShiftedComparison.lean) · [Signed replacement](TSGA/CoulombRotationReplacement.lean) | Constructs the comparison matrices, bounds their power oscillations and combines both Poisson additions with the spin-axis and phase rotations. The free-scale comparison keeps the kinetic integral weighted by the taper. [Free scales](TSGA/FreeWindowReplacement.lean) · [Local Sobolev domain](TSGA/LocalWindowReplacement.lean) |
| Removing electrons according to spin, Lemma E.1 | [Partial trace](TSGA/FockPartialTrace.lean) · [Mixed-state removal](TSGA/GeometricSpinRemoval.lean) · [Spin contraction](TSGA/SpinContraction.lean) | Constructs a localized mixed state with the contracted density, kinetic energy, pair energy and current. Gives both energy inequalities, including the ordered-matrix inequality for singular densities with an H¹ cutoff square root. [Cutoff representability](TSGA/SpinRemovalRegular.lean) |
| Energy bounds and scaling, Proposition E.2(i) | [WavevectorRegularity.lean](TSGA/WavevectorRegularity.lean) · [GasScaling.lean](TSGA/GasScaling.lean) | Obtains the sharp power bounds from the uniform gas. Passes the finite Coulomb dilation and Lieb–Oxford inequalities to the SSW limit with the wavevector scaled by α¹ᐟ³, including α = 0. |
| Fixed-charge convexity, Proposition E.2(ii) | [GasConvexity.lean](TSGA/GasConvexity.lean) | Passes the finite Coulomb mixing inequality to the common thermodynamic limit, given representing states for the spiral cutoffs along one sequence. |
| Wavevector regularity, Proposition E.2(iii) | [WavevectorRegularity.lean](TSGA/WavevectorRegularity.lean) | Derives the Lipschitz estimate from corrected concavity and gas growth for every positive semidefinite spin matrix, including the vacuum. |
| Matrix regularity at positive minority fraction, Proposition E.2(iv) | [CoulombRegularity.lean](TSGA/CoulombRegularity.lean) · [MinorityRegularity.lean](TSGA/MinorityRegularity.lean) · [RayRegularity.lean](TSGA/RayRegularity.lean) | Proves the matrix Lipschitz bound with the stated 1/ν dependence, also for unequal traces. The Coulomb specialization derives both ray scaling and fixed-charge convexity from finite-system inputs. |
| Matrix regularity up to full polarization, Proposition E.2(v)–(vi) | [Ordered comparison](TSGA/OrderedGas.lean) · [Hölder estimate](TSGA/CoulombHolder.lean) · [Matrix-root estimate](TSGA/CoulombRootRegularity.lean) | Gives the cube-root Hölder estimate and the Lipschitz estimate in the matrix power 1/p for every real p ≥ 3. The matrices may have different traces and eigenframes. Both results use finite Coulomb tiling estimates and the reduced Fock traces for removal of electrons by spin. |
| Subadditivity with local errors, Lemma C.1 | [Single-island profiles](TSGA/IslandTetraProfiles.lean) · [Fock trial](TSGA/IslandTrialAssembly.lean) · [Tetrahedral estimate](TSGA/IslandPoissonConstruction.lean) | Builds both states on a common marked Poisson realization and derives the finite-radius and bounded-charge comparisons. |
| Cube-root comparison following Proposition E.2 | [SpectralHolder.lean](TSGA/SpectralHolder.lean) | Transfers the scalar Hölder bound to noncommuting spin matrices by Jensen's inequality in two spectral bases. Together with the Lipschitz case this gives the exponent min(1, 1/(3θ)). |
| Particle-number rescaling | [Coulomb corollaries](TSGA/CoulombCorollaries.lean) · [Spiral estimate](TSGA/RescaledSpiralEstimate.lean) | `rescaledNoncollinearLSDA` gives the LSDA error of order $N^{\max\{5/6,\,1-1/(3+9\theta)\}}$ for a fixed profile. The corollary `rescaledNoncollinearLSDA_improvesLLS` gives $o(N^{11/12})$ for θ < 1. `rescaledSpiral` gives order $N^{5/6}$ for the rescaled phase under the global root-gradient assumption. For θ ≤ 1/3 the spiral estimate needs only the weighted root gradient on the active set. |
| Additional conditional estimates at full polarization | [Endpoint implication](TSGA/ConditionalUEG.lean) · [Coulomb LSDA](TSGA/ConditionalCoulombLSDA.lean) | The conjectured linear cost of flipping spins implies a matrix Lipschitz estimate at zero wavevector and the improved LSDA exponent at arbitrary polarization. A power-law endpoint bound of order α ∈ [1/3,1] gives the interpolated LSDA exponent by the same signed tile comparison. [Intermediate exponents](TSGA/EndpointCoulombLSDA.lean) |

[Sobolev.lean](TSGA/Sobolev.lean) defines the spatial fields on Euclidean
three-space. Matrix powers use Hermitian functional calculus. Weak partial
derivatives are identified by integration against smooth compactly supported
tests. The phase carries a continuous representative of its gradient, as
available from local Sobolev regularity for the manuscript's range of p.

## The SSW gas theorem

`TSGA.SSW.sswGas_theorem` constructs the SSW and uniform gas energies for the
energy functional supplied to it. Its limit quantifies over every admissible
domain sequence, outer smoothing width and mollifier. The resulting
`referenceEnergies` can be used directly in the TSGA and LSDA statements.
For the Coulomb model, `CoulombModelInputs.ssw_limit` gives Theorem 3.1 and
`CoulombModelInputs.ssw_properties` gives the three parts of Proposition 3.2.
At fixed charge the uniform gas energy is an even convex function of the
signed polarization. [Gas properties](TSGA/SSWGasProperties.lean)

- The domain and cutoff are concrete objects in Euclidean three-space. The
  indicator is convolved with the rescaled kernel. Lean checks the cutoff's
  mass, the particle number, and the vanishing boundary-layer and kinetic
  costs at the prescribed scales. [Domains](TSGA/SSWDomain.lean) ·
  [Boundary estimates](TSGA/SSWBoundary.lean)
- A sequence of balls of radius n + 1 with smoothing width one satisfies
  all the domain hypotheses. Its boundary estimate follows by subtracting
  two ball volumes. Squaring and normalizing a smooth radial amplitude
  supplies an explicit admissible mollifier. [Ball sequence](TSGA/BallSequence.lean) ·
  [Radial kernel](TSGA/RadialMollifier.lean)
- The reference energy uses one of the 24 tetrahedra of the cube. Direction
  averaging uses normalized Euclidean surface measure, the standard spherical
  representation of the Haar rotation average. A two-scale inequality
  gives the same tetrahedron limit at every fixed positive smoothing width.
  The domain upper bound uses dominated convergence for the normalized
  dilation average with weight `t⁻⁴` on [1/2, 3/2].
  [Direction average](TSGA/DirectionAverage.lean) ·
  [Two-scale limit](TSGA/TetrahedronLimit.lean) · [Dilation average](TSGA/ScaleAverage.lean)
- Translation and rotation covariance follow from the corresponding finite
  energy invariances. The spin-population bounds follow by taking limits of
  the finite constrained-search comparisons on a single admissible sequence.
  [Covariance](TSGA/SpiralCovariance.lean) · [Spin bounds](TSGA/SSWBounds.lean)

The abstract version of Theorem 3.1 applies to a functional with zero
vacuum energy. It uses `FiniteSpinLaws` for finite spin comparisons and
`FiniteLocalization` for bounds and convergence of the averaged tile
energies. The Coulomb specialization derives the spin laws, the rough tile bounds and
the finite comparisons on regular domains from the model and the inputs below.
[Localization hypotheses and limit proof](TSGA/SSWLocalization.lean)

For the Coulomb model, `ManyBody.coulomb_sswGas_and_rate_of_fock_localization`
gives Theorem 3.1 and Proposition D.1, and returns all seven finite comparisons
at one constant. The lower comparisons use the state-level smeared
Graf–Schenker and IMS inequality. For the upper comparisons Lean assembles
disjoint Fock tensor products on the actual 24-tetrahedron lattice, averages
translations, frames and dilations, and estimates the boundary and skeleton
energies. The reference kernel is supported in the ball of radius 1/100.
Each domain sequence may use its own mollifier. The qualitative argument also
works with the older quadratic electrostatic estimate.
[Physical tiling theorem](TSGA/CoulombPhysicalTiling.lean) ·
[State localization](TSGA/CoulombLowerTiling.lean) ·
[Product trials](TSGA/CoulombUpperTrialAssembly.lean) ·
[Qualitative limit](TSGA/CoulombQualitativeLimit.lean)

A spin-dependent phase
adds the integrated spin current and the quadratic population cost to the
kinetic energy and preserves the Coulomb interaction. A uniform boost gives
the correction involving the axial magnetization. At full polarization the
null spin channel annihilates every occupied component of positive weight.
Its distributional derivative vanishes too, giving
$J_3 = \cos(\theta) P$. [Spin twist](TSGA/WaveTwist.lean) ·
[Exact ensemble laws](TSGA/EnsembleTwist.lean) · [Rank-one current](TSGA/RankOneCurrent.lean) ·
[Finite transport](TSGA/CoulombTransportModel.lean) · [Coulomb gas theorem](TSGA/CoulombTilingModel.lean)

For Lemma E.1, `fock_partial_trace_spin_removal` constructs one countable mixed state
for each spin contraction S. Its spatial density is SρS*, and its kinetic
energy, Coulomb interaction and axial current in every direction are traces
of the original state. The kinetic matrix is the second moment of its spin
momentum density. The Coulomb matrix integrates the spin-resolved pair
marginal with the unordered-pair normalization N(N−1)/2. Bounded Coulomb
multipliers converge under the finite interaction assumption. The argument
also covers singular S and ensembles with infinite second particle-number
moment. `FockPartialTraceSpectralTheorem.spinCurrentTraces` supplies the input used by the
ordered-frame and Coulomb regularity theorems.
[Doubled-wave partial trace](TSGA/FockPartialTrace.lean) · [Mixed-state removal](TSGA/GeometricSpinRemoval.lean) ·
[Finite-sector tests](TSGA/GeometricSpinTests.lean) ·
[Spin isometry on waves](TSGA/SpinFockWave.lean)

For a general coplanar spin density, conjugation followed by a constant
axial rotation preserves the prescribed density and reverses both spin
momenta. Mixing the two ensembles gives the zero-current trial in the
finite-system upper bound. [Coplanar states](TSGA/PlanarCurrent.lean) ·
[Finite-system theorem](TSGA/FiniteCoulombSpirals.lean)

## The transverse spin-gradient approximation

`TSGA.ManyBody.CoulombModelInputs.fixedAxisTSGA` gives the two estimates of
Theorem 3.3 for the reference gas constructed by `CoulombModelInputs.sswGas`.
The spin direction can vary in the rotating frame. At a point x the reference
spiral freezes that frame's density matrix and keeps the affine phase
φ(x) + ∇φ(x)·h at displacement h about the third spin axis.
`Density.cutoffSpiral_affinePhase` gives this identity for the cutoff spiral.
`AxialGasInvariant.localEnergy_azimuthalFrame` gives pointwise equality of the
reference energies in the physical and rotating frames. At a zero of the
transverse magnetization, `SSW.sswEnergy_of_transverseMagnetization_eq_zero`
shows that every wavevector gives the uniform gas energy, including in the
vacuum. [Fixed-axis identities](TSGA/GradientForm.lean) · [Reference gas at zero transverse magnetization](TSGA/SSWGasProperties.lean)

The finite-error theorem assumes integrability of the density-weighted phase
Hessian and the root gradient weighted by the squared wavevector. The extended
theorem `CoulombModelInputs.tsga` also gives integrability of the local SSW
energy when a phase error is infinite.
In the global-root estimate a single constant works for every admissible θ at
fixed p. `CoulombModelInputs.tsgaFinite` also proves a refinement when the
minority fraction is bounded below. The paper's azimuthal and zero-phase
corollaries are `CoulombModelInputs.azimuthalTSGA` and
`CoulombModelInputs.noncollinearLSDA`.
[Coulomb theorem](TSGA/CoulombTheorem.lean) · [Extended integrals](TSGA/ExtendedEstimate.lean) ·
[Coulomb corollaries](TSGA/CoulombCorollaries.lean)

- Lean bounds the errors on balls of small and large density oscillation.
  On a ball with positive minimum wavevector magnitude, it absorbs the local
  root-gradient cost into the phase-weighted integral. When the minimum is
  zero, the comparison uses only the phase curvature term.
  [Bulk errors](TSGA/BulkTile.lean) · [Phase errors](TSGA/PhaseTile.lean) ·
  [Truncated wavevector](TSGA/PhaseTruncation.lean)
- Integrating the upper and lower comparisons over tile centers gives the
  absolute error bound. Rescaling gives the coefficient ε on the first
  integral for every ε > 0. In the global-root case, a scalar Lipschitz
  estimate transfers the bound at θ = 2/p to all pθ ≥ 2 with one constant
  depending only on p.
  [Integration over centers](TSGA/LocalizationAssembly.lean) ·
  [Rescaling](TSGA/ErrorScale.lean) · [Matrix powers](TSGA/SharpInterpolation.lean)

## Specialization to the Coulomb energy

`TSGA.ManyBody.levyLieb_tsga` applies Theorem 3.3 to the constrained-search
energy and to the SSW gas defined from that same energy. Given a positive
density with finite charge and square-root kinetic energy,
`FiniteEnergyInputs.representable` produces a representing mixed state
from a one-body trial and its quasi-free realization. The
`physical_aPriori` lemma derives the rough rotated-energy bound from a
finite kinetic trial and the Lieb–Oxford bound. It obtains gas growth from
finite tetrahedron bounds, and measurability from finite energies along a
single convergent sequence. [Physical theorem](TSGA/PhysicalTSGA.lean)

- The spin marginal of a normalized wave is positive semidefinite almost
  everywhere by its Gram matrix formula on square-integrable slices. The
  same holds for a countable mixture, which therefore gives a spin density
  with an everywhere positive semidefinite representative. The integrated
  charge is n in the n-particle sector and the expected number for a mixture.
  Mixing two trial ensembles proves convexity of the constrained search.
  Subtracting the common Hartree term preserves convexity at fixed charge density. A constant
  axial spin rotation on every particle preserves kinetic and interaction
  energy and rotates the marginal by conjugation. This supplies the gas
  symmetry used in Corollary 3.4.
  [Positivity](TSGA/MarginalPositivity.lean) · [Particle number](TSGA/ParticleNumber.lean) ·
  [State mixing](TSGA/StateMixing.lean) · [Axial spin invariance](TSGA/StateSpinRotation.lean)
- For nonconstant rotations, the scalar weak product rule gives an
  L² gradient of the rotated square root with squared norm bounded by twice
  the original kinetic term plus twice the phase kinetic term. For matrix
  powers, a two-eigenbasis argument transfers the scalar Lipschitz constant
  exactly to the Hilbert–Schmidt distance. The remaining weak composition
  input is a Sobolev theorem independent of the density powers.
  [Rotated square root](TSGA/AxialKinetic.lean) · [Spectral estimate](TSGA/SpectralLipschitz.lean) ·
  [Weak composition](TSGA/MatrixChainRule.lean)
- In Lemma 4.13 each occupied wave is multiplied by the tensor product of
  the spatial spin unitaries. Unitarity preserves its spin-summed Coulomb
  expectation. Integrating the first-particle marginal cancels all spectator
  unitaries and gives the full conjugated spin matrix. The kinetic cross term
  satisfies Cauchy–Schwarz for the countable mixture. The analytic input is
  the local weak product rule for arrays of H¹ functions, including zero
  extension for waves supported in a closed ball. Lean proves the scalar
  marginal identity for unbounded nonnegative tests by Fubini and permutation
  symmetry. [Sector rotation](TSGA/LocalRotationWave.lean) ·
  [Mixed states](TSGA/LocalSpinRotation.lean) · [Scalar marginal](TSGA/LocalScalarMarginalProof.lean)
- The physical upper tiles have side length t(ℓ−1) and the lower tiles have
  side length tℓ. Both use smoothing width t and weight 24/(tℓ)³.
  For ℓ = 1/ε their cutoff masses are (1−ε)³ and 1, respectively. If C is
  the reference tetrahedron's Fisher area constant, integrating the cutoff
  Fisher term against a nonnegative L¹ field u costs at most 4Cε ∫u.
  [Physical windows](TSGA/ActualTileCutoffs.lean) · [Cutoff averages](TSGA/ActualTileFisher.lean)
- For the variable phase-rotated density, finite disjoint Fock products
  approximate the countable upper lattice in L¹. The proof unfolds the
  translation and frame averages and controls the periodic skeleton and
  the Hartree variance. The lower estimate minimizes the smeared
  Graf–Schenker bound on the same density. Dilation averaging gives both
  comparisons with an error bounded by a constant times ε times the
  integral of ρ + ρ² + ρ|∇φ|² + |∇√M|².
  [Countable products](TSGA/CountableCoulombBlocks.lean) · [Variable-density localization](TSGA/CoulombActualTiles.lean) · [Signed tile profiles](TSGA/ActualTileAssembly.lean)

### Physical inputs to Theorem 3.3

The hypotheses of the Coulomb theorem are listed in `CoulombModelInputs`.
They include one-body trial identities, Lieb–Oxford, Fock tensorization and
partial traces, constrained-search minimizers and lower semicontinuity, the
state-level Graf–Schenker estimate, scalar skeleton bounds, marked Poisson
laws, Haar averaging, periodic transport, Fourier estimates and weak Sobolev
calculus. The island input `IslandFockInputs.of_compactness` derives its
minimizer field from fixed-charge compactness via Theorem 2.2.
[Attainment in the island construction](TSGA/IslandFockAttainment.lean)

The reference mollifier has support
in the closed ball of radius 1/100. The TSGA model uses three spatial dimensions. The one-body kinetic
bounds and sharpness example also have dimension-parametric proofs.
For the bare Coulomb interaction the quasi-free upper estimate requires
finite Hartree energy. Sobolev embedding and Hardy–Littlewood–Sobolev give
this condition from the density hypotheses for d ≥ 2. In d = 1 the kernel
1/|x−y| can have a divergent direct integral even for smooth densities.
[Model inputs](TSGA/CoulombModelInputs.lean) · [One-body inputs](TSGA/PhysicalTSGA.lean) · [Fock inputs](TSGA/IslandTrialAssembly.lean)

At each center, the physical upper and lower profiles satisfy either the
small-oscillation comparison or the large-oscillation trial bound. A common
integrable function dominates both errors. Integrating it accounts for the
cutoff mass deficit and exterior energy, and gives both signs at the same
scale. The rough energy estimate then extends the result to every ε > 0.
[Signed profiles](TSGA/IntegratedActualTiles.lean) · [Integrated error](TSGA/CoulombTileErrorIntegral.lean) · [Local to global](TSGA/CoulombLocalToGlobal.lean) · [Scale extension](TSGA/CoulombEstimateFromBounds.lean)

- The reference tetrahedron has volume ℓ³/24. Its four face inequalities
  bound the volume of the boundary layer of width w by 1156 ℓ²w for
  0 < w ≤ ℓ. For the smoothed indicator f, strong L² convergence of
  scalar directional difference quotients and this layer bound give
  ∫|∇√f|² ≤ C |Δℓ|/(ℓδ) for every δ > 0. Combining the one-body kinetic
  trial, the finite spiral estimate and Lieb–Oxford gives the rough
  Coulomb bounds uniformly in the tile size, smoothing width, density
  and wavevector. [Tile volume](TSGA/TetrahedronVolume.lean) ·
  [Boundary layer](TSGA/TetrahedronBoundary.lean) ·
  [Directional limits](TSGA/SobolevDirectionalLimits.lean) ·
  [Fisher estimate](TSGA/CutoffGradientBound.lean) · [Rough energy bounds](TSGA/CoulombCutoffArea.lean)
- In each particle sector, permutation symmetry makes every ordered pair
  contribute equally to the Coulomb expectation. Integrating the
  two-particle marginal against 1/(2|x−y|) recovers the mixed-state
  interaction. The exterior island comparison uses this trace identity
  and its integrability directly. [Pair density](TSGA/CoulombPairDensity.lean) ·
  [Exterior trial](TSGA/IslandLocalization.lean)
- Coordinate dilation acts on each normalized antisymmetric wavefunction.
  The Jacobian gives the new marginal, the kinetic factor b² and the Coulomb
  factor b. The inverse map, mixing and Hartree subtraction give the dilation
  law for the constrained search. [Coordinate dilation](TSGA/CoordinateDilation.lean)
- For a bounded domain, the L² difference quotients of the square root of
  its smoothed indicator are bounded by those of the scalar mollifier times
  the square root of the domain volume. The standard scalar H¹ characterization
  gives a weak gradient. The finite kinetic trial then represents the tapered
  matrix on balls and tetrahedra, including a rank-one spin matrix.
  [Scalar cutoff](TSGA/CutoffFisher.lean) · [Finite states](TSGA/CutoffRepresentability.lean)
- At an ordered pair of matrices, the kinetic and Coulomb traces after spin
  removal control the finite-volume cost. Optimizing the two length scales
  yields the cube root of the removed charge fraction. Fixed-charge convexity
  and dilation extend the bound to unordered matrices. Angular transport,
  interpolation of the minority fraction, and a change of trace then yield
  the matrix-root estimate. Joint continuity at the vacuum as well as at
  positive trace gives measurability of the local SSW energy.
  [Angular transport](TSGA/AngularGas.lean) · [Fixed charge](TSGA/CoulombFixedTraceRoot.lean) ·
  [Change of trace](TSGA/RootTraceRegularity.lean) · [Continuity](TSGA/GasContinuity.lean)
- On the gapped branch of Proposition 4.16, a low minority eigenvalue and
  small oscillation force a uniform spectral gap. The explicit spin
  rotation aligns the majority axes. Its weak gradient on the ball satisfies
  r |∇V|² ≤ 192² |∇√M|² by the local Sobolev composition rule.
  [Bloch axis](TSGA/BlochAxis.lean) · [Weak gradient on the comparison ball](TSGA/TileAlignment.lean)
- The missing charge and its compensation are convolutions of two positive
  periodic shells. Coupling the two samples with the same angular coordinate,
  radial volume quantile and smoothing displacement moves each point by at
  most 3s for s = δ/ℓ. Their common mass is at most 3s. The bounded-density
  transport inequality on the flat torus gives a squared homogeneous H⁻¹
  bound of order s³. The averaged Coulomb Fourier estimate supplies the factor
  ℓ² and yields δ³/ℓ. The separate Fourier proof following the manuscript
  uses the pyramid and convolution identities in `SkeletonCoefficients`.
  [Physical shell estimate](TSGA/CoulombShellTransport.lean) ·
  [Coulomb variance](TSGA/CoulombCubicVariance.lean) ·
  [Manuscript Fourier argument](TSGA/SkeletonFourier.lean) ·
  [Peyré, Theorem 2.5](https://www.numdam.org/item/10.1051/cocv/2017050.pdf)
- On a ball satisfying the essential θ-power oscillation test with threshold
  θ/64, the continuous representative gives a common lower and upper
  comparison matrix for every orientation and dilation. The upper tile
  estimate uses the lower matrix and the lower estimate uses the upper matrix.
  The integrated tile proof freezes the wavevector at ∇φ(c).
  The separate estimate in Lemma 4.18 chooses a minimum of |∇φ| on the ball. The construction also covers zero
  charge. The two Poisson additions, the local spin rotations, and the SSW
  finite-size rate give the signed Coulomb estimate for the original density.
  Its error is expressed in ball averages of the mass density, square-root
  kinetic energy, bulk gradient and phase gradient terms. The coefficient is
  uniform in the center and ε. The phase terms have exponent 2p−1. The bulk
  term uses the exponent for the general, minority-floor or global-root
  estimate, with θp = 2 in the global-root case.
  [Small-ball theorem](TSGA/RegularSmallTile.lean) ·
  [Comparison matrices](TSGA/SmallBallAlignment.lean) ·
  [Coulomb replacements](TSGA/SmallBallReplacement.lean) ·
  [Finite-size rate](TSGA/ActualFrozenScale.lean) ·
  [Gas modulus](TSGA/SmallBallGasChoice.lean) ·
  [Error density](TSGA/SmallBallErrorDensity.lean) ·
  [Integration of the error over centers](TSGA/SmallBallIntegratedError.lean)
- On each large-oscillation tile a quasi-free state realizes the
  windowed density. The weak product rule for the matrix square root
  bounds its kinetic energy. Lieb–Oxford supplies the other sign, and
  averaging the two costs gives the rough finite-minus-gas estimate.
  For either taper and all three bulk exponents, the essential oscillation test
  gives a pair of points on the closed comparison ball. The continuous
  representative attains the essential charge supremum there. On a wholly
  active ball the spectral power comparison controls that charge by the
  gradient of the matrix root. On balls meeting the inactive set the
  truncated phase density extends across it with the weighted gradient bound.
  The θ-power test applies in all three regimes. In the global-root estimate
  it implies the root test with threshold κ/(pθ). The resulting Coulomb
  trial and two-sided bound hold for the original density. The generic
  Sobolev–Morrey embedding, ball inequalities and local weak calculus enter
  as explicit analysis inputs.
  [Density representative](TSGA/BallDensityRepresentative.lean) · [Truncated gradient](TSGA/BallTruncatedGradient.lean) · [Active-ball estimate](TSGA/BallActiveMorrey.lean) · [Coulomb tile estimate](TSGA/RegularLargeTile.lean)

The physical tiling theorem takes disjoint Fock tensorization, lower
semicontinuity of the extended constrained search, the Haar frame laws, the
smeared Graf–Schenker inequality, the scalar skeleton mass and Fisher estimates,
the general transport and averaged Fourier inequalities, and standard Sobolev
and one-body results as explicit inputs. Spin removal uses two explicit literature inputs. The first is the partial trace over the discarded spin copy and its finite-sector
spectral decomposition, tested against bounded position, momentum and pair
multipliers of a doubled wave. Lean constructs the doubled wave and pulls
the observables back through its tensor-power isometry. The second is Plancherel
for the spin marginals of one occupied wave, including the first-derivative
identities. Lean obtains the polarized current form and all three localized
observables from these inputs. For Lemma C.1 the shell covariance comes from the mixed Poisson
two-point formula for the nested outer and inner tetrahedra. Its Coulomb
integral and those of the two other fluctuation fields follow from the
single-mark masses, diameters and Schur estimates. The interior matrix
estimate uses the square roots of the background and the combined density.
The two density additions in Proposition 4.16 share the same scalar geometry.
The spin-alignment cost contains the tapered square-root gradient and a term
proportional to |q|² times the squared displacement of the aligning frame.
The phase comparison has the same quarter-oscillation cost in both directions.
Their cutoff averages enter the subsequent tiling argument.
[Spin-axis comparison](TSGA/AlignmentGaugeComparison.lean) · [Phase comparison](TSGA/ConstantWavevectorRotation.lean) · [Shell covariance](TSGA/IslandMaskCovariance.lean) ·
[Interior Fisher estimate](TSGA/IslandInteriorTrial.lean) ·
[Single-mark Fisher estimates](TSGA/IslandSingleFisher.lean) · [Ordered comparisons](TSGA/IslandTrialAssembly.lean)

The island construction uses the stationary marked Poisson process and its
Laplace and Campbell formulas as inputs. The Lean Laplace formula applies when
almost surely only finitely many marks contribute a factor different from one.
The window around each point gives this property for all three cutoffs. The
union of the two windows gives it for the covariance formula. The construction
also uses weak product and composition rules for the cutoffs and the smeared
Graf–Schenker inequality. Its operator inputs include
geometric Fock restriction, disjoint tensorization, measurable selection and
barycentric averaging of normal states, and the finite-system variational
results. The one-body
Fermi-projector trial, quasi-free realization, Lieb–Oxford inequality and
standard Sobolev composition, product and difference-quotient theorems
are explicit analytic inputs. The results use three spatial dimensions.
[Bounded localization tests](TSGA/GeometricSpinTests.lean) · [Fourier convention and moments](TSGA/SectorFourierDensity.lean) · [Lewin, Proposition 3.1](https://arxiv.org/abs/1009.2836) · [Island trials](TSGA/IslandLocalization.lean) ·
[Finite trial inputs](TSGA/PhysicalTSGA.lean) · [Tiling data](TSGA/TSGATiles.lean)
