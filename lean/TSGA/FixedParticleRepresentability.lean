import TSGA.LayerGradient
import TSGA.SpatialFisherDomain
import TSGA.ParticleNumber
import TSGA.MarginalPositivity

/-! # Fixed-particle representability of a spin density

The one-particle marginal supplies the necessity of the square-root condition
by the matrix Hoffmann–Ostenhof theorem. For sufficiency the layer trial gives
a Pauli contraction with the required diagonal. Its trace is the integral of
the charge, so the fixed-trace ensemble realization applies.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory Filter

/-- Particle number is exactly `N` in every component of positive weight. -/
def MixedState.InParticleSector (Γ : MixedState) (N : ℕ) : Prop :=
  ∀ k, 0 < Γ.weight k → (Γ.component k).particles = N

theorem MixedState.InParticleSector.charge {Γ : MixedState} {N : ℕ}
    (h : Γ.InParticleSector N) : (∫ x, (Γ.matrixDensity x).trace.re) = N := by
  rw [Γ.particleNumber]
  have term (k : ℕ) : Γ.weight k * (Γ.component k).particles = Γ.weight k * (N : ℝ) := by
    rcases (Γ.weight_nonneg k).eq_or_lt with hz | hp
    · simp [← hz]
    · rw [h k hp]
  simpa only [term, one_mul] using (Γ.normalized.mul_right (N : ℝ)).tsum_eq

/-- The fixed-particle ensemble realization of a one-body Pauli contraction
of integer trace, in the diagonal and kinetic observables used here. -/
def CanonicalEnsembleRealization : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ γ : OneBody, (∑' k, γ.occupation k) = N →
    ∃ Γ : MixedState, Γ.InParticleSector N ∧ feasible γ.matrixDensity Γ ∧ Γ.kinetic = γ.kinetic

private theorem weakPartial_univ_iff {i : Fin 3} {f g : Position → ℂ} :
    WeakPartialOn Set.univ i f g ↔ Spatial.WeakPartial i f g := by
  simp [WeakPartialOn, Spatial.WeakPartial, locallyIntegrableOn_univ]

/-- Apply the dimension-independent natural-orbital theorem to the one-body
marginal of the three-dimensional constrained search. -/
theorem OneBody.density_domain (γ : OneBody) (D : Density)
    (hd : γ.matrixDensity =ᵐ[volume] D.matrix)
    (chain : Spatial.RankOneRootChain 3) (closed : Spatial.ClosedFisherConvexity 3) :
    (∫ x, D.charge x) = ∑' k, γ.occupation k ∧ ∃ S : MatrixGradient, SqrtRegular D S := by
  let g : Spatial.OneBody 3 := {
    occupation := γ.occupation, occupation_mem := γ.occupation_mem, finite_trace := γ.finite_trace
    orbital := γ.orbital, orbital_L2 := γ.orbital_L2, orthonormal := γ.orthonormal
    gradient := γ.gradient, weak := fun k s i => weakPartial_univ_iff.mp (γ.weak k s i)
    gradient_L2 := γ.gradient_L2, finite_kinetic := γ.finite_kinetic }
  let A : Spatial.Density 3 := ⟨D.matrix, D.positive⟩
  obtain ⟨mass, S, reg, _, _⟩ := Spatial.hoffmann_ostenhof_oneBody_domain chain closed g A hd
  exact ⟨mass, S, reg.charge, fun i j k => weakPartial_univ_iff.mpr (reg.weak i j k), reg.grad⟩

/-- Gontier's characterization (Theorem 2.1). Positivity is bundled in
the representative `D`, while equality of densities is almost everywhere. -/
theorem fixedParticle_representability
    {cTF κ₁ κ₂ : ℝ} (trial : LayerConstruction cTF κ₁ κ₂)
    (canonical : CanonicalEnsembleRealization) (marg : OneBodyMarginals)
    (chain : Spatial.RankOneRootChain 3) (closed : Spatial.ClosedFisherConvexity 3)
    (M : Position → SpinMatrix) {N : ℕ} (hN : 0 < N) :
    (∃ Γ : MixedState, Γ.InParticleSector N ∧ feasible M Γ) ↔
    ∃ (D : Density) (S : MatrixGradient), M =ᵐ[volume] D.matrix ∧
      SqrtRegular D S ∧ (∫ x, D.charge x) = N := by
  constructor
  · rintro ⟨Γ, sector, hΓ⟩
    obtain ⟨γ, density, _⟩ := marg.marginal Γ
    obtain ⟨_, S, reg⟩ := γ.density_domain Γ.density (density.trans Γ.feasible_density) chain closed
    refine ⟨Γ.density, S, hΓ.symm.trans Γ.feasible_density, reg, ?_⟩
    exact (integral_congr_ae (Γ.feasible_density.symm.mono fun x hx =>
      congrArg (fun A : SpinMatrix => A.trace.re) hx)).trans sector.charge
  · rintro ⟨D, S, hd, reg, mass⟩
    obtain ⟨w, _, _⟩ := trial D S reg 1 zero_lt_one
    have htrace := (w.gamma.density_domain D w.density chain closed).1
    obtain ⟨Γ, sector, hΓ, _⟩ := canonical N hN w.gamma (htrace.symm.trans mass)
    exact ⟨Γ, sector, (hΓ.trans w.density).trans hd.symm⟩

/-- A pure one-electron marginal has rank at most one at every point.
The spectator space consists of the empty configuration. -/
theorem Wave.oneParticle_det_zero (ψ : Wave 1) (x : Position) :
    (ψ.matrixDensity x).det = 0 := by
  simp [Matrix.det_fin_two, Wave.matrixDensity, Measure.volume_pi_eq_dirac (0 : Space 0)]
  ring

end TSGA.ManyBody
