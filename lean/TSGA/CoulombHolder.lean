import TSGA.CoulombRegularity
import TSGA.OrderedGas
import TSGA.GasContinuity
import TSGA.CutoffRepresentability
import TSGA.CutoffFisher

/-! # Coulomb gas regularity in the TSGA theorem

The matrix bound uses spin removal on finite Coulomb states, the finite
tiling rate, fixed-charge convexity, and coordinate dilation. Joint continuity
then gives the local measurability required in Theorem 3.3.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW TSGA.Localization
open scoped ComplexOrder

/-- Proposition E.2(v), with one constant for all matrices and wavevectors. -/
theorem coulomb_ssw_holder {η : Mollifier} {J K cLO : ℝ}
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ)
    (rate : FiniteRateTiling energy η K) (removal : SpiralRemovalTrials η J) (hc : 0 ≤ cLO)
    (lo : ∀ D : Density, ∀ Γ, feasible D.matrix Γ →
      -cLO * (∫ x, D.charge x^(4/3 : ℝ)) ≤ indirectAt D.matrix Γ) :
    ∃ C > 0, ∀ {A B : SpinMatrix}, A.PosSemidef → B.PosSemidef → ∀ q : Position,
      let r := max A.trace.re B.trace.re
      0 < r → |sswEnergy energy η A q - sswEnergy energy η B q| ≤
        C*holderGrowth r q*(hilbertSchmidt (A-B)/r)^(1/3:ℝ) := by
  let gas := coulomb_sswGas η loc states
  obtain ⟨C, hC, ho⟩ := ordered_ssw_holder rate (removal.withLiebOxford lo)
  have hK := zero_le_one.trans rate.one_le
  let R := 2*(cLO+2*K)+2*(2*K+1)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨100*C+100*R+8*K, by positivity, ?_⟩
  intro A B hA hB q r hr
  apply holder_of_ordered_and_ray (fun P => sswEnergy energy η P q) q hK hC.le hR
    (fun hP => rate.abs_le_holderGrowth hP q) (fun _ ht => coulomb_ssw_convex_fixed_charge η loc states ht q)
    _ (fun {P Q} hP hQP hQ => ho P Q hP hQP hQ q) hA hB hr
  intro P hP α ha ha'
  exact gas.ray_lipschitz rate hc hP q ha ha' (ssw_scaling gas hc lo P hP q
    (fun n => SpiralKinematics.representable states P hP n q) ha ha')

/-- On each tetrahedron the scalar cutoff has an H¹ square root. The
finite-energy construction therefore supplies the starting state for spin removal. -/
theorem spiralRemovalTrials_of_frames {η : Mollifier} (H : FiniteEnergyInputs)
    (sob : SobolevDifferenceQuotients)
    (frames : ∀ ℓ > 0, ∀ δ > 0, δ ≤ ℓ → ∀ q : Position,
      Nonempty (OrderedSpiralFrame (smoothedIndicator (tetrahedron ℓ) η δ) (regionVolume (tetrahedron ℓ)) q)) :
    SpiralRemovalTrials η (max 1 tetrahedronDirectConstant) := by
  refine ⟨le_max_left .., le_max_right .., frames, ?_⟩
  intro A ha ℓ hℓ δ hδ _
  have hv := tetrahedron_volume_pos hℓ
  have hi := Integrable.of_integral_ne_zero ((tile_cutoff_mass η hℓ hδ).trans_ne hv.ne')
  obtain ⟨g, hw, hg⟩ := smoothedIndicator_sqrt_sobolev sob (tetrahedron_open ℓ).measurableSet
    (ENNReal.toReal_pos_iff.mp hv).2.ne η hδ
  obtain ⟨Γ, hΓ⟩ := H.representable_cutoff (fun x => (smoothedIndicator_bounds _ η hδ x).1) hi g hw hg ha
  exact ⟨⟨Γ,hΓ⟩⟩

/-- The extended TSGA theorem with local measurability supplied by continuity
of the same gas that occurs in the energy estimate. -/
theorem levyLieb_tsga_of_spin_removal {η : Mollifier} {K : ℝ}
    (H : FiniteEnergyInputs) (chain : WeakPhaseProduct) (sobolev : SobolevLipschitzComposition)
    (rate : FiniteRateTiling energy η K)
    (differences : SobolevDifferenceQuotients)
    (frames : ∀ ℓ > 0, ∀ δ > 0, δ ≤ ℓ → ∀ q : Position,
      Nonempty (OrderedSpiralFrame (smoothedIndicator (tetrahedron ℓ) η δ) (regionVolume (tetrahedron ℓ)) q))
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ)
    (tiles : TSGALocalization (referenceEnergies energy η)) :
    MainExtendedTSGAEstimate (referenceEnergies energy η) := by
  have lo (D : Density) (Γ : MixedState) (hΓ : feasible D.matrix Γ) :
      -H.loCoeff * (∫ x, D.charge x^(4/3:ℝ)) ≤ indirectAt D.matrix Γ := by
    change _ ≤ Γ.interaction - hartree D.charge
    have h := H.liebOxford D Γ hΓ
    unfold chargeMoment at h
    linarith only [h]
  have removal := spiralRemovalTrials_of_frames H differences frames
  obtain ⟨_, _, hmat⟩ := coulomb_ssw_holder loc states rate removal H.lo_nonneg lo
  have hcont := continuous_ssw_of_holder (coulomb_sswGas η loc states) rate hmat
  obtain ⟨A, hA, rough⟩ := physical_aPriori_of_local_measurable H chain rate
    (fun _ _ hD hφ => local_ssw_measurable_of_continuous hcont hD hφ)
  exact tsga_theorem_extended rough hA tiles (weakPowerComparison_of_sobolev sobolev)

end TSGA.ManyBody
