import TSGA.CoulombModel
import TSGA.IntegratedScaleCost

/-! # From the integrated Coulomb bounds to the TSGA and LSDA estimates -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization PhaseLocalization SSW

/-- The two signs have been summed at a common localization scale. The
constant and threshold are chosen before the density and its phase. -/
def CoulombSmallScaleBound (η : Mollifier) (mode : BulkRegime) (ν p θ A τ : ℝ) : Prop :=
  ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular D p θ S T →
    PhaseAdmissible D p φ G → RegimeHyp mode ν D G p → ∀ ε : ℝ, 0 < ε → ε ≤ τ →
    let F := referenceEnergies energy η
    |rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| ≤ A*integratedScaleCost mode D φ S T G p θ ε

theorem CoulombGasInputs.aPriori {η : Mollifier} {K : ℝ} (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (chain : WeakPhaseProduct) (sob : SobolevDifferenceQuotients) :
    ∃ A ≥ 0, APriori (referenceEnergies energy η) A := by
  obtain ⟨_,_,hmat⟩ := coulomb_ssw_holder L.localization (L.kinematics H sob) L.rate
    (L.removal H sob) H.lo_nonneg H.indirect_lower
  have joint := continuous_ssw_of_holder (coulomb_sswGas η L.localization (L.kinematics H sob))
    L.rate hmat
  exact physical_aPriori_of_local_measurable H chain L.rate
    (fun _ _ reg phase => local_ssw_measurable_of_continuous joint reg phase)

/-- Choose the scale once for the regime, using the global a priori bound
when the requested mass coefficient is large. -/
private theorem normalize_on_phases {η : Mollifier} {mode : BulkRegime} {A τ A₀ ν p θ : ℝ}
    (rough : APriori (referenceEnergies energy η) A₀) (hA₀ : 0 ≤ A₀) (hp : 3 < p) (hθ : 0 < θ)
    (hA : 1 ≤ A) (hτ : 0 < τ) (allowed : Phase → Prop)
    (bound : ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular D p θ S T →
      PhaseAdmissible D p φ G → RegimeHyp mode ν D G p → allowed φ → ∀ ε : ℝ, 0 < ε → ε ≤ τ →
      let F := referenceEnergies energy η
      |rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| ≤ A*integratedScaleCost mode D φ S T G p θ ε) :
    ∃ C > 0, ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular D p θ S T →
      PhaseAdmissible D p φ G → RegimeHyp mode ν D G p → allowed φ → ∀ ε : ℝ, 0 < ε →
      let F := referenceEnergies energy η
      Integrable (localEnergy F D φ) ∧
      |rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| ≤
        ε*(∫ x, massDensity D φ x) + C*(1+ε)/ε*(∫ x, kineticDensity S x) +
        C/ε^(mode.exponent p θ)*(∫ x, bulkDensity mode T G p x) +
        C/ε^(2*p-1)*(∫ x, phaseDensity D φ G p x) := by
  let L := max (2*A₀) A
  have hL : 0 < L := (zero_lt_one.trans_le hA).trans_le (le_max_right ..)
  obtain ⟨C,hC,scales⟩ := extend_small_scale hL hτ (mode.exponent p θ) (2*p-1)
  refine ⟨C,hC,?_⟩
  intro D φ S T G reg phase regime usePhase ε he F
  obtain ⟨hi,hrough⟩ := rough.rough_bound hA₀ hp hθ reg phase
  have hm : 0 ≤ ∫ x, massDensity D φ x := integral_nonneg (massDensity_nonneg D φ)
  have hs : 0 ≤ ∫ x, kineticDensity S x := integral_nonneg fun _ => sq_nonneg _
  have hu : 0 ≤ ∫ x, bulkDensity mode T G p x := integral_nonneg (bulkDensity_nonneg mode T G p)
  have hv : 0 ≤ ∫ x, phaseDensity D φ G p x := integral_nonneg (phaseDensity_nonneg D φ G p)
  refine ⟨hi,scales hm hs hu hv
    (hrough.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (add_nonneg hm hs))) ?_ ε he⟩
  intro δ hδ hδτ
  exact (bound D φ S T G reg phase regime usePhase δ hδ hδτ).trans
    (mul_le_mul_of_nonneg_right (le_max_right ..) (integratedScaleCost_nonneg mode D φ S T G p θ hδ))

theorem normalize_coulomb_scale {η : Mollifier} {mode : BulkRegime} {A τ A₀ ν p θ : ℝ}
    (rough : APriori (referenceEnergies energy η) A₀) (hA₀ : 0 ≤ A₀) (hp : 3 < p) (hθ : 0 < θ)
    (hA : 1 ≤ A) (hτ : 0 < τ) (bound : CoulombSmallScaleBound η mode ν p θ A τ) :
    ∃ C > 0, ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular D p θ S T →
      PhaseAdmissible D p φ G → RegimeHyp mode ν D G p → ∀ ε : ℝ, 0 < ε →
      let F := referenceEnergies energy η
      Integrable (localEnergy F D φ) ∧
      |rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| ≤
        ε*(∫ x, massDensity D φ x) + C*(1+ε)/ε*(∫ x, kineticDensity S x) +
        C/ε^(mode.exponent p θ)*(∫ x, bulkDensity mode T G p x) +
        C/ε^(2*p-1)*(∫ x, phaseDensity D φ G p x) := by
  obtain ⟨C,hC,allScales⟩ := normalize_on_phases rough hA₀ hp hθ hA hτ (fun _ => True)
    (fun D φ S T G reg phase regime _ => bound D φ S T G reg phase regime)
  exact ⟨C,hC,fun D φ S T G reg phase regime => allScales D φ S T G reg phase regime trivial⟩

/-- The conditional zero-phase improvement only needs the sharper small-scale
bound at zero phase. -/
theorem lsda_of_unrestricted_small_scale {η : Mollifier} {p θ A τ A₀ : ℝ}
    (rough : APriori (referenceEnergies energy η) A₀) (hA₀ : 0 ≤ A₀)
    (hp : 3 < p) (hθ : 0 < θ) (hA : 1 ≤ A) (hτ : 0 < τ)
    (bound : ∀ (D : Density) (S T : MatrixGradient), DensityRegular D p θ S T →
      ∀ ε : ℝ, 0 < ε → ε ≤ τ →
      let F := referenceEnergies energy η
      |rotatedEnergy F D Phase.zero - ∫ x, localEnergy F D Phase.zero x| ≤
        A*integratedScaleCost .minority D Phase.zero S T 0 p θ ε) :
    ∃ C > 0, LSDAEstimate (referenceEnergies energy η) (fun _ => True) p θ (polarizedBulkExponent p θ) C := by
  let F := referenceEnergies energy η
  have hp₀ : 0 < p := by linarith
  obtain ⟨C,hC,allScales⟩ := normalize_on_phases (mode := .minority) (ν := 0) rough hA₀ hp hθ
    hA hτ (fun φ => φ = Phase.zero) (by
      intro D φ S T G reg phase _ hz ε he hle
      subst φ
      simpa [integratedScaleCost,phaseDensity,weightedRoot,bulkDensity,Phase.hessianNorm,Phase.zero,Real.zero_rpow (by linarith : p ≠ 0)] using bound D S T reg ε he hle)
  refine ⟨C,hC,?_⟩
  intro D S T _ reg ε he
  have minor : MinorityBound 0 D := ae_of_all _ fun x => by simpa using D.positive x
  have phase := phaseAdmissible_zero D hp₀ (0 : MatrixGradient)
  obtain ⟨hi,h⟩ := allScales D Phase.zero S T 0 reg phase minor rfl ε he
  have eq : localEnergy F D Phase.zero = fun x => F.ueg (D.matrix x) := funext fun x =>
    F.zero_mode _ (D.positive x)
  refine ⟨eq ▸ hi,?_⟩
  change |rotatedEnergy F D Phase.zero - ∫ x, localEnergy F D Phase.zero x| ≤ _ at h
  rw [eq] at h
  simpa [F,rotatedEnergy,Phase.zero,Phase.hessianNorm,lsdaError,kineticDensity,bulkDensity,
    rootPower,phaseDensity,weightedRoot,BulkRegime.exponent,massDensity,Real.zero_rpow hp₀.ne'] using h

/-- Normalize the integrated comparisons in all three regimes. Global
matrix-root control is used at the endpoint θ = 2/p. The weak power
comparison then gives one constant for every admissible θ at fixed p. -/
theorem levyLieb_tsga_of_small_scale_bounds {η : Mollifier} {K : ℝ}
    (H : FiniteEnergyInputs) (L : CoulombGasInputs η K) (chain : WeakPhaseProduct)
    (comp : SobolevLipschitzComposition) (sob : SobolevDifferenceQuotients)
    (general : ∀ p θ : ℝ, 3 < p → 0 < θ → θ < 1 → 2 ≤ p*θ →
      ∃ A ≥ 1, ∃ τ > 0, CoulombSmallScaleBound η .general 0 p θ A τ)
    (minority : ∀ p θ ν : ℝ, 3 < p → 0 < θ → θ < 1 → 2 ≤ p*θ → 0 < ν → ν ≤ 1/2 →
      ∃ A ≥ 1, ∃ τ > 0, CoulombSmallScaleBound η .minority ν p θ A τ)
    (sharp : ∀ p : ℝ, 3 < p →
      ∃ A ≥ 1, ∃ τ > 0, CoulombSmallScaleBound η .globalRoot 0 p (2/p) A τ) :
    MainExtendedTSGAEstimate (referenceEnergies energy η) := by
  obtain ⟨A₀,hA₀,rough⟩ := L.aPriori H chain sob
  apply extended_of_mainTSGA _ rough
  constructor
  · intro p θ hp hθ hθ' hpθ
    obtain ⟨A,hA,τ,hτ,bound⟩ := general p θ hp hθ hθ' hpθ
    obtain ⟨C,hC,allScales⟩ := normalize_coulomb_scale rough hA₀ hp hθ hA hτ bound
    refine ⟨C,hC,?_⟩
    intro D S T _ reg φ G phase ε he
    obtain ⟨hi,h⟩ := allScales D φ S T G reg phase trivial ε he
    refine ⟨hi,?_⟩
    simpa only [rotatedEnergy,localEnergy,tsgaError,massDensity,kineticDensity,bulkDensity,
      rootPower,integral_phaseDensity phase,BulkRegime.exponent] using h
  · intro p θ ν hp hθ hθ' hpθ hν hν'
    obtain ⟨A,hA,τ,hτ,bound⟩ := minority p θ ν hp hθ hθ' hpθ hν hν'
    obtain ⟨C,hC,allScales⟩ := normalize_coulomb_scale rough hA₀ hp hθ hA hτ bound
    refine ⟨C,hC,?_⟩
    intro D S T minor reg φ G phase ε he
    obtain ⟨hi,h⟩ := allScales D φ S T G reg phase minor ε he
    refine ⟨hi,?_⟩
    simpa only [rotatedEnergy,localEnergy,tsgaError,massDensity,kineticDensity,bulkDensity,
      rootPower,integral_phaseDensity phase,BulkRegime.exponent] using h
  · intro p hp
    obtain ⟨A,hA,τ,hτ,bound⟩ := sharp p hp
    have hp₀ : 0 < p := by linarith
    obtain ⟨C,hC,allScales⟩ := normalize_coulomb_scale rough hA₀ hp (div_pos (by norm_num) hp₀) hA hτ bound
    apply sharp_from_two_div hp hC (weakPowerComparison_of_sobolev comp)
    intro D S T G reg weak globalRoot φ phase ε he
    obtain ⟨hi,h⟩ := allScales D φ S T G reg phase ⟨weak,globalRoot⟩ ε he
    have split : (∫ x, bulkDensity .globalRoot T G p x) =
        (∫ x, rootPower T p x) + ∫ x, rootPower G p x :=
      integral_add (rootPower_integrable hp₀ reg.theta_Lp) (rootPower_integrable hp₀ globalRoot)
    refine ⟨hi,h.trans_eq ?_⟩
    rw [split,integral_phaseDensity phase]
    unfold tsgaError massDensity kineticDensity rootPower BulkRegime.exponent
    ring

end TSGA.ManyBody

namespace TSGA

/-- At zero phase the active set is empty. Both bounds in the LSDA
corollary use only the square-root and θ-power gradient of the density. -/
theorem MainExtendedTSGAEstimate.lsda {F : GasEnergies} (H : MainExtendedTSGAEstimate F)
    {p θ : ℝ} (hp : 3 < p) (hlo : 2/p ≤ θ) (hhi : θ < 1) :
    (∃ C > 0, LSDAEstimate F (fun _ => True) p θ (bulkExponent p θ) C) ∧
      (∀ ν : ℝ, 0 < ν → ν ≤ 1/2 → ∃ C > 0,
        LSDAEstimate F (MinorityBound ν) p θ (polarizedBulkExponent p θ) C) :=
  mainLSDA_of_mainTSGA H.toFinite hp hlo hhi

end TSGA
