import TSGA.MainTheorem
import TSGA.ErrorScale
import TSGA.TSGATiles
import TSGA.SharpInterpolation
import TSGA.ExtendedEstimate

/-! # Theorem 3.3, the transverse spin-gradient approximation

The proof integrates the two signed comparisons, applies the local bulk and
phase estimates and chooses the localization scale. The physics inputs are
finite tile energy comparisons and whole-space a priori bounds.
-/

noncomputable section

namespace TSGA.Localization

open MeasureTheory PhaseLocalization

/-- The finite comparisons at all sufficiently small scales for one
polarization regime. Both signs use the same constants. -/
def FiniteComparisons (F : GasEnergies) (mode : BulkRegime) (ν p θ A τ : ℝ) : Prop :=
  ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular D p θ S T →
    PhaseAdmissible D p φ G → RegimeHyp mode ν D G p →
    ∀ δ : ℝ, 0 < δ → δ ≤ τ → δ ≤ 1 → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      Nonempty (SignedTileComparison F mode D φ S T G p θ δ A σ)

/-- The small-scale threshold and finite comparison constants may depend
on the indicated parameters. The global-root comparison is required at
the single matrix power 2/p. -/
structure TSGALocalization (F : GasEnergies) : Prop where
  general : ∀ p θ : ℝ, 3 < p → 0 < θ → θ < 1 → 2 ≤ p * θ →
    ∃ A ≥ 1, ∃ τ > 0, FiniteComparisons F .general 0 p θ A τ
  minority : ∀ p θ ν : ℝ, 3 < p → 0 < θ → θ < 1 → 2 ≤ p * θ → 0 < ν → ν ≤ 1/2 →
    ∃ A ≥ 1, ∃ τ > 0, FiniteComparisons F .minority ν p θ A τ
  sharp : ∀ p : ℝ, 3 < p → ∃ A ≥ 1, ∃ τ > 0,
    FiniteComparisons F .globalRoot 0 p (2/p) A τ

/-- The uniform estimate expressed in terms of the four spatial error densities. -/
private def FieldEstimate (F : GasEnergies) (mode : BulkRegime) (ν p θ b C : ℝ) : Prop :=
  ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular D p θ S T →
    PhaseAdmissible D p φ G → RegimeHyp mode ν D G p → ∀ ε : ℝ, 0 < ε →
    Integrable (localEnergy F D φ) ∧
    |rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| ≤
      ε * (∫ x, massDensity D φ x) + C * (1 + ε) / ε * (∫ x, kineticDensity S x) +
      C / ε ^ b * (∫ x, bulkDensity mode T G p x) +
      C / ε ^ (2 * p - 1) * (∫ x, phaseDensity D φ G p x)

private theorem fieldEstimate_of_tiles {F : GasEnergies} {A₀ A τ p b : ℝ}
    (rough : APriori F A₀) (hA₀ : 0 ≤ A₀) (hA : 1 ≤ A) (hτ : 0 < τ) (hp : 3 < p) :
    ∃ C > 0, ∀ (mode : BulkRegime) (ν θ : ℝ), 0 < θ → 2 ≤ p * θ → mode.exponent p θ = b →
      FiniteComparisons F mode ν p θ A τ → FieldEstimate F mode ν p θ b C := by
  let J := (3*A + A*A₀) + ballCoefficient p A
  let L := max (2 * A₀) J
  have ha : 0 ≤ A := zero_le_one.trans hA
  have hJ : 0 < J := by
    dsimp [J, ballCoefficient]
    linarith [tileConstant_nonneg p ha, mul_nonneg ha hA₀]
  have hL := hJ.trans_le (le_max_right (2*A₀) J)
  obtain ⟨C, hC, normalize⟩ := extend_small_scale hL (lt_min hτ zero_lt_one) b (2 * p - 1)
  refine ⟨C, hC, ?_⟩
  intro mode ν θ hθ hpθ hb tiles D φ S T G hD hφ hr ε hε
  let m := massDensity D φ
  let s := kineticDensity S
  let u := bulkDensity mode T G p
  let v := phaseDensity D φ G p
  have hm := massDensity_integrable hD hφ
  have hs := kineticDensity_integrable hD
  have hu := bulkDensity_integrable (by linarith : 0 < p) hD hr
  have hv := phaseDensity_integrable hφ
  have hm₀ : 0 ≤ ∫ x, m x := integral_nonneg (massDensity_nonneg D φ)
  have hs₀ : 0 ≤ ∫ x, s x := integral_nonneg fun x => sq_nonneg _
  have hu₀ : 0 ≤ ∫ x, u x := integral_nonneg (bulkDensity_nonneg mode T G p)
  have hv₀ : 0 ≤ ∫ x, v x := integral_nonneg (phaseDensity_nonneg D φ G p)
  obtain ⟨href, hrough⟩ := rough.rough_bound hA₀ hp hθ hD hφ
  refine ⟨href, normalize hm₀ hs₀ hu₀ hv₀ (hrough.trans ?_) ?_ ε hε⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hm₀ hs₀)
  · intro δ hδ hle
    have h₁ := hle.trans (min_le_right τ 1)
    let cost := scaleCostDensity J δ b (2 * p - 1) m s u v
    have side (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
        TileSide (σ * rotatedEnergy F D φ) (fun x => σ * localEnergy F D φ x) cost := by
      obtain ⟨P⟩ := tiles D φ S T G hD hφ hr δ hδ (hle.trans (min_le_left τ 1)) h₁ σ hσ
      simpa only [hb] using P.toTileSide rough hA₀ hσ hp hpθ hδ h₁ hA hD hφ hr
    have hcost : Integrable cost := scaleCost_integrable J δ b (2*p-1) hm hs hu hv
    have up : TileSide (rotatedEnergy F D φ) (localEnergy F D φ) cost := by
      simpa only [one_mul] using side 1 (Or.inl rfl)
    have lo : TileSide (-rotatedEnergy F D φ) (-localEnergy F D φ) cost := by
      simpa only [neg_one_mul, Pi.neg_def] using side (-1) (Or.inr rfl)
    have hbound := abs_error_of_tiles href hcost up lo
    rw [show (∫ x, cost x) = _ from integral_scaleCost J δ b (2*p-1) hm hs hu hv] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by positivity))

end TSGA.Localization

namespace TSGA

open MeasureTheory TSGA.Localization PhaseLocalization

/-- The finite tile estimates imply both bounds of Theorem 3.3 and the
additional bound under a positive minority-density hypothesis. -/
theorem tsga_theorem {F : GasEnergies} {A₀ : ℝ} (rough : APriori F A₀) (hA₀ : 0 ≤ A₀)
    (tiles : TSGALocalization F) (chain : WeakPowerComparison) : MainTSGAEstimate F := by
  constructor
  · intro p θ hp hθ hθ' hpθ
    obtain ⟨A, hA, τ, hτ, htiles⟩ := tiles.general p θ hp hθ hθ' hpθ
    obtain ⟨C, hC, bound⟩ := fieldEstimate_of_tiles (b := bulkExponent p θ) rough hA₀ hA hτ hp
    refine ⟨C, hC, ?_⟩
    intro D S T _ hD φ G hφ ε hε
    have h := bound .general 0 θ hθ hpθ rfl htiles D φ S T G hD hφ trivial ε hε
    refine ⟨h.1, ?_⟩
    simpa only [rotatedEnergy, localEnergy, tsgaError, massDensity, kineticDensity, bulkDensity,
      rootPower, integral_phaseDensity hφ] using h.2
  · intro p θ ν hp hθ hθ' hpθ hν hν'
    obtain ⟨A, hA, τ, hτ, htiles⟩ := tiles.minority p θ ν hp hθ hθ' hpθ hν hν'
    obtain ⟨C, hC, bound⟩ := fieldEstimate_of_tiles (b := polarizedBulkExponent p θ) rough hA₀ hA hτ hp
    refine ⟨C, hC, ?_⟩
    intro D S T hminor hD φ G hφ ε hε
    have h := bound .minority ν θ hθ hpθ rfl htiles D φ S T G hD hφ hminor ε hε
    refine ⟨h.1, ?_⟩
    simpa only [rotatedEnergy, localEnergy, tsgaError, massDensity, kineticDensity, bulkDensity,
      rootPower, integral_phaseDensity hφ] using h.2
  · intro p hp
    obtain ⟨A, hA, τ, hτ, htiles⟩ := tiles.sharp p hp
    obtain ⟨C, hC, bound⟩ := fieldEstimate_of_tiles (b := 2*p-1) rough hA₀ hA hτ hp
    apply sharp_from_two_div hp hC chain
    intro D S T G hD hweak hglob φ hφ ε hε
    have hp₀ : 0 < p := by linarith
    have hθ : 0 < 2 / p := div_pos (by norm_num) hp₀
    have hpθ : 2 ≤ p * (2 / p) := by rw [mul_div_cancel₀ _ hp₀.ne']
    have h := bound .globalRoot 0 (2/p) hθ hpθ rfl htiles
      D φ S T G hD hφ ⟨hweak,hglob⟩ ε hε
    have hT := rootPower_integrable (by linarith : 0 < p) hD.theta_Lp
    have hG := rootPower_integrable (by linarith : 0 < p) hglob
    refine ⟨h.1, ?_⟩
    have hbulk : (∫ x, bulkDensity .globalRoot T G p x) =
        (∫ x, rootPower T p x) + ∫ x, rootPower G p x := integral_add hT hG
    apply h.2.trans_eq
    rw [hbulk, integral_phaseDensity hφ]
    unfold tsgaError massDensity kineticDensity rootPower
    ring

/-- The full statement with the nonnegative phase remainders allowed to be
infinite. The local energy is integrable under the stated phase kinetic
bound, whether or not the error estimate is finite. -/
theorem tsga_theorem_extended {F : GasEnergies} {A₀ : ℝ} (rough : APriori F A₀)
    (hA₀ : 0 ≤ A₀) (tiles : TSGALocalization F) (chain : WeakPowerComparison) :
    MainExtendedTSGAEstimate F :=
  extended_of_mainTSGA (tsga_theorem rough hA₀ tiles chain) rough

end TSGA
