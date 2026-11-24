import TSGA.LocalErrorTerms
import TSGA.TilingBounds
import TSGA.BulkTile
import TSGA.PhaseTile
import TSGA.ReplacementScale
import TSGA.FrozenTile

/-! # Finite localization inputs for the transverse spin-gradient approximation

In a signed comparison, the family of tapered energies is averaged over
orientations, dilations and the finite tile index. Its local comparison leaves
two scalar errors at each center, before Young's inequality is applied.
-/

noncomputable section

namespace TSGA.Localization

open MeasureTheory PhaseLocalization

/-- A uniform bound for the bulk, phase, and direct gradient terms on a
comparison ball. At the sharp exponent this depends only on p and A. -/
def ballCoefficient (p A : ℝ) : ℝ := 2 * A + tileConstant p A

/-- Tiling geometry, integrability, and local Sobolev estimates for one sign. The
signs +1 and −1 can use different cutoffs. The charge and the tapered energy
are those of the given density field in both cases. -/
structure SignedTilingData (F : GasEnergies) (mode : BulkRegime) (D : Density) (φ : Phase)
    (S T G : MatrixGradient) (p θ δ A σ : ℝ) where
  tiles : AveragedTiles
  profile : TileProfile
  energy_integrable : tiles.EnergyIntegrable F D φ
  cutoff_eq : profile.cutoff = tiles.cutoffProfile
  energy_eq : profile.tileEnergy = fun c => σ * tiles.energy F D φ c
  radius_le : profile.radius ≤ A / δ
  bulkError : Position → ℝ
  phaseError : Position → ℝ
  tiling : FiniteTilingLaws F tiles profile D φ S δ A σ
  bulk : ∀ᵐ c, mode.TileInput p θ δ A (ballAverage profile.radius (massDensity D φ) c)
    (ballAverage profile.radius (bulkDensity mode T G p) c) (bulkError c)
  phase : ∀ᵐ c, RepresentativeTileInput D φ G p δ A profile.radius c (phaseError c)

/-- One centerwise comparison completes the finite data. -/
structure SignedTileComparison (F : GasEnergies) (mode : BulkRegime) (D : Density) (φ : Phase)
    (S T G : MatrixGradient) (p θ δ A σ : ℝ) extends SignedTilingData F mode D φ S T G p θ δ A σ where
  comparison : FrozenTileComparison F D φ tiles profile θ σ (fun c => bulkError c + phaseError c +
    A * (ballAverage profile.radius (rootPower T p) c / δ ^ mode.replacementExponent p θ))

theorem SignedTileComparison.toTileSide {F : GasEnergies} {mode : BulkRegime}
    {D : Density} {φ : Phase} {S T G : MatrixGradient} {p θ ν δ A σ A₀ : ℝ}
    (P : SignedTileComparison F mode D φ S T G p θ δ A σ)
    (rough : APriori F A₀) (hA₀ : 0 ≤ A₀) (hσ : σ = 1 ∨ σ = -1)
    (hp : 3 < p) (hpθ : 2 ≤ p * θ) (hδ : 0 < δ) (hle : δ ≤ 1) (hA : 1 ≤ A)
    (hD : DensityRegular D p θ S T) (hφ : PhaseAdmissible D p φ G)
    (hr : RegimeHyp mode ν D G p) :
    TileSide (σ * rotatedEnergy F D φ) (fun x => σ * localEnergy F D φ x)
      (scaleCostDensity ((3*A + A*A₀) + ballCoefficient p A) δ (mode.exponent p θ) (2 * p - 1)
        (massDensity D φ) (kineticDensity S) (bulkDensity mode T G p) (phaseDensity D φ G p)) := by
  let m := massDensity D φ
  let u := bulkDensity mode T G p
  let v := phaseDensity D φ G p
  let b := mode.exponent p θ
  let k := 2 * p - 1
  let J := ballCoefficient p A
  have ha : 0 ≤ A := zero_le_one.trans hA
  have ht := tileConstant_nonneg p ha
  have hj : 0 ≤ J := by dsimp [J, ballCoefficient]; linarith
  have hm := massDensity_integrable hD hφ
  have hu := bulkDensity_integrable (by linarith : 0 < p) hD hr
  have hv := phaseDensity_integrable hφ
  obtain ⟨cutoff, localization⟩ := P.tiling.assemble hδ hle hm (kineticDensity_integrable hD)
    P.cutoff_eq P.energy_eq
  let Q : TileProfile := { P.profile with
    ballCost := ballCostDensity J δ b k m u v
    ballCost_integrable := ballCost_integrable J δ b k hm hu hv }
  let raw := fun c => P.bulkError c + P.phaseError c +
    A * (ballAverage Q.radius (rootPower T p) c / δ ^ mode.replacementExponent p θ)
  apply TileSide.of_local_domination Q raw localization (P.comparison.estimate hσ P.energy_eq P.cutoff_eq)
  · filter_upwards [P.bulk, P.phase] with c hbulk hphase
    have hM := ballAverage_nonnegative Q.radius (massDensity_nonneg D φ) c
    have hU := ballAverage_nonnegative Q.radius (bulkDensity_nonneg mode T G p) c
    have hV := ballAverage_nonnegative Q.radius (phaseDensity_nonneg D φ G p) c
    have hT := rootPower_integrable (by linarith : 0 < p) hD.theta_Lp
    have hT₀ := ballAverage_nonnegative Q.radius (rootPower_nonneg T p) c
    have hTU : ballAverage Q.radius (rootPower T p) c ≤ ballAverage Q.radius u c := by
      apply ballAverage_mono Q.radius hT hu
      exact ae_of_all _ (rootPower_le_bulkDensity mode T G p)
    have h1 := hbulk.bound hp hpθ hδ ha hM hU
    have h2 := hphase.bound hp hδ hle hA Q.radius_pos hD.charge_L1 hm hφ
    let x := δ * ballAverage Q.radius m c
    let y := ballAverage Q.radius u c / δ ^ b
    let z := ballAverage Q.radius v c / δ ^ k
    change P.bulkError c ≤ A * (x + y) at h1
    change P.phaseError c ≤ tileConstant p A * (x + z) at h2
    have hx : 0 ≤ x := mul_nonneg hδ.le hM
    have hy : 0 ≤ y := div_nonneg hU (Real.rpow_nonneg hδ.le _)
    have hz : 0 ≤ z := div_nonneg hV (Real.rpow_nonneg hδ.le _)
    have hreplace : A * (ballAverage Q.radius (rootPower T p) c / δ ^ mode.replacementExponent p θ)
        ≤ A * y :=
      mul_le_mul_of_nonneg_left ((mode.replacement_cost_le p θ hδ hle hT₀).trans
        (div_le_div_of_nonneg_right hTU (Real.rpow_nonneg hδ.le _))) ha
    change raw c ≤ ballAverage Q.radius (ballCostDensity J δ b k m u v) c
    rw [ballAverage_ballCost Q.radius J δ b k hm hu hv]
    change P.bulkError c + P.phaseError c + _ ≤ (2 * A + tileConstant p A) * (x + y + z)
    nlinarith only [h1, h2, hreplace, mul_nonneg ha hx, mul_nonneg ht hy, mul_nonneg ha hz]
  · filter_upwards [cutoff.bound rough hδ ha hA₀ hσ] with x ho
    let m' := δ * m x
    let s' := kineticDensity S x / δ
    let u' := u x / δ ^ b
    let v' := v x / δ ^ k
    have hs : 0 ≤ s' := div_nonneg (sq_nonneg _) hδ.le
    have hU : 0 ≤ u' := div_nonneg (bulkDensity_nonneg ..) (Real.rpow_nonneg hδ.le _)
    have hV : 0 ≤ v' := div_nonneg (phaseDensity_nonneg ..) (Real.rpow_nonneg hδ.le _)
    let K := 3*A + A*A₀
    have hk : 0 ≤ K := by dsimp [K]; positivity
    change P.profile.exterior x + _ + _ + _ ≤ K * (m' + s') at ho
    change P.profile.exterior x + _ + _ + J * (m' + u' + v') + _ ≤ (K + J) * (m' + s' + u' + v')
    linarith only [ho, mul_nonneg hj hs, mul_nonneg hk hU, mul_nonneg hk hV]

end TSGA.Localization
