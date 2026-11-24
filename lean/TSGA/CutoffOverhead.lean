import TSGA.LocalizationAssembly
import TSGA.ErrorDensity

/-! # Cutoff costs in the signed TSGA tile comparison

Missing mass multiplies the signed reference energy. The cutoff kinetic cost
multiplies the charge. These contributions therefore require different
pointwise bounds before summing the translated tiles.
-/

namespace TSGA.Localization

open MeasureTheory

/-- The mass defect, averaged cutoff kinetic energy, exterior error and
per-volume cost before the signed comparison is integrated over space. -/
structure CutoffControl (P : TileProfile) (D : Density) (φ : Phase) (S : MatrixGradient)
    (δ A : ℝ) : Prop where
  charge_eq : P.charge = D.charge
  missing_mass : 1 - (∫ z, P.cutoff z) ≤ A * δ
  kinetic_mass : (∫ z, P.kineticKernel z) ≤ A * δ
  exterior : ∀ᵐ x, P.exterior x ≤ A * (δ * massDensity D φ x + kineticDensity S x / δ)
  volumeCost : ∀ᵐ x, P.volumeCost x ≤ A * (δ * massDensity D φ x + kineticDensity S x / δ)

/-- The signed upper and lower comparisons have the same cutoff constant.
Only the SSW growth bound is needed to pay for the missing cutoff mass. -/
theorem CutoffControl.bound {P : TileProfile} {D : Density} {φ : Phase} {S : MatrixGradient}
    {δ A A₀ σ : ℝ} {F : GasEnergies} (H : CutoffControl P D φ S δ A)
    (rough : APriori F A₀) (hδ : 0 < δ) (hA : 0 ≤ A) (hA₀ : 0 ≤ A₀)
    (hσ : σ = 1 ∨ σ = -1) :
    ∀ᵐ x, P.exterior x + (∫ z, P.cutoff z) * P.volumeCost x +
      (∫ z, P.kineticKernel z) * P.charge x +
      ((∫ z, P.cutoff z) - 1) * (σ * localEnergy F D φ x) ≤
      (3 * A + A * A₀) * (δ * massDensity D φ x + kineticDensity S x / δ) := by
  let m := ∫ z, P.cutoff z
  have hm : 0 ≤ m := integral_nonneg_of_ae P.cutoff_nonneg
  have hm' : m ≤ 1 := P.cutoff_mass_le_one
  have hs : |σ| = 1 := hσ.elim (fun h => by simp [h]) (fun h => by simp [h])
  filter_upwards [H.exterior, H.volumeCost] with x hext hvol
  let a := massDensity D φ x
  let k := kineticDensity S x / δ
  have ha : 0 ≤ a := massDensity_nonneg D φ x
  have hk : 0 ≤ k := div_nonneg (sq_nonneg _) hδ.le
  have hcharge : D.charge x ≤ a := by
    unfold a massDensity
    linarith only [sq_nonneg (D.charge x), mul_nonneg (D.charge_nonneg x) (sq_nonneg ‖φ.grad x‖)]
  have hbase : 0 ≤ A * (δ * a + k) := by positivity
  have hvolume : m * P.volumeCost x ≤ A * (δ * a + k) := by
    calc
      _ ≤ m * (A * (δ * a + k)) := mul_le_mul_of_nonneg_left hvol hm
      _ ≤ 1 * (A * (δ * a + k)) := mul_le_mul_of_nonneg_right hm' hbase
      _ = _ := one_mul _
  have hkin : (∫ z, P.kineticKernel z) * P.charge x ≤ A * (δ * a + k) := by
    rw [H.charge_eq]
    calc
      _ ≤ (A * δ) * a := mul_le_mul H.kinetic_mass hcharge (D.charge_nonneg x) (mul_nonneg hA hδ.le)
      _ ≤ _ := by nlinarith only [mul_nonneg hA hk]
  have he : |localEnergy F D φ x| ≤ A₀ * a := rough.gas_growth (D.matrix x) (D.positive x) _
  have hmiss : (m - 1) * (σ * localEnergy F D φ x) ≤ (A * A₀) * (δ * a + k) := by
    calc
      _ ≤ |(m - 1) * (σ * localEnergy F D φ x)| := le_abs_self _
      _ = (1 - m) * |localEnergy F D φ x| := by
        rw [abs_mul, abs_mul, hs, one_mul, abs_of_nonpos (sub_nonpos.mpr hm')]
        ring
      _ ≤ (A * δ) * (A₀ * a) :=
        mul_le_mul H.missing_mass he (abs_nonneg _) (mul_nonneg hA hδ.le)
      _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg hA hA₀) hk]
  change P.exterior x ≤ A * (δ * a + k) at hext
  change P.exterior x + m * P.volumeCost x + _ + (m - 1) * _ ≤ (3 * A + A * A₀) * (δ * a + k)
  linarith only [hvolume, hkin, hmiss, hext]

end TSGA.Localization
