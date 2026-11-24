import TSGA.ErrorDensity
import TSGA.BulkLocalization
import TSGA.LocalizationAssembly

/-! # The four spatial error integrals in Theorem 3.3 -/

noncomputable section

namespace TSGA.Localization

open MeasureTheory PhaseLocalization

/-- The sharp alternative uses both unweighted matrix gradients. -/
def bulkDensity (mode : BulkRegime) (T G : MatrixGradient) (p : ℝ) (x : Position) : ℝ :=
  match mode with
  | .general | .minority => rootPower T p x
  | .globalRoot => rootPower T p x + rootPower G p x

def RegimeHyp (mode : BulkRegime) (ν : ℝ) (D : Density) (G : MatrixGradient) (p : ℝ) : Prop :=
  match mode with
  | .general => True
  | .minority => MinorityBound ν D
  | .globalRoot => IsMatrixGradientOn Set.univ (D.power (1 / p)) G ∧
      MemLp (matrixGradNorm G) (ENNReal.ofReal p)

theorem rootPower_le_bulkDensity (mode : BulkRegime) (T G : MatrixGradient) (p : ℝ) (x : Position) :
    rootPower T p x ≤ bulkDensity mode T G p x := by
  cases mode with
  | general | minority => exact le_rfl
  | globalRoot => exact le_add_of_nonneg_right (rootPower_nonneg G p x)

theorem bulkDensity_nonneg (mode : BulkRegime) (T G : MatrixGradient) (p : ℝ) (x : Position) :
    0 ≤ bulkDensity mode T G p x := by
  cases mode
  · exact rootPower_nonneg ..
  · exact rootPower_nonneg ..
  · exact add_nonneg (rootPower_nonneg ..) (rootPower_nonneg ..)

theorem bulkDensity_integrable {D : Density} {p θ ν : ℝ} {S T G : MatrixGradient}
    {mode : BulkRegime} (hp : 0 < p) (h : DensityRegular D p θ S T) (hr : RegimeHyp mode ν D G p) :
    Integrable (bulkDensity mode T G p) := by
  cases mode
  · exact rootPower_integrable hp h.theta_Lp
  · exact rootPower_integrable hp h.theta_Lp
  · exact (rootPower_integrable hp h.theta_Lp).add (rootPower_integrable hp hr.2)

/-- Normalized error from integrating a comparison ball. The square-root
gradient is carried by the cutoff term separately. -/
def ballCostDensity (J δ b k : ℝ) (mass bulk phase : Position → ℝ) (x : Position) : ℝ :=
  J * (δ * mass x + bulk x / δ ^ b + phase x / δ ^ k)

def scaleCostDensity (L δ b k : ℝ) (mass kin bulk phase : Position → ℝ) (x : Position) : ℝ :=
  L * (δ * mass x + kin x / δ + bulk x / δ ^ b + phase x / δ ^ k)

theorem ballCost_integrable (J δ b k : ℝ) {m u v : Position → ℝ}
    (hm : Integrable m) (hu : Integrable u) (hv : Integrable v) :
    Integrable (ballCostDensity J δ b k m u v) :=
  (((hm.const_mul δ).add (hu.div_const _)).add (hv.div_const _)).const_mul J

theorem scaleCost_integrable (L δ b k : ℝ) {m s u v : Position → ℝ}
    (hm : Integrable m) (hs : Integrable s) (hu : Integrable u) (hv : Integrable v) :
    Integrable (scaleCostDensity L δ b k m s u v) :=
  ((((hm.const_mul δ).add (hs.div_const δ)).add (hu.div_const _)).add (hv.div_const _)).const_mul L

theorem integral_scaleCost (L δ b k : ℝ) {m s u v : Position → ℝ}
    (hm : Integrable m) (hs : Integrable s) (hu : Integrable u) (hv : Integrable v) :
    (∫ x, scaleCostDensity L δ b k m s u v x) =
      L * (δ * (∫ x, m x) + (∫ x, s x) / δ + (∫ x, u x) / δ ^ b + (∫ x, v x) / δ ^ k) := by
  have hms : Integrable (fun x => δ * m x + s x / δ) := (hm.const_mul δ).add (hs.div_const δ)
  have hmsu : Integrable (fun x => δ * m x + s x / δ + u x / δ ^ b) := hms.add (hu.div_const _)
  simp only [scaleCostDensity, integral_const_mul, integral_add hmsu (hv.div_const (δ ^ k)),
    integral_add hms (hu.div_const (δ ^ b)), integral_add (hm.const_mul δ) (hs.div_const δ), integral_div]

theorem ballAverage_ballCost (R J δ b k : ℝ) {m u v : Position → ℝ}
    (hm : Integrable m) (hu : Integrable u) (hv : Integrable v) (c : Position) :
    ballAverage R (ballCostDensity J δ b k m u v) c =
      J * (δ * ballAverage R m c + ballAverage R u c / δ ^ b + ballAverage R v c / δ ^ k) := by
  have hmu : IntegrableOn (fun x => δ * m x + u x / δ ^ b) (Metric.ball c R) :=
    (hm.integrableOn.const_mul δ).add (hu.integrableOn.div_const _)
  simp only [ballAverage, ballIntegral, ballCostDensity, integral_const_mul,
    integral_add hmu (hv.integrableOn.div_const (δ ^ k)),
    integral_add (hm.integrableOn.const_mul δ) (hu.integrableOn.div_const (δ ^ b)), integral_div]
  ring

theorem ballAverage_nonnegative (R : ℝ) {f : Position → ℝ} (hf : ∀ x, 0 ≤ f x) (c : Position) :
    0 ≤ ballAverage R f c := div_nonneg (integral_nonneg hf) ENNReal.toReal_nonneg

end TSGA.Localization
