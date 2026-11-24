import TSGA.Sobolev
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening

/-! # Domains and smoothing for the thermodynamic SSW limit

The cutoff is the convolution in `eq:spiral_limit`. The last lemmas verify the
scale choice in Steps 2 and 3 of the proof.
-/

noncomputable section

namespace TSGA.SSW

open Filter MeasureTheory
open scoped Topology InnerProductSpace Convolution

/-- A radial unit-mass kernel with finite kinetic energy of its square root. -/
structure Mollifier where
  kernel : Position → ℝ
  radial : ∀ x y, ‖x‖ = ‖y‖ → kernel x = kernel y
  nonneg : ∀ x, 0 ≤ kernel x
  compact : HasCompactSupport kernel
  integrable : Integrable kernel
  mass : ∫ x, kernel x = 1
  sqrt_gradient : ∃ G : Position → Position,
    (∀ i, WeakPartialOn Set.univ i (fun x => Real.sqrt (kernel x)) (fun x => G x i)) ∧ MemLp G 2

def Mollifier.scaled (χ : Mollifier) (δ : ℝ) (x : Position) : ℝ :=
  (δ ^ 3)⁻¹ * χ.kernel (δ⁻¹ • x)

theorem Mollifier.scaled_integrable (χ : Mollifier) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (χ.scaled δ) :=
  (χ.integrable.comp_smul (inv_ne_zero hδ.ne')).const_mul _

theorem Mollifier.scaled_mass (χ : Mollifier) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, χ.scaled δ x = 1 := by
  rw [show (∫ x, χ.scaled δ x) = _ from integral_const_mul _ _,
    Measure.integral_comp_inv_smul_of_nonneg volume χ.kernel hδ.le, χ.mass]
  simp [smul_eq_mul, finrank_euclideanSpace, hδ.ne']

/-- An indicator convolved with the kernel rescaled to width `δ`. -/
def smoothedIndicator (Ω : Set Position) (χ : Mollifier) (δ : ℝ) : Position → ℝ := by
  classical
  exact Ω.indicator (fun _ => (1 : ℝ)) ⋆ χ.scaled δ

/-- A constant spin matrix rotated through the phase `q · x` and multiplied by a cutoff. -/
def cutoffSpiral (f : Position → ℝ) (M : SpinMatrix) (q x : Position) : SpinMatrix :=
  (f x : ℂ) • rotate (⟪q, x⟫_ℝ) M

@[simp] theorem cutoffSpiral_zero_matrix (f : Position → ℝ) (q x : Position) :
    cutoffSpiral f 0 q x = 0 := by simp [cutoffSpiral, rotate]

@[simp] theorem cutoffSpiral_zero_wavevector (f : Position → ℝ) (M : SpinMatrix) (x : Position) :
    cutoffSpiral f M 0 x = (f x : ℂ) • M := by simp [cutoffSpiral]

/-- The real Lebesgue volume, used for the bounded open regions below. -/
def regionVolume (U : Set Position) : ℝ := volume.real U

/-- Geometric hypotheses of `thm:spiral_limit`, including the outer smoothing
width and a single kernel used throughout the sequence. -/
structure DomainSequence where
  region : ℕ → Set Position
  region_open : ∀ n, IsOpen (region n)
  region_connected : ∀ n, IsConnected (region n)
  region_bounded : ∀ n, Bornology.IsBounded (region n)
  vol_tendsto : Tendsto (fun n => regionVolume (region n)) atTop atTop
  boundary : ∃ C : ℝ, 0 < C ∧ ∀ n r, 0 < r → r ≤ regionVolume (region n) ^ (1 / 3 : ℝ) / C →
    volume (Metric.thickening r (frontier (region n))) ≤
      ENNReal.ofReal (C * r * regionVolume (region n) ^ (2 / 3 : ℝ))
  delta : ℕ → ℝ
  delta_pos : ∀ n, 0 < delta n
  delta_ratio : Tendsto (fun n => delta n / regionVolume (region n) ^ (1 / 3 : ℝ)) atTop (𝓝 0)
  delta_product : Tendsto (fun n => delta n * regionVolume (region n) ^ (1 / 3 : ℝ)) atTop atTop
  mollifier : Mollifier

namespace DomainSequence

variable (D : DomainSequence)

def vol (n : ℕ) : ℝ := regionVolume (D.region n)

theorem vol_pos (n : ℕ) : 0 < D.vol n :=
  ENNReal.toReal_pos ((D.region_open n).measure_pos volume (D.region_connected n).nonempty).ne'
    (D.region_bounded n).measure_lt_top.ne

def length (n : ℕ) : ℝ := D.vol n ^ (1 / 3 : ℝ)

def tileLength (n : ℕ) : ℝ := D.vol n ^ (1 / 6 : ℝ)

theorem tileLength_pos (n : ℕ) : 0 < D.tileLength n := Real.rpow_pos_of_pos (D.vol_pos n) _

theorem length_tendsto : Tendsto D.length atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp D.vol_tendsto

theorem tileLength_tendsto : Tendsto D.tileLength atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp D.vol_tendsto

/-- The smoothed indicator of the physical domain at its outer cutoff scale. -/
def cutoff (n : ℕ) : Position → ℝ :=
  smoothedIndicator (D.region n) D.mollifier (D.delta n)

/-- Normalization of the cutoff gives the finite spiral particle number. -/
theorem cutoff_mass (n : ℕ) : ∫ x, D.cutoff n x = D.vol n := by
  classical
  have hregion : Integrable ((D.region n).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff (D.region_open n).measurableSet).2
      (integrableOn_const (D.region_bounded n).measure_lt_top.ne)
  rw [cutoff, smoothedIndicator, integral_convolution _ hregion (D.mollifier.scaled_integrable (D.delta_pos n)),
    D.mollifier.scaled_mass (D.delta_pos n), integral_indicator (D.region_open n).measurableSet]
  simp [vol, regionVolume]

/-- The density matrix `U_q M U_q* (1_Ω ∗ χ_δ)` as a field on Euclidean space. -/
def spiralField (M : SpinMatrix) (n : ℕ) (q x : Position) : SpinMatrix :=
  cutoffSpiral (D.cutoff n) M q x

/-- The spatial integral of the charge has the normalization used in the
finite variational formula, independent of the wavevector. -/
theorem spiralField_particleNumber (M : SpinMatrix) (n : ℕ) (q : Position) :
    (∫ x, (D.spiralField M n q x).trace.re) = M.trace.re * D.vol n := by
  simp only [spiralField, cutoffSpiral, Matrix.trace_smul, trace_rotate, smul_eq_mul, Complex.re_ofReal_mul,
    integral_mul_const, D.cutoff_mass]
  exact mul_comm _ _

def totalEnergy (E : (Position → SpinMatrix) → ℝ) (M : SpinMatrix) (n : ℕ)
    (q : Position) : ℝ := E (D.spiralField M n q)

def energyDensity (E : (Position → SpinMatrix) → ℝ) (M : SpinMatrix) (n : ℕ)
    (q : Position) : ℝ := D.totalEnergy E M n q / D.vol n

/-- Outer boundary fraction for inner smoothing width one. -/
def boundaryFraction (n : ℕ) : ℝ := (D.tileLength n + 1 + D.delta n) / D.length n

theorem boundaryFraction_tendsto_zero : Tendsto D.boundaryFraction atTop (𝓝 0) := by
  have hratio : Tendsto (fun n => D.tileLength n / D.length n) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp D.vol_tendsto
    convert h using 1
    funext n
    change D.vol n ^ (1 / 6 : ℝ) / D.vol n ^ (1 / 3 : ℝ) = D.vol n ^ (-(1 / 6 : ℝ))
    rw [← Real.rpow_sub (D.vol_pos n)]
    norm_num
  have hlength : Tendsto (fun n => (D.length n)⁻¹) atTop (𝓝 0) :=
    D.length_tendsto.inv_tendsto_atTop
  have hδ : Tendsto (fun n => D.delta n / D.length n) atTop (𝓝 0) := D.delta_ratio
  change Tendsto (fun n => (D.tileLength n + 1 + D.delta n) / D.length n) atTop (𝓝 0)
  simpa only [add_div, one_div, zero_add] using (hratio.add hlength).add hδ

/-- The three vanishing scale factors controlling the lower and upper comparisons. -/
def error (n : ℕ) : ℝ :=
  (D.tileLength n)⁻¹ + D.boundaryFraction n + (D.delta n * D.length n)⁻¹

theorem error_tendsto_zero : Tendsto D.error atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (D.tileLength n)⁻¹) atTop (𝓝 0) := D.tileLength_tendsto.inv_tendsto_atTop
  have ho : Tendsto (fun n => (D.delta n * D.length n)⁻¹) atTop (𝓝 0) :=
    D.delta_product.inv_tendsto_atTop
  exact (show Tendsto (fun n => (D.tileLength n)⁻¹ + D.boundaryFraction n +
    (D.delta n * D.length n)⁻¹) atTop (𝓝 0) by
    simpa only [zero_add] using (hi.add D.boundaryFraction_tendsto_zero).add ho)

/-- Error in Step 3 with inner width one. The three coefficients collect the
fixed-density and fixed-wavevector factors on the boundary, cutoff and skeleton. -/
theorem upperError_tendsto_zero (A B C : ℝ) :
    Tendsto (fun n => A * ((D.tileLength n)⁻¹ + D.boundaryFraction n) +
      B * ((D.tileLength n)⁻¹ + (D.delta n * D.length n)⁻¹) + C / D.tileLength n)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (D.tileLength n)⁻¹) atTop (𝓝 0) := D.tileLength_tendsto.inv_tendsto_atTop
  have houter : Tendsto (fun n => (D.delta n * D.length n)⁻¹) atTop (𝓝 0) :=
    D.delta_product.inv_tendsto_atTop
  simpa only [mul_zero, zero_add, add_zero, div_eq_mul_inv] using
    (((hi.add D.boundaryFraction_tendsto_zero).const_mul A).add ((hi.add houter).const_mul B)).add
      (hi.const_mul C)

end DomainSequence
end TSGA.SSW
