import TSGA.LocalEstimate
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Linarith

/-! # Summing the center-wise comparisons in the proof of Theorem 3.3

The tile energy is averaged over the internal tile parameters at fixed center.
Translation integration of a cutoff gives its mass. A ball error contributes
its spatial integral after division by the volume of the comparison ball.
-/

noncomputable section

namespace TSGA.Localization

open MeasureTheory
open scoped Convolution

/-- Integral against the profile of a translated tile, including any fixed
cell-volume normalization. The profile is written in the reflected coordinate
`c - x`. -/
def cutoffAverage (χ f : Position → ℝ) (c : Position) : ℝ := (f ⋆ χ) c

theorem cutoffAverage_integrable {χ f : Position → ℝ} (hχ : Integrable χ) (hf : Integrable f) :
    Integrable (cutoffAverage χ f) :=
  hf.integrable_convolution _ hχ

theorem integral_cutoffAverage {χ f : Position → ℝ} (hχ : Integrable χ) (hf : Integrable f) :
    (∫ c, cutoffAverage χ f c) = (∫ x, χ x) * ∫ x, f x := by
  change (∫ c, (f ⋆ χ) c) = _
  rw [integral_convolution _ hf hχ]
  exact mul_comm _ _

theorem cutoffAverage_add {χ f g : Position → ℝ} (hχ : Integrable χ)
    (hf : Integrable f) (hg : Integrable g) :
    ∀ᵐ c, cutoffAverage χ (f + g) c = cutoffAverage χ f c + cutoffAverage χ g c := by
  filter_upwards [hf.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hχ,
    hg.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hχ] with c hfc hgc
  exact hfc.add_distrib hgc

theorem cutoffAverage_mono {χ f g : Position → ℝ} (hχ : Integrable χ)
    (hχ₀ : ∀ᵐ x, 0 ≤ χ x) (hf : Integrable f) (hg : Integrable g) (hfg : f ≤ᵐ[volume] g) :
    ∀ᵐ c, cutoffAverage χ f c ≤ cutoffAverage χ g c := by
  filter_upwards [hf.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hχ,
    hg.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hχ] with c hfc hgc
  apply integral_mono_ae hfc hgc
  filter_upwards [hfg, (quasiMeasurePreserving_sub_left_of_right_invariant volume c).ae hχ₀]
    with x hx hχx
  exact mul_le_mul_of_nonneg_right hx hχx

def ballIntegral (R : ℝ) (f : Position → ℝ) (c : Position) : ℝ := ∫ x in Metric.ball c R, f x

def ballVolume (R : ℝ) : ℝ := volume.real (Metric.ball (0 : Position) R)

def ballAverage (R : ℝ) (f : Position → ℝ) (c : Position) : ℝ :=
  ballIntegral R f c / ballVolume R

private def ballKernel (R : ℝ) : Position → ℝ :=
  (Metric.ball (0 : Position) R).indicator fun _ => 1

private theorem ballKernel_integrable (R : ℝ) : Integrable (ballKernel R) := by
  apply (integrable_indicator_iff measurableSet_ball).2
  exact integrableOn_const (measure_ball_lt_top (μ := (volume : Measure Position)) (x := (0 : Position)) (r := R)).ne

private theorem ballKernel_mass (R : ℝ) : (∫ x, ballKernel R x) = ballVolume R := by
  simp [ballKernel, integral_indicator measurableSet_ball, ballVolume]

private theorem cutoffAverage_ballKernel (R : ℝ) (f : Position → ℝ) :
    cutoffAverage (ballKernel R) f = ballIntegral R f := by
  funext c
  change (∫ x, f x * ballKernel R (c - x)) = ∫ x in Metric.ball c R, f x
  rw [← integral_indicator measurableSet_ball]
  congr 1
  funext x
  have hmem : c - x ∈ Metric.ball (0 : Position) R ↔ x ∈ Metric.ball c R := by
    simp only [Metric.mem_ball, dist_zero_right, ← dist_eq_norm c x, dist_comm c x]
  by_cases h : x ∈ Metric.ball c R
  · simp [ballKernel, h, hmem.mpr h]
  · simp [ballKernel, h, mt hmem.mp h]

theorem ballIntegral_integrable (R : ℝ) {f : Position → ℝ} (hf : Integrable f) :
    Integrable (ballIntegral R f) := by
  rw [← cutoffAverage_ballKernel]
  exact cutoffAverage_integrable (ballKernel_integrable R) hf

/-- Every spatial point belongs to comparison balls with a set of centers of
Lebesgue measure exactly `ballVolume R`. -/
theorem integral_ballIntegral (R : ℝ) {f : Position → ℝ} (hf : Integrable f) :
    (∫ c, ballIntegral R f c) = ballVolume R * ∫ x, f x := by
  rw [← cutoffAverage_ballKernel, integral_cutoffAverage (ballKernel_integrable R) hf, ballKernel_mass]

theorem ballVolume_pos {R : ℝ} (hR : 0 < R) : 0 < ballVolume R :=
  ENNReal.toReal_pos ((Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hR)).ne')
    (measure_ball_lt_top (μ := (volume : Measure Position)) (x := (0 : Position)) (r := R)).ne

/-- Ball error terms divided by the cell volume scale uniformly in ℓ in
three dimensions. -/
theorem ballVolume_scaled {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) :
    ballVolume (ℓ * R) = ℓ ^ 3 * ballVolume R := by
  simp only [ballVolume, measureReal_def, Measure.addHaar_ball_mul_of_pos volume (0 : Position) hℓ,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hℓ.le _), finrank_euclideanSpace,
    Fintype.card_fin]

theorem ballAverage_integrable (R : ℝ) {f : Position → ℝ} (hf : Integrable f) :
    Integrable (ballAverage R f) := (ballIntegral_integrable R hf).div_const _

theorem integral_ballAverage {R : ℝ} (hR : 0 < R) {f : Position → ℝ} (hf : Integrable f) :
    (∫ c, ballAverage R f c) = ∫ x, f x := by
  simp only [ballAverage, integral_div, integral_ballIntegral R hf]
  exact mul_div_cancel_left₀ _ (ballVolume_pos hR).ne'

theorem ballAverage_add (R : ℝ) {f g : Position → ℝ} (hf : Integrable f) (hg : Integrable g)
    (c : Position) :
    ballAverage R (fun x => f x + g x) c = ballAverage R f c + ballAverage R g c := by
  rw [ballAverage, ballIntegral, integral_add hf.integrableOn hg.integrableOn, add_div]
  rfl

theorem ballAverage_mono (R : ℝ) {f g : Position → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hfg : f ≤ᵐ[volume] g) (c : Position) : ballAverage R f c ≤ ballAverage R g c :=
  div_le_div_of_nonneg_right
    (integral_mono_ae hf.integrableOn hg.integrableOn (ae_restrict_of_ae hfg)) ENNReal.toReal_nonneg

/-- Tile label, orientation and dilation can be sampled as one parameter.
The nonnegative weight carries the number of labels and inverse cell volume.
The shapes are in reflected coordinates, so a tile centered at `c` has
cutoff `shape i (c - x)`. -/
structure AveragedTiles where
  Parameter : Type
  [space : MeasurableSpace Parameter]
  measure : Measure Parameter
  probability : IsProbabilityMeasure measure
  weight : Parameter → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  shape : Parameter → Position → ℝ
  shape_mem : ∀ i x, shape i x ∈ Set.Icc 0 1
  profile_integrable : ∀ z, Integrable (fun i => weight i * shape i z) measure

def AveragedTiles.cutoffProfile (T : AveragedTiles) (z : Position) : ℝ := by
  letI := T.space
  exact ∫ i, T.weight i * T.shape i z ∂T.measure

/-- Average of the finite-system energy of the actual taper of the spin
density at fixed center, using the same weights as `cutoffProfile`. -/
def AveragedTiles.energy (T : AveragedTiles) (F : GasEnergies) (D : Density)
    (φ : Phase) (c : Position) : ℝ := by
  letI := T.space
  exact ∫ i, T.weight i * F.energy (fun x =>
    (T.shape i (c - x) : ℂ) • rotate (φ.value x) (D.matrix x)) ∂T.measure

/-- Integrability in the internal parameters where the nonlinear localized
energy is evaluated. Integrability in the outer center variable is recorded
in `TileProfile`. -/
def AveragedTiles.EnergyIntegrable (T : AveragedTiles) (F : GasEnergies) (D : Density)
    (φ : Phase) : Prop := by
  letI := T.space
  exact ∀ᵐ c, Integrable (fun i => T.weight i * F.energy (fun x =>
    (T.shape i (c - x) : ℂ) • rotate (φ.value x) (D.matrix x))) T.measure

/-- Fubini identifies the mean of the cutoff linear terms with convolution
against the averaged cutoff profile. The finite tile energy itself can be
nonlinear in the tapered field. -/
theorem cutoffAverage_parameter_integral {ι : Type*} [MeasurableSpace ι]
    (μ : Measure ι) [SFinite μ] (weight : ι → ℝ) (shape : ι → Position → ℝ)
    (f : Position → ℝ) (c : Position)
    (h : Integrable (fun p : Position × ι => f p.1 * (weight p.2 * shape p.2 (c - p.1)))
      (volume.prod μ)) :
    cutoffAverage (fun z => ∫ i, weight i * shape i z ∂μ) f c =
      ∫ i, weight i * cutoffAverage (shape i) f c ∂μ := by
  calc
    _ = ∫ x, ∫ i, f x * (weight i * shape i (c - x)) ∂μ := by
      change (∫ x, f x * ∫ i, weight i * shape i (c - x) ∂μ) = _
      simp_rw [integral_const_mul]
    _ = ∫ i, ∫ x, f x * (weight i * shape i (c - x)) ∂volume ∂μ := integral_integral_swap h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with i
      change (∫ x, f x * (weight i * shape i (c - x))) = weight i * ∫ x, f x * shape i (c - x)
      simp_rw [mul_left_comm (f _) (weight i), integral_const_mul]

/-- Cell-normalized profiles at one scale for either sign of the localization.
The upper cutoff can have mass less than one. Its deficit is accounted for
in `densityCost`. `kineticKernel` is the averaged squared gradient of the
cutoff square root, including its coefficient in the energy comparison. -/
structure TileProfile where
  cutoff : Position → ℝ
  kineticKernel : Position → ℝ
  radius : ℝ
  radius_pos : 0 < radius
  tileEnergy : Position → ℝ
  volumeCost : Position → ℝ
  charge : Position → ℝ
  ballCost : Position → ℝ
  exterior : Position → ℝ
  cutoff_integrable : Integrable cutoff
  cutoff_nonneg : ∀ᵐ x, 0 ≤ cutoff x
  cutoff_mass_le_one : (∫ x, cutoff x) ≤ 1
  kinetic_integrable : Integrable kineticKernel
  kinetic_nonneg : ∀ᵐ x, 0 ≤ kineticKernel x
  tile_integrable : Integrable tileEnergy
  volumeCost_integrable : Integrable volumeCost
  charge_integrable : Integrable charge
  ballCost_integrable : Integrable ballCost
  exterior_integrable : Integrable exterior

def TileProfile.localBase (P : TileProfile) (reference : Position → ℝ) (c : Position) : ℝ :=
  cutoffAverage P.cutoff reference c + cutoffAverage P.cutoff P.volumeCost c +
    cutoffAverage P.kineticKernel P.charge c

def TileProfile.densityCost (P : TileProfile) (reference : Position → ℝ) (x : Position) : ℝ :=
  P.exterior x + (∫ z, P.cutoff z) * P.volumeCost x + (∫ z, P.kineticKernel z) * P.charge x +
    P.ballCost x + ((∫ z, P.cutoff z) - 1) * reference x

/-- Inputs to the integration over centers. `tileEnergy` already includes the
averages over shapes, rotations and dilations; the comparison ball and the
cutoff convolutions are still located at each individual center. -/
def TileSide (energy : ℝ) (reference cost : Position → ℝ) : Prop :=
  ∃ P : TileProfile, energy ≤ (∫ c, P.tileEnergy c) + ∫ x, P.exterior x ∧
    (∀ᵐ c, P.tileEnergy c ≤ P.localBase reference c + ballAverage P.radius P.ballCost c) ∧
    (∀ᵐ x, P.densityCost reference x ≤ cost x)

theorem TileSide.of_local_domination {energy : ℝ} {reference cost : Position → ℝ}
    (P : TileProfile) (raw : Position → ℝ)
    (hglobal : energy ≤ (∫ c, P.tileEnergy c) + ∫ x, P.exterior x)
    (hlocal : ∀ᵐ c, P.tileEnergy c ≤ P.localBase reference c + raw c)
    (hraw : ∀ᵐ c, raw c ≤ ballAverage P.radius P.ballCost c)
    (hc : ∀ᵐ x, P.densityCost reference x ≤ cost x) :
    TileSide energy reference cost := by
  refine ⟨P, hglobal, ?_, hc⟩
  filter_upwards [hlocal, hraw] with c h h'
  exact h.trans (by linarith)

theorem TileSide.bound {energy : ℝ} {reference cost : Position → ℝ}
    (h : TileSide energy reference cost) (href : Integrable reference) (hcost : Integrable cost) :
    energy - (∫ x, reference x) ≤ ∫ x, cost x := by
  obtain ⟨P, hglobal, hloc, hc⟩ := h
  have hRef := cutoffAverage_integrable P.cutoff_integrable href
  have hVol := cutoffAverage_integrable P.cutoff_integrable P.volumeCost_integrable
  have hKin := cutoffAverage_integrable P.kinetic_integrable P.charge_integrable
  have hBall := ballAverage_integrable P.radius P.ballCost_integrable
  have htile := integral_mono_ae P.tile_integrable (((hRef.add hVol).add hKin).add hBall) hloc
  have hvc := P.volumeCost_integrable.const_mul (∫ z, P.cutoff z)
  have hkc := P.charge_integrable.const_mul (∫ z, P.kineticKernel z)
  have hdeficit := href.const_mul ((∫ z, P.cutoff z) - 1)
  have htotal := integral_mono_ae
    ((((P.exterior_integrable.add hvc).add hkc).add P.ballCost_integrable).add hdeficit) hcost hc
  rw [integral_add' ((hRef.add hVol).add hKin) hBall,
    integral_add' (hRef.add hVol) hKin, integral_add' hRef hVol,
    integral_cutoffAverage P.cutoff_integrable href,
    integral_cutoffAverage P.cutoff_integrable P.volumeCost_integrable,
    integral_cutoffAverage P.kinetic_integrable P.charge_integrable,
    integral_ballAverage P.radius_pos P.ballCost_integrable] at htile
  rw [integral_add' (((P.exterior_integrable.add hvc).add hkc).add P.ballCost_integrable) hdeficit,
    integral_add' ((P.exterior_integrable.add hvc).add hkc) P.ballCost_integrable,
    integral_add' (P.exterior_integrable.add hvc) hkc, integral_add' P.exterior_integrable hvc,
    integral_const_mul, integral_const_mul, integral_const_mul] at htotal
  linarith only [hglobal, htile, htotal]

/-- Summing the upper and lower local comparisons gives the absolute energy
error with the same integrable error density. -/
theorem abs_error_of_tiles {energy : ℝ} {reference cost : Position → ℝ}
    (href : Integrable reference) (hcost : Integrable cost)
    (upper : TileSide energy reference cost) (lower : TileSide (-energy) (-reference) cost) :
    |energy - (∫ x, reference x)| ≤ ∫ x, cost x := by
  have hlo := lower.bound href.neg hcost
  simp only [Pi.neg_apply, integral_neg] at hlo
  exact abs_le.mpr ⟨by linarith, upper.bound href hcost⟩

end TSGA.Localization
