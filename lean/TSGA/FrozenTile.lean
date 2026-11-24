import TSGA.ErrorDensity
import TSGA.LocalizationAssembly
import TSGA.FrozenRate
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Freezing the spin matrix and the wavevector on a comparison ball

The finite SSW rate concerns a single constant matrix and wavevector at each
center, shared by all orientations and dilations of the tile. On balls of
large oscillation the proof instead uses the rough finite and gas bounds.
-/

noncomputable section

namespace TSGA.Localization

open MeasureTheory
open scoped ComplexOrder

private def originalTileEnergy (T : AveragedTiles) (F : GasEnergies) (D : Density)
    (φ : Phase) (c : Position) (i : T.Parameter) : ℝ :=
  F.energy (fun x => (T.shape i (c - x) : ℂ) • rotate (φ.value x) (D.matrix x))

private def frozenTileEnergy (T : AveragedTiles) (F : GasEnergies) (B : SpinMatrix)
    (q c : Position) (i : T.Parameter) : ℝ :=
  F.energy (SSW.cutoffSpiral (fun x => T.shape i (c - x)) B q)

/-- The gauge and constant-matrix replacement applies to each tile before
averaging over orientations and dilations. -/
def AveragedTiles.ReplacementAt (T : AveragedTiles) (F : GasEnergies) (D : Density)
    (φ : Phase) (B : SpinMatrix) (q c : Position) (σ replacement : ℝ) : Prop := by
  letI := T.space
  exact ∃ e : T.Parameter → ℝ,
    Integrable (fun i => T.weight i * originalTileEnergy T F D φ c i) T.measure ∧
    Integrable (fun i => T.weight i * e i) T.measure ∧
    (∀ᵐ i ∂T.measure, σ * originalTileEnergy T F D φ c i ≤
      σ * frozenTileEnergy T F B q c i + e i) ∧
    (∫ i, T.weight i * e i ∂T.measure) ≤ replacement

theorem AveragedTiles.ReplacementAt.integrate {T : AveragedTiles} {F : GasEnergies}
    {D : Density} {φ : Phase} {B : SpinMatrix} {q c : Position} {σ replacement : ℝ}
    (H : T.ReplacementAt F D φ B q c σ replacement) (hfr : T.FrozenIntegrable F B q c) :
    σ * T.energy F D φ c ≤ σ * T.frozenEnergy F B q c + replacement := by
  let := T.space
  obtain ⟨e, ho, he, htile, herr⟩ := H
  have hf : Integrable (fun i => T.weight i * frozenTileEnergy T F B q c i) T.measure := hfr
  have h := integral_mono_ae (ho.const_mul σ) ((hf.const_mul σ).add he) (by
    filter_upwards [htile] with i hi
    have hm := mul_le_mul_of_nonneg_left hi (T.weight_nonneg i)
    change σ * (T.weight i * originalTileEnergy T F D φ c i) ≤
      σ * (T.weight i * frozenTileEnergy T F B q c i) + T.weight i * e i
    linarith only [hm])
  change (∫ i, σ * (T.weight i * originalTileEnergy T F D φ c i) ∂T.measure) ≤
    ∫ i, σ * (T.weight i * frozenTileEnergy T F B q c i) + T.weight i * e i ∂T.measure at h
  rw [integral_const_mul, integral_add (hf.const_mul σ) he, integral_const_mul] at h
  exact h.trans (add_le_add_right herr _)

/-- The essential pairwise Hilbert–Schmidt oscillation of the matrix power
is at most κ times the θ power of the essential supremum of the charge. -/
def SmallPowerOscillation (D : Density) (θ κ R : ℝ) (c : Position) : Prop :=
  let μ := volume.restrict (Metric.ball c R)
  ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
    Real.sqrt (∑ i, ∑ j, ‖D.power θ x i j - D.power θ y i j‖ ^ 2) ≤
      κ * (essSup D.charge μ) ^ θ

def TileProfile.directCost (P : TileProfile) (c : Position) : ℝ :=
  cutoffAverage P.cutoff P.volumeCost c + cutoffAverage P.kineticKernel P.charge c

/-- Inputs on one small-oscillation ball. The pointwise gas comparison is
made with the same frozen matrix and wavevector as the finite-volume rate.
The last field only bounds the three errors produced by these steps. -/
structure FrozenSmallTile (F : GasEnergies) (D : Density) (φ : Phase) (tiles : AveragedTiles)
    (P : TileProfile) (σ : ℝ) (raw : Position → ℝ) (c : Position) where
  matrix : SpinMatrix
  positive : matrix.PosSemidef
  wavevector : Position
  frozen_integrable : tiles.FrozenIntegrable F matrix wavevector c
  replacementError : ℝ
  finiteSizeError : ℝ
  replacement_nonneg : 0 ≤ replacementError
  finiteSize_nonneg : 0 ≤ finiteSizeError
  modulus : Position → ℝ
  replacement : tiles.ReplacementAt F D φ matrix wavevector c σ replacementError
  finite_size : FrozenSizeRate F tiles matrix wavevector c finiteSizeError σ
  reference_integrable : Integrable (fun x => (σ * localEnergy F D φ x) * P.cutoff (c - x))
  modulus_integrable : Integrable (fun x => modulus x * P.cutoff (c - x))
  compare_gas : ∀ᵐ x, P.cutoff (c - x) ≠ 0 →
    |F.ssw matrix wavevector - localEnergy F D φ x| ≤ modulus x
  error_bound : replacementError + finiteSizeError + cutoffAverage P.cutoff modulus c ≤
    P.directCost c + raw c

/-- Charge powers and the spiral kinetic density in the rough SSW estimates. -/
def roughTileDensity (D : Density) (φ : Phase) (x : Position) : ℝ :=
  D.charge x ^ (4/3 : ℝ) + D.charge x ^ (5/3 : ℝ) + D.charge x * ‖φ.grad x‖ ^ 2

/-- On a large-oscillation ball, the finite energy and the local gas
reference are each estimated using the rough density. The cost of this
density and the finite kinetic remainder is controlled by local gradients. -/
structure RoughLargeTile (F : GasEnergies) (D : Density) (φ : Phase) (tiles : AveragedTiles)
    (P : TileProfile) (raw : Position → ℝ) (c : Position) where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  kinetic : ℝ
  finite : |tiles.energy F D φ c| ≤
    coefficient * cutoffAverage P.cutoff (roughTileDensity D φ) c + kinetic
  gas : |cutoffAverage P.cutoff (localEnergy F D φ) c| ≤
    coefficient * cutoffAverage P.cutoff (roughTileDensity D φ) c
  error_bound : 2 * (coefficient * cutoffAverage P.cutoff (roughTileDensity D φ) c) + kinetic ≤
    P.directCost c + raw c

private theorem signed_le_abs {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (a : ℝ) : σ * a ≤ |a| := by
  rcases hσ with rfl | rfl
  · simpa only [one_mul] using le_abs_self a
  · simpa only [neg_one_mul] using neg_le_abs a

theorem FrozenSmallTile.estimate {F : GasEnergies} {D : Density} {φ : Phase}
    {tiles : AveragedTiles} {P : TileProfile} {σ : ℝ} {raw : Position → ℝ} {c : Position}
    (H : FrozenSmallTile F D φ tiles P σ raw c) (hσ : σ = 1 ∨ σ = -1)
    (hcut : P.cutoff = tiles.cutoffProfile) :
    σ * tiles.energy F D φ c ≤ P.localBase (fun x => σ * localEnergy F D φ x) c + raw c := by
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  have hk : Integrable (fun x => P.cutoff (c - x)) :=
    P.cutoff_integrable.comp_sub_left c
  have hp : ∀ᵐ x, (σ * F.ssw H.matrix H.wavevector) * P.cutoff (c - x) ≤
      (σ * localEnergy F D φ x) * P.cutoff (c - x) + H.modulus x * P.cutoff (c - x) := by
    filter_upwards [H.compare_gas,
      (quasiMeasurePreserving_sub_left_of_right_invariant volume c).ae P.cutoff_nonneg] with x hx hχ
    by_cases hz : P.cutoff (c - x) = 0
    · simp [hz]
    have h := (signed_le_abs hσ _).trans (hx hz)
    rw [mul_sub] at h
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) hχ
  have hi := integral_mono_ae (hk.const_mul (σ * F.ssw H.matrix H.wavevector))
    (H.reference_integrable.add H.modulus_integrable) hp
  have hr := H.finite_size.estimate H.positive
  rw [← hcut] at hr
  change (∫ x, (σ * F.ssw H.matrix H.wavevector) * P.cutoff (c - x)) ≤
    ∫ x, (σ * localEnergy F D φ x) * P.cutoff (c - x) + H.modulus x * P.cutoff (c - x) at hi
  rw [integral_const_mul, integral_sub_left_eq_self P.cutoff (volume : Measure Position) c,
    integral_add H.reference_integrable H.modulus_integrable] at hi
  change _ ≤ cutoffAverage P.cutoff (fun x => σ * localEnergy F D φ x) c +
    cutoffAverage P.cutoff H.modulus c at hi
  unfold TileProfile.localBase
  have he := H.error_bound
  unfold TileProfile.directCost at he
  linarith only [H.replacement.integrate H.frozen_integrable, hr, hi, he]

theorem RoughLargeTile.estimate {F : GasEnergies} {D : Density} {φ : Phase}
    {tiles : AveragedTiles} {P : TileProfile} {σ : ℝ} {raw : Position → ℝ} {c : Position}
    (H : RoughLargeTile F D φ tiles P raw c) (hσ : σ = 1 ∨ σ = -1) :
    σ * tiles.energy F D φ c ≤ P.localBase (fun x => σ * localEnergy F D φ x) c + raw c := by
  have hsgn : cutoffAverage P.cutoff (fun x => σ * localEnergy F D φ x) c =
      σ * cutoffAverage P.cutoff (localEnergy F D φ) c := by
    change (∫ x, (σ * localEnergy F D φ x) * P.cutoff (c - x)) =
      σ * ∫ x, localEnergy F D φ x * P.cutoff (c - x)
    simp_rw [mul_assoc, integral_const_mul]
  have hneg : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hf := (signed_le_abs hσ _).trans H.finite
  have hg := (signed_le_abs hneg _).trans H.gas
  have he := H.error_bound
  unfold TileProfile.directCost at he
  rw [TileProfile.localBase, hsgn]
  linarith only [hf, hg, he]

/-- A fixed oscillation threshold for the localized family, with a bounded
charge on almost every comparison ball. Branches depend only on the center. -/
def FrozenTileComparison (F : GasEnergies) (D : Density) (φ : Phase) (tiles : AveragedTiles)
    (P : TileProfile) (θ σ : ℝ) (raw : Position → ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/4 ∧ ∀ᵐ c,
    (∃ r : ℝ, ∀ᵐ x ∂volume.restrict (Metric.ball c P.radius), D.charge x ≤ r) ∧
    (SmallPowerOscillation D θ κ P.radius c → Nonempty (FrozenSmallTile F D φ tiles P σ raw c)) ∧
    (¬SmallPowerOscillation D θ κ P.radius c → Nonempty (RoughLargeTile F D φ tiles P raw c))

theorem FrozenTileComparison.estimate {F : GasEnergies} {D : Density} {φ : Phase}
    {tiles : AveragedTiles} {P : TileProfile} {θ σ : ℝ} {raw : Position → ℝ}
    (H : FrozenTileComparison F D φ tiles P θ σ raw) (hσ : σ = 1 ∨ σ = -1)
    (henergy : P.tileEnergy = fun c => σ * tiles.energy F D φ c)
    (hcut : P.cutoff = tiles.cutoffProfile) :
    ∀ᵐ c, P.tileEnergy c ≤ P.localBase (fun x => σ * localEnergy F D φ x) c + raw c := by
  obtain ⟨κ, _, _, h⟩ := H
  filter_upwards [h] with c hc
  rw [henergy]
  by_cases hos : SmallPowerOscillation D θ κ P.radius c
  · obtain ⟨Hsmall⟩ := hc.2.1 hos
    exact Hsmall.estimate hσ hcut
  · obtain ⟨Hlarge⟩ := hc.2.2 hos
    exact Hlarge.estimate hσ

end TSGA.Localization
