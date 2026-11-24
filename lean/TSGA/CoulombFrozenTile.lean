import TSGA.CoulombReplacement
import TSGA.CoulombTileModulus
import TSGA.PhysicalTSGA

/-! # Coulomb constructions for the two finite-tile branches

The small-oscillation case combines the two physical density additions,
local gauge estimates, the tetrahedral finite-size rate and a gas modulus.
The rough case compares an actual finite trial and the thermodynamic
power bounds against the same nonnegative cutoff.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization TSGA.SSW
open scoped ComplexOrder

/-- A pointwise modulus with its range of validity. A common spectral floor
can be required by the minority-density estimate. -/
structure PhysicalTileModulus (η : Mollifier) where
  domain : SpinMatrix → SpinMatrix → Prop
  value : (A B : SpinMatrix) → A.PosSemidef → B.PosSemidef → Position → Position → ℝ
  bound : ∀ {A B} (hA : A.PosSemidef) (hB : B.PosSemidef), domain A B → ∀ q k,
    |sswEnergy energy η A q - sswEnergy energy η B k| ≤ value A B hA hB q k

/-- The general modulus uses the θ-power variation for the density terms
and the 1/p power for the spiral kinetic term. -/
def generalTileModulus {η : Mollifier} {J K cLO p θ : ℝ}
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ a : ℝ), SpinParameters M ζ a →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ a)
    (rate : FiniteRateTiling energy η K) (removal : SpiralRemovalTrials η J) (hc : 0 ≤ cLO)
    (lo : ∀ D : Density, ∀ Γ, feasible D.matrix Γ →
      -cLO*(∫ x, D.charge x^(4/3:ℝ)) ≤ indirectAt D.matrix Γ)
    (hp : 3 ≤ p) (hθ : 0 < θ) : PhysicalTileModulus η := by
  let law := coulomb_small_tile_modulus loc states rate removal hc lo hp hθ
  let C := Classical.choose law
  refine ⟨fun _ _ => True, fun A B hA hB q k =>
    let r := max A.trace.re B.trace.re
    let d := fun a : ℝ => hilbertSchmidt (hA.1.cfc (fun t => t^a) - hB.1.cfc (fun t => t^a))/r^a
    C*((r^(4/3:ℝ)+r^(5/3:ℝ))*(d θ)^(min 1 (1/(3*θ))) + r*‖q‖^2*d (1/p)) +
      (2*K+1)*(B.trace.re^(7/6:ℝ)+B.trace.re^(4/3:ℝ)+B.trace.re*max ‖q‖ ‖k‖)*‖q-k‖, ?_⟩
  intro A B hA hB _ q k
  exact (Classical.choose_spec law).2 hA hB q k

/-- Fixed-scale and dilation-averaged finite covariance data for one sign
and a fixed comparison matrix. -/
structure CoulombFreezeScale {η : Mollifier} {K : ℝ} (rate : FiniteRateTiling energy η K)
    (tiles : AveragedTiles) (B : SpinMatrix) (q c : Position) (σ : ℝ) where
  length : ℝ
  width : ℝ
  length_pos : 0 < length
  width_pos : 0 < width
  admissible : width*K ≤ length
  averaged : Bool
  fixed_sign : averaged = false → σ = 1
  covariance : tiles.frozenEnergy (referenceEnergies energy η) B q c = (∫ z, tiles.cutoffProfile z) *
    (if averaged then scaleAverage (fun t => averagedTile energy η B q (t*length) (t*width))
      else averagedTile energy η B q length width)
  error : ℝ
  nonneg : 0 ≤ error
  scalar : (∫ z, tiles.cutoffProfile z) *
    (if σ = 1 then (K^2+K)*(if averaged then 4*upperRateError B.trace.re q length width
      else upperRateError B.trace.re q length width) else K*lowerRateError B.trace.re q length width) ≤ error

theorem CoulombFreezeScale.toRate {η : Mollifier} {K : ℝ} {rate : FiniteRateTiling energy η K}
    {tiles : AveragedTiles} {B : SpinMatrix} {q c : Position} {σ : ℝ}
    (H : CoulombFreezeScale rate tiles B q c σ) (hσ : σ=1 ∨ σ=-1) :
    FrozenSizeRate (referenceEnergies energy η) tiles B q c H.error σ := by
  let s : FrozenRateScales (referenceEnergies energy η) B q :=
    ⟨η,K,H.length,H.width,rate,H.length_pos,H.width_pos,H.admissible,rfl⟩
  rcases hσ with rfl | rfl
  · cases hb : H.averaged with
    | false => exact .upper s (by simpa [s,hb,referenceEnergies] using H.covariance) (by simpa [s,hb] using H.scalar)
    | true => exact .upperAverage s (by simpa [s,hb,referenceEnergies] using H.covariance) (by simpa [s,hb] using H.scalar)
  · have hb : H.averaged = true := by
      cases h : H.averaged with
      | false => exact False.elim ((by norm_num : (-1:ℝ)≠1) (H.fixed_sign h))
      | true => rfl
    exact .lower s (by simpa [s,hb,referenceEnergies] using H.covariance) (by simpa [s,show (-1:ℝ)≠1 by norm_num] using H.scalar)

variable {η : Mollifier} {K : ℝ} {rate : FiniteRateTiling energy η K}

/-- Microscopic and scalar data for the small-oscillation branch. The
constant frozen matrix and wavevector are common to every orientation. -/
structure SmallCoulombTrials (rate : FiniteRateTiling energy η K) (mod : PhysicalTileModulus η)
    (D : Density) (φ : Phase) (tiles : AveragedTiles) (P : TileProfile) (σ : ℝ) (raw : Position → ℝ) (c : Position) where
  Ω : Type
  [spaceΩ : MeasurableSpace Ω]
  μ : Measure Ω
  [probΩ : IsProbabilityMeasure μ]
  Y : Type
  [spaceY : MeasurableSpace Y]
  ν : Measure Y
  [probY : IsProbabilityMeasure ν]
  q : Position
  region : Set Position
  supported : ∀ i x, x ∉ region → tiles.shape i (c-x) = 0
  low : SpinMatrix
  high : SpinMatrix
  positive : (if σ=1 then low else high).PosSemidef
  ε : ℝ
  distance : ℝ
  coeff : ℝ
  loCoeff : ℝ
  ε_pos : 0 < ε
  ε_le : ε ≤ 1
  distance_nonneg : 0 ≤ distance
  coeff_nonneg : 0 ≤ coeff
  trials : ∀ i, CoulombTileReplacement μ ν D φ (comparisonTaper tiles q c region supported i) low high ε distance coeff loCoeff
  finite : CoulombFreezeScale rate tiles (if σ=1 then low else high) q c σ
  frozen_integrable : tiles.FrozenIntegrable (referenceEnergies energy η) (if σ=1 then low else high) q c
  original_integrable : letI := tiles.space
                        Integrable (fun i => tiles.weight i *
                          energy ((comparisonTaper tiles q c region supported i).phaseField D φ).matrix) tiles.measure
  trial_integrable : letI := tiles.space
                     Integrable (fun i => tiles.weight i*(trials i).error σ) tiles.measure
  replaceError : ℝ
  replace_nonneg : 0 ≤ replaceError
  trial_sum : letI := tiles.space
              (∫ i, tiles.weight i*(trials i).error σ ∂tiles.measure) ≤ replaceError
  domain : ∀ᵐ x, P.cutoff (c-x) ≠ 0 → mod.domain (if σ=1 then low else high) (D.matrix x)
  local_integrable : Integrable (fun x => (σ*localEnergy (referenceEnergies energy η) D φ x)*P.cutoff (c-x))
  modulus_integrable : Integrable (fun x =>
    mod.value _ _ positive (D.positive x) q (φ.grad x)*P.cutoff (c-x))
  scalar : replaceError + finite.error + cutoffAverage P.cutoff
    (fun x => mod.value _ _ positive (D.positive x) q (φ.grad x)) c ≤ P.directCost c + raw c

def SmallCoulombTrials.toFrozen {mod : PhysicalTileModulus η} {D : Density} {φ : Phase}
    {tiles : AveragedTiles} {P : TileProfile} {σ : ℝ} {raw : Position → ℝ} {c : Position}
    (H : SmallCoulombTrials rate mod D φ tiles P σ raw c) (hσ : σ=1 ∨ σ=-1) :
    FrozenSmallTile (referenceEnergies energy η) D φ tiles P σ raw c where
  matrix := if σ=1 then H.low else H.high
  positive := H.positive
  wavevector := H.q
  frozen_integrable := H.frozen_integrable
  replacementError := H.replaceError
  finiteSizeError := H.finite.error
  replacement_nonneg := H.replace_nonneg
  finiteSize_nonneg := H.finite.nonneg
  modulus x := mod.value _ _ H.positive (D.positive x) H.q (φ.grad x)
  replacement := by
    let := H.spaceΩ
    let := H.spaceY
    let := H.probΩ
    let := H.probY
    exact coulomb_replacementAt tiles _ rfl D φ H.q c H.region H.supported H.low H.high H.trials
      H.ε_pos H.ε_le H.distance_nonneg H.coeff_nonneg hσ H.original_integrable H.trial_integrable H.trial_sum
  finite_size := H.finite.toRate hσ
  reference_integrable := H.local_integrable
  modulus_integrable := H.modulus_integrable
  compare_gas := H.domain.mono fun x hx hcut => mod.bound H.positive (D.positive x) (hx hcut) _ _
  error_bound := H.scalar

/-- The large-oscillation branch uses one feasible state for the finite
upper bound, and the global Lieb–Oxford inequality for the finite lower
bound. The supplied estimates on these trials are scalar costs. -/
structure LargeCoulombTrials (H : FiniteEnergyInputs) (rate : FiniteRateTiling energy η K)
    (D : Density) (φ : Phase) (tiles : AveragedTiles) (P : TileProfile) (raw : Position → ℝ) (c : Position) where
  coefficient : ℝ
  covers_gas : K ≤ coefficient
  kinetic : ℝ
  localDensity : tiles.Parameter → Density
  local_eq : ∀ i x, (localDensity i).matrix x = (tiles.shape i (c-x) : ℂ) • rotate (φ.value x) (D.matrix x)
  trial : tiles.Parameter → MixedState
  feasible_trial : ∀ i, feasible (localDensity i).matrix (trial i)
  cost : tiles.Parameter → ℝ
  trial_cost : ∀ i, (trial i).kinetic+(trial i).interaction-hartree (localDensity i).charge ≤ cost i
  indirect_cost : ∀ i, H.loCoeff * chargeMoment (localDensity i) (4/3) ≤ cost i
  energy_integrable : letI := tiles.space
                      Integrable (fun i => tiles.weight i*energy (localDensity i).matrix) tiles.measure
  cost_integrable : letI := tiles.space
                    Integrable (fun i => tiles.weight i*cost i) tiles.measure
  trial_average : letI := tiles.space
                  (∫ i, tiles.weight i*cost i ∂tiles.measure) ≤
                    coefficient*cutoffAverage P.cutoff (roughTileDensity D φ) c + kinetic
  rough_integrable : Integrable (fun x => roughTileDensity D φ x * P.cutoff (c-x))
  scalar : 2*(coefficient*cutoffAverage P.cutoff (roughTileDensity D φ) c) + kinetic ≤ P.directCost c + raw c

private theorem rough_gas_density {K : ℝ} (rate : FiniteRateTiling energy η K)
    (D : Density) (φ : Phase) (x : Position) :
    |localEnergy (referenceEnergies energy η) D φ x| ≤ K*roughTileDensity D φ x := by
  let r := D.charge x
  have hr : 0 ≤ r := D.charge_nonneg x
  have ha : r*r^(1/3:ℝ) = r^(4/3:ℝ) := by
    rw [show (4/3:ℝ) = 1/3+1 by norm_num, Real.rpow_add_one' hr (by norm_num), mul_comm]
  have hb : r*r^(2/3:ℝ) = r^(5/3:ℝ) := by
    rw [show (5/3:ℝ) = 2/3+1 by norm_num, Real.rpow_add_one' hr (by norm_num), mul_comm]
  obtain ⟨hlo,hhi⟩ := rate.ssw_power_bounds (D.positive x) (φ.grad x)
  change -K*(r*r^(1/3:ℝ)) ≤ _ at hlo
  change _ ≤ K*(r*(r^(1/3:ℝ)+r^(2/3:ℝ)+‖φ.grad x‖^2)) at hhi
  change |sswEnergy energy η (D.matrix x) (φ.grad x)| ≤ K*(r^(4/3:ℝ)+r^(5/3:ℝ)+r*‖φ.grad x‖^2)
  rw [ha] at hlo
  rw [mul_add r, mul_add r, ha, hb] at hhi
  refine abs_le.mpr ⟨?_,hhi⟩
  have hK := zero_le_one.trans rate.one_le
  have h53 := mul_nonneg hK (Real.rpow_nonneg hr (5/3))
  have hq := mul_nonneg hK (mul_nonneg hr (sq_nonneg ‖φ.grad x‖))
  linarith only [hlo,h53,hq]

def LargeCoulombTrials.toRough {H : FiniteEnergyInputs} {D : Density} {φ : Phase}
    {tiles : AveragedTiles} {P : TileProfile} {raw : Position → ℝ} {c : Position}
    (G : LargeCoulombTrials H rate D φ tiles P raw c) : RoughLargeTile (referenceEnergies energy η) D φ tiles P raw c := by
  letI := tiles.space
  letI : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  have hcoef : 0 ≤ G.coefficient := (zero_le_one.trans rate.one_le).trans G.covers_gas
  refine ⟨G.coefficient,hcoef,G.kinetic, ?_, ?_, G.scalar⟩
  · have stateBound (i : tiles.Parameter) : |energy (G.localDensity i).matrix| ≤ G.cost i := by
      let A := G.localDensity i
      have rep : feasible A.matrix (G.trial i) := G.feasible_trial i
      have low : hartree A.charge-H.loCoeff*chargeMoment A (4/3) ≤ levyLieb A.matrix :=
        le_levyLieb ⟨_,rep⟩ fun Γ hg => (H.liebOxford A Γ hg).trans (le_add_of_nonneg_left Γ.kinetic_nonneg)
      change |levyLieb A.matrix-hartree A.charge| ≤ _
      exact abs_le.mpr ⟨by linarith only [low,G.indirect_cost i], by linarith only [levyLieb_le rep,G.trial_cost i]⟩
    have hE : tiles.energy (referenceEnergies energy η) D φ c =
        ∫ i, tiles.weight i*energy (G.localDensity i).matrix ∂tiles.measure := by
      apply integral_congr_ae
      apply ae_of_all
      intro i
      exact congrArg (fun field : Position → SpinMatrix => tiles.weight i * energy field) (funext (G.local_eq i)).symm
    rw [hE, ← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply (integral_mono_ae G.energy_integrable.norm G.cost_integrable _).trans G.trial_average
    apply ae_of_all
    intro i
    simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (tiles.weight_nonneg i)]
    exact mul_le_mul_of_nonneg_left (stateBound i) (tiles.weight_nonneg i)
  · change |∫ x, localEnergy _ D φ x * P.cutoff (c-x)| ≤ G.coefficient*(∫ x, roughTileDensity D φ x*P.cutoff (c-x))
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (G.rough_integrable.const_mul _)
    filter_upwards [(quasiMeasurePreserving_sub_left_of_right_invariant volume c).ae P.cutoff_nonneg] with x hx
    have hr : 0 ≤ roughTileDensity D φ x := add_nonneg
      (add_nonneg (Real.rpow_nonneg (D.charge_nonneg x) _) (Real.rpow_nonneg (D.charge_nonneg x) _))
      (mul_nonneg (D.charge_nonneg x) (sq_nonneg _))
    have bound := (rough_gas_density rate D φ x).trans (mul_le_mul_of_nonneg_right G.covers_gas hr)
    simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hx]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right bound hx

/-- A family of primitive Coulomb trials and scale identities for the
two branches, with one oscillation threshold for the tile family. -/
def CoulombFrozenComparison (H : FiniteEnergyInputs) (rate : FiniteRateTiling energy η K) (M : PhysicalTileModulus η)
    (D : Density) (φ : Phase) (tiles : AveragedTiles) (P : TileProfile) (θ σ : ℝ) (raw : Position → ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/4 ∧ ∀ᵐ c,
    (∃ r : ℝ, ∀ᵐ x ∂volume.restrict (Metric.ball c P.radius), D.charge x ≤ r) ∧
    (SmallPowerOscillation D θ κ P.radius c → Nonempty (SmallCoulombTrials rate M D φ tiles P σ raw c)) ∧
    (¬SmallPowerOscillation D θ κ P.radius c → Nonempty (LargeCoulombTrials H rate D φ tiles P raw c))

theorem CoulombFrozenComparison.toFrozen {H : FiniteEnergyInputs} {M : PhysicalTileModulus η} {D : Density}
    {φ : Phase} {tiles : AveragedTiles} {P : TileProfile} {θ σ : ℝ} {raw : Position → ℝ}
    (h : CoulombFrozenComparison H rate M D φ tiles P θ σ raw) (hσ : σ=1 ∨ σ=-1) :
    FrozenTileComparison (referenceEnergies energy η) D φ tiles P θ σ raw := by
  obtain ⟨κ,hpos,hle,hc⟩ := h
  refine ⟨κ,hpos,hle,hc.mono fun c h => ⟨h.1, ?_, ?_⟩⟩
  · intro hs
    exact (h.2.1 hs).map fun t => t.toFrozen hσ
  · intro hs
    exact (h.2.2 hs).map fun t => t.toRough

end TSGA.ManyBody
