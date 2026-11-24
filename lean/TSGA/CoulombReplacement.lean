import TSGA.IslandLocalization
import TSGA.GaugeEnergy
import TSGA.FrozenTile
import TSGA.ComparisonMatrices
import TSGA.ReplacementInterpolation

/-! # The two ordered Coulomb comparisons of Proposition 4.16

The lower constant matrix is compared to the aligned density by adding
electrons. A second addition compares the aligned density to the upper
constant matrix. The local unitary maps the aligned spiral to the physical
spiral in both directions.
-/

noncomputable section

namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization
open scoped ComplexOrder MatrixOrder InnerProductSpace

structure SpiralTaper (K : Set Position) where
  shape : Position → ℝ
  range : ∀ x, shape x ∈ Set.Icc 0 1
  outside : ∀ x ∉ K, shape x = 0
  wavevector : Position

variable {K : Set Position}

def SpiralTaper.field (t : SpiralTaper K) (A : Density) : Density where
  matrix x := SSW.cutoffSpiral t.shape (A.matrix x) t.wavevector x
  positive x := (rotate_posSemidef _ (A.positive x)).smul (Complex.zero_le_real.mpr (t.range x).1)

def constantSpinDensity (B : SpinMatrix) (hB : B.PosSemidef) : Density := ⟨fun _ => B, fun _ => hB⟩

def SpiralTaper.residual (t : SpiralTaper K) (A B : Density) (order : ∀ x ∈ K, A.matrix x ≤ B.matrix x) :
    Density where
  matrix x := SSW.cutoffSpiral t.shape (B.matrix x-A.matrix x) t.wavevector x
  positive x := by
    by_cases hx : x ∈ K
    · exact (rotate_posSemidef _ (Matrix.le_iff.mp (order x hx))).smul (Complex.zero_le_real.mpr (t.range x).1)
    · simp [SSW.cutoffSpiral, t.outside x hx, Matrix.PosSemidef.zero]

theorem SpiralTaper.sum_residual (t : SpiralTaper K) (A B : Density) (ho : ∀ x ∈ K, A.matrix x ≤ B.matrix x) :
    (t.field A).matrix + (t.residual A B ho).matrix = (t.field B).matrix := by
  funext x
  change _ • rotate _ (A.matrix x) + (t.shape x : ℂ) • rotate _ (B.matrix x - A.matrix x) = _
  simp only [rotate, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  abel

/-- The residual charge cap follows from the unrotated matrix oscillation
on the comparison ball. Tapering preserves it and gives zero off the ball. -/
theorem SpiralTaper.residual_cap (t : SpiralTaper K) (A B : Density) (ho : ∀ x ∈ K, A.matrix x ≤ B.matrix x)
    {η : ℝ} (hη : 0 ≤ η) (dist : ∀ x ∈ K, hilbertSchmidt (B.matrix x-A.matrix x) ≤ η) :
    ∀ x, (t.residual A B ho).charge x ≤ 2*η := by
  intro x
  change ((t.shape x : ℂ) • rotate _ (B.matrix x-A.matrix x)).trace.re ≤ _
  rw [Matrix.trace_smul, trace_rotate, smul_eq_mul, Complex.re_ofReal_mul]
  by_cases hx : x ∈ K
  · have h := (le_abs_self _).trans ((SSW.abs_trace_re_le_hilbertSchmidt _).trans
      (mul_le_mul_of_nonneg_left (dist x hx) (by norm_num : 0 ≤ (2:ℝ))))
    exact (mul_le_mul_of_nonneg_left h (t.range x).1).trans
      (mul_le_of_le_one_left (by linarith : 0 ≤ 2*η) (t.range x).2)
  · rw [t.outside x hx, zero_mul]
    linarith

/-- The aligned matrix field in the common reference eigenbasis. -/
def referenceDensity (M : Density) (c : Position) : Density where
  matrix := SpectralExtrema.referenceFrame M c
  positive x := inSpinFrame_pos _ (fun i => (M.positive x).eigenvalues_nonneg i)

/-- The spectral-extrema construction provides both ordered pairs and a
Hilbert–Schmidt cap from componentwise eigenvalue oscillation. -/
theorem spectral_ordered_pairs {M : Density} (E : SpectralExtrema M K) (c : Position) {η : ℝ}
    (hη : 0 ≤ η) (osc : ∀ x ∈ K, ∀ y ∈ K, ∀ i, |(M.positive x).1.eigenvalues i - (M.positive y).1.eigenvalues i| ≤ η) :
    ∀ x ∈ K, E.lowerMatrix c ≤ (referenceDensity M c).matrix x ∧
      (referenceDensity M c).matrix x ≤ E.upperMatrix c ∧
      hilbertSchmidt ((referenceDensity M c).matrix x-E.lowerMatrix c) ≤ 2*η ∧
      hilbertSchmidt (E.upperMatrix c-(referenceDensity M c).matrix x) ≤ 2*η := by
  intro x hx
  let U := (M.positive c).1.eigenvectorUnitary
  have bound (a b : Fin 2 → ℝ) (hab : ∀ i, |a i-b i| ≤ η) :
      hilbertSchmidt (inSpinFrame U a-inSpinFrame U b) ≤ 2*η := by
    rw [inSpinFrame_sub]
    have h := inSpinFrame_hs U (a-b)
    simp only [Pi.sub_apply] at h
    have hs (i : Fin 2) : (a i-b i)^2 ≤ η^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hab i) 2
    nlinarith only [h,hs 0,hs 1,sq_nonneg η,hη]
  exact ⟨(E.ordered c hx).1, (E.ordered c hx).2,
    bound _ _ (fun i => osc x hx _ (E.min_mem i) i),
    bound _ _ (fun i => osc _ (E.max_mem i) x hx i)⟩

/-- In the common eigenbasis the effective residual cap is controlled
by the oscillation of the θ power in Proposition 4.16. -/
theorem spectral_ordered_of_power_oscillation {M : Density} (E : SpectralExtrema M K) (c : Position)
    {r θ ω : ℝ} (hr : 0 ≤ r) (hθ : 0 < θ) (hθ' : θ ≤ 1) (hω : 0 ≤ ω)
    (peak : ∀ x ∈ K, M.charge x ≤ r)
    (osc : ∀ x ∈ K, ∀ y ∈ K, hilbertSchmidt (M.power θ x - M.power θ y) ≤ ω) :
    let η := (1/θ*r^(1-θ))*ω
    ∀ x ∈ K, E.lowerMatrix c ≤ (referenceDensity M c).matrix x ∧
      (referenceDensity M c).matrix x ≤ E.upperMatrix c ∧
      hilbertSchmidt ((referenceDensity M c).matrix x-E.lowerMatrix c) ≤ 2*η ∧
      hilbertSchmidt (E.upperMatrix c-(referenceDensity M c).matrix x) ≤ 2*η := by
  have hc : 0 ≤ 1/θ*r^(1-θ) := mul_nonneg (one_div_nonneg.mpr hθ.le) (Real.rpow_nonneg hr _)
  apply spectral_ordered_pairs E c (mul_nonneg hc hω)
  intro x hx y hy i
  have h := eigenvalue_power_distance (M.positive x) (M.positive y) (u := 1) (by norm_num) i
  calc
    _ = |(M.positive x).1.eigenvalues i^(1:ℝ)-(M.positive y).1.eigenvalues i^(1:ℝ)| := by simp
    _ ≤ _ := h.trans ((matrix_power_oscillation (M.positive x) (M.positive y) hθ hθ' hr (peak x hx) (peak y hy)).trans
      (mul_le_mul_of_nonneg_left (osc x hx y hy) hc))

variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure Y} [IsProbabilityMeasure ν]

/-- The covariance estimate for one ordered trial, either via the auxiliary
two-point mark representation or directly from the common Poisson process. -/
inductive OrderedFluctuation {B D : Density} (u : IslandTrial μ (B.matrix+D.matrix))
    (S : MatrixGradient) (ν : Measure Y) [IsProbabilityMeasure ν] (ε r C : ℝ) : Prop
  | localization : Nonempty (IslandFluctuations u S ν ε r C) → OrderedFluctuation u S ν ε r C
  | estimate : (u.fluctuation ≤ 12*C*ε*islandBackground B S + 6*C*(r^2/ε)*(∫ x, D.charge x^2)) →
      OrderedFluctuation u S ν ε r C

/-- Representability and localization operators for a single ordered
pair after applying the actual taper and constant wavevector. -/
structure OrderedSpiralAddition (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (t : SpiralTaper K) (A B : Density) (ε η C : ℝ) where
  order : ∀ x ∈ K, A.matrix x ≤ B.matrix x
  distance : ∀ x ∈ K, hilbertSchmidt (B.matrix x-A.matrix x) ≤ η
  gradients : IslandGradients (t.field A) (t.residual A B order) ε
  mass : Integrable (t.residual A B order).charge
  trials : ∀ r : ℝ, 1 ≤ r → ε*r^2 ≤ 1 →
    ∃ u : IslandTrial μ ((t.field A).matrix+(t.residual A B order).matrix),
      Nonempty (ExteriorLocalization u gradients.background ν ε r C) ∧
      Nonempty (IslandInterior u gradients r C) ∧ OrderedFluctuation u gradients.background ν ε r C

variable {t : SpiralTaper K} {A B : Density} {ε η C : ℝ}

def OrderedSpiralAddition.cost (H : OrderedSpiralAddition μ ν t A B ε η C) : ℝ :=
  (12*C+2*C^2)*(3*ε*islandBackground (t.field A) H.gradients.background + sqrtKinetic H.gradients.mixed +
    3*(ε + Real.sqrt (2*η/ε) + 2*η/ε)*(∫ x, (t.residual A B H.order).charge x))

theorem OrderedSpiralAddition.energy_bound (H : OrderedSpiralAddition μ ν t A B ε η C)
    (he : 0 < ε) (he' : ε ≤ 1) (hη : 0 ≤ η) (hC : 0 ≤ C) :
    energy (t.field B).matrix ≤ energy (t.field A).matrix + H.cost := by
  rw [← t.sum_residual A B H.order]
  apply subadditivity_of_bounded_charge he he' (by positivity) (by linarith : 0 ≤ 2*η)
    (ae_of_all _ (t.residual_cap A B H.order hη H.distance)) H.mass
  intro r hr hm
  obtain ⟨u,⟨out⟩,⟨ins⟩,fl⟩ := H.trials r hr hm
  cases fl with
  | localization h =>
    exact subadditivity_from_localization H.gradients u out ins h.some he he' hC hr hm
  | estimate h =>
    exact subadditivity_from_fluctuation_bound H.gradients u out ins h he he' hC hm

/-- The residual charge integrated over one cutoff is bounded by its cap
times the cutoff volume. -/
theorem OrderedSpiralAddition.residual_mass (H : OrderedSpiralAddition μ ν t A B ε η C)
    (ht : Integrable t.shape) :
    (∫ x, (t.residual A B H.order).charge x) ≤ 2*η*(∫ x, t.shape x) := by
  rw [← integral_const_mul]
  apply integral_mono_ae H.mass (ht.const_mul _)
  apply ae_of_all
  intro x
  change ((t.shape x : ℂ) • rotate _ (B.matrix x-A.matrix x)).trace.re ≤ _
  rw [Matrix.trace_smul, trace_rotate, smul_eq_mul, Complex.re_ofReal_mul]
  by_cases hx : x ∈ K
  · have hh := (le_abs_self _).trans ((SSW.abs_trace_re_le_hilbertSchmidt _).trans
      (mul_le_mul_of_nonneg_left (H.distance x hx) (by norm_num : 0 ≤ (2:ℝ))))
    simpa only [mul_comm (2*η)] using mul_le_mul_of_nonneg_left hh (t.range x).1
  · simp [t.outside x hx]

/-- Apply the two Young–Morrey estimates to the actual integrated charge of
the ordered residual. The square-root and linear charge-ratio terms have
powers 3/2 and 2, respectively. -/
theorem OrderedSpiralAddition.residual_interpolation (H : OrderedSpiralAddition μ ν t A B ε η C)
    {p θ r ω L G : ℝ} (hp : 3 < p) (hθp : 2 ≤ θ*p) (he : 0 < ε) (hη : 0 ≤ η)
    (hr : 0 < r) (hL : 0 ≤ L) (hω : 0 ≤ ω) (hsmall : ω ≤ r^θ)
    (ht : Integrable t.shape) (hcap : 2*η ≤ L*(r^(1-θ)*ω))
    (hmorrey : (∫ x, t.shape x)*ω^p ≤ G) :
    let V := ∫ x, t.shape x
    let cap := 2*η
    (Real.sqrt (cap/ε)+cap/ε)*(∫ x, (t.residual A B H.order).charge x) ≤
      (L^(3/2:ℝ)+L^2)*(ε*V*(r+r^2)+ε^(1-max p (3*θ*p-3))*G) := by
  let V := ∫ x, t.shape x
  let cap := 2*η
  have hv : 0 ≤ V := integral_nonneg fun x => (t.range x).1
  have hc : 0 ≤ cap := by dsimp [cap]; linarith
  have h₁ := residual_charge_interpolation (m := (3/2:ℝ)) hp hθp (by constructor <;> norm_num)
    he hr hv hL hc hω hsmall hcap hmorrey
  have h₂ := residual_charge_interpolation (m := (2:ℝ)) hp hθp (by constructor <;> norm_num)
    he hr hv hL hc hω hsmall hcap hmorrey
  have hs : Real.sqrt (cap/ε)*cap = ε^(1-(3/2:ℝ))*cap^(3/2:ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow hc he.le,
      show (3/2:ℝ)=(1/2:ℝ)+1 by norm_num, Real.rpow_add_one' hc (by norm_num),
      show (1-((1/2:ℝ)+1))= -(1/2:ℝ) by norm_num, Real.rpow_neg he.le]
    ring
  have hq : cap/ε*cap = ε^(1-(2:ℝ))*cap^(2:ℝ) := by norm_num [Real.rpow_neg_one]; ring
  have hm := mul_le_mul_of_nonneg_left (H.residual_mass ht)
    (add_nonneg (Real.sqrt_nonneg (cap/ε)) (div_nonneg hc he.le))
  change (Real.sqrt (cap/ε)+cap/ε)*(∫ x, (t.residual A B H.order).charge x) ≤ _ 
  change _ ≤ (Real.sqrt (cap/ε)+cap/ε)*(cap*V) at hm
  apply hm.trans
  rw [← mul_assoc, add_mul, hs, hq]
  norm_num only [Real.rpow_two] at h₂ ⊢
  change _ ≤ (L^(3/2:ℝ)+L^2)*(ε*V*(r+r^2)+ε^(1-max p (3*θ*p-3))*G)
  dsimp only at h₁ h₂
  linarith only [h₁,h₂]

/-- The bounded-charge energy bound with the residual terms interpolated
at the exponent of Proposition 4.16. Both square-root gradient integrals
still involve the physical tapered matrices. -/
theorem OrderedSpiralAddition.interpolated_bound (H : OrderedSpiralAddition μ ν t A B ε η C)
    {p θ r ω L G : ℝ} (hp : 3 < p) (hθp : 2 ≤ θ*p) (he : 0 < ε) (he' : ε ≤ 1)
    (hC : 0 ≤ C) (hη : 0 ≤ η) (hr : 0 < r) (hL : 0 ≤ L) (hω : 0 ≤ ω) (hsmall : ω ≤ r^θ)
    (ht : Integrable t.shape) (hcap : 2*η ≤ L*(r^(1-θ)*ω))
    (hmorrey : (∫ x, t.shape x)*ω^p ≤ G) :
    let V := ∫ x, t.shape x
    energy (t.field B).matrix ≤ energy (t.field A).matrix +
      (12*C+2*C^2)*(3*ε*islandBackground (t.field A) H.gradients.background + sqrtKinetic H.gradients.mixed +
        3*(ε*(∫ x, (t.residual A B H.order).charge x) +
        (L^(3/2:ℝ)+L^2)*(ε*V*(r+r^2)+ε^(1-max p (3*θ*p-3))*G))) := by
  have h := H.residual_interpolation hp hθp he hη hr hL hω hsmall ht hcap hmorrey
  dsimp only at h ⊢
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 3*(12*C+2*C^2) by positivity)
  have hb := H.energy_bound he he' hη hC
  unfold OrderedSpiralAddition.cost at hb
  linarith only [hb,h']

private def spiralUnitary (q x : Position) : unitary SpinMatrix :=
  ⟨spinRotation (⟪q,x⟫_ℝ), (Matrix.mem_specialUnitaryGroup_iff.mp (spinRotation_mem_specialUnitaryGroup _)).1⟩

/-- The aligning unitary in the laboratory frame is U_q V U_q*. -/
def SpiralTaper.alignment (t : SpiralTaper K) (V : Position → unitary SpinMatrix) (x : Position) : unitary SpinMatrix :=
  spiralUnitary t.wavevector x * V x * star (spiralUnitary t.wavevector x)

theorem SpiralTaper.alignment_target (t : SpiralTaper K) (V : Position → unitary SpinMatrix) (A M : Density)
    (maps : ∀ x ∈ K, M.matrix x = (V x : SpinMatrix)*A.matrix x*star (V x : SpinMatrix)) :
    (conjugatedDensity (t.field A) (t.alignment V)).matrix = (t.field M).matrix := by
  funext x
  by_cases hx : x ∈ K
  · let U := spiralUnitary t.wavevector x
    change ((U * V x * star U : unitary SpinMatrix) : SpinMatrix) *
      ((t.shape x : ℂ) • ((U : SpinMatrix)*A.matrix x*star (U : SpinMatrix))) *
      star ((U * V x * star U : unitary SpinMatrix) : SpinMatrix) =
      (t.shape x : ℂ) • ((U : SpinMatrix)*M.matrix x*star (U : SpinMatrix))
    rw [maps x hx, Matrix.mul_smul, Matrix.smul_mul]
    have cancel (X : SpinMatrix) : star (U : SpinMatrix)*((U : SpinMatrix)*X) = X := by
      rw [← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
    simp only [Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star, Matrix.mul_assoc, cancel]
  · simp [conjugatedDensity, SpiralTaper.field, SSW.cutoffSpiral, t.outside x hx]

/-- Formal spin rotation in both directions for the tapered densities. -/
structure GaugeComparison (A B : Density) (L : ℝ) where
  U : Position → unitary SpinMatrix
  target : (conjugatedDensity A U).matrix = B.matrix
  forwardCost : ℝ
  inverseCost : ℝ
  forward : RotationLaw A U forwardCost
  inverse : RotationLaw B (fun x => star (U x)) inverseCost
  input_rep : ∃ Γ, feasible A.matrix Γ
  output_rep : ∃ Γ, feasible B.matrix Γ
  lo_A : ∀ Γ, feasible A.matrix Γ → hartree A.charge-L*chargeMoment A (4/3) ≤ Γ.interaction
  lo_B : ∀ Γ, feasible B.matrix Γ → hartree B.charge-L*chargeMoment B (4/3) ≤ Γ.interaction

def gaugeError (A : Density) (ε L W : ℝ) := ε*(energy A.matrix+L*chargeMoment A (4/3))+(1+1/ε)*W

theorem GaugeComparison.signed {L : ℝ} (H : GaugeComparison A B L) (he : 0 < ε) :
    energy B.matrix ≤ energy A.matrix + gaugeError A ε L H.forwardCost ∧
    energy A.matrix ≤ energy B.matrix + gaugeError B ε L H.inverseCost := by
  have inv : (conjugatedDensity B (fun x => star (H.U x))).matrix = A.matrix := by
    funext x
    change (star (H.U x) : unitary SpinMatrix).val * B.matrix x * star (star (H.U x) : unitary SpinMatrix).val = _
    rw [← H.target]
    change star (H.U x : SpinMatrix) * ((H.U x : SpinMatrix)*A.matrix x*star (H.U x : SpinMatrix)) *
      star (star (H.U x : SpinMatrix)) = _
    simp only [star_star, Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
  have plus := local_rotation_bound he H.input_rep H.forward H.lo_A
  have minus := local_rotation_bound he H.output_rep H.inverse H.lo_B
  rw [H.target] at plus
  rw [inv] at minus
  unfold gaugeError
  constructor <;> linarith

/-- The two inequalities of Proposition 4.16 on one actual tapered spiral,
with separate island and local gauge contributions. -/
theorem coulomb_replacement {M aligned : Density} {low high : SpinMatrix}
    (hLow : low.PosSemidef) (hHigh : high.PosSemidef)
    (lower : OrderedSpiralAddition μ ν t (constantSpinDensity low hLow) aligned ε η C)
    (upper : OrderedSpiralAddition μ ν t aligned (constantSpinDensity high hHigh) ε η C)
    {L : ℝ} (gauge : GaugeComparison (t.field aligned) (t.field M) L)
    (he : 0 < ε) (he' : ε ≤ 1) (hη : 0 ≤ η) (hC : 0 ≤ C) :
    energy (t.field M).matrix ≤ energy (SSW.cutoffSpiral t.shape low t.wavevector) +
      (lower.cost + gaugeError (t.field aligned) ε L gauge.forwardCost) ∧
    energy (SSW.cutoffSpiral t.shape high t.wavevector) ≤ energy (t.field M).matrix +
      (upper.cost + gaugeError (t.field M) ε L gauge.inverseCost) := by
  obtain ⟨forward,inverse⟩ := gauge.signed he
  have hlo := lower.energy_bound he he' hη hC
  have hhi := upper.energy_bound he he' hη hC
  change energy (t.field aligned).matrix ≤ energy (SSW.cutoffSpiral t.shape low t.wavevector) + lower.cost at hlo
  change energy (SSW.cutoffSpiral t.shape high t.wavevector) ≤ energy (t.field aligned).matrix + upper.cost at hhi
  constructor <;> linarith

def SpiralTaper.phaseField (t : SpiralTaper K) (M : Density) (φ : Phase) : Density where
  matrix x := (t.shape x : ℂ) • rotate (φ.value x) (M.matrix x)
  positive x := (rotate_posSemidef _ (M.positive x)).smul (Complex.zero_le_real.mpr (t.range x).1)

/-- Both density additions and both physical gauge changes on a single tile.
The phase gauge is the transition from the local constant wavevector to φ. -/
structure CoulombTileReplacement (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (M : Density) (φ : Phase) (t : SpiralTaper K) (low high : SpinMatrix) (ε η C L : ℝ) where
  aligned : Density
  low_pos : low.PosSemidef
  high_pos : high.PosSemidef
  lower : OrderedSpiralAddition μ ν t (constantSpinDensity low low_pos) aligned ε η C
  upper : OrderedSpiralAddition μ ν t aligned (constantSpinDensity high high_pos) ε η C
  gauge : GaugeComparison (t.field aligned) (t.field M) L
  phaseGauge : GaugeComparison (t.field M) (t.phaseField M φ) L

def CoulombTileReplacement.error {M : Density} {φ : Phase} {low high : SpinMatrix} {L : ℝ}
    (D : CoulombTileReplacement μ ν M φ t low high ε η C L) (σ : ℝ) : ℝ :=
  if σ = 1 then D.lower.cost + gaugeError (t.field D.aligned) ε L D.gauge.forwardCost +
    gaugeError (t.field M) ε L D.phaseGauge.forwardCost
  else D.upper.cost + gaugeError (t.field M) ε L D.gauge.inverseCost +
    gaugeError (t.phaseField M φ) ε L D.phaseGauge.inverseCost

theorem CoulombTileReplacement.signed {M : Density} {φ : Phase} {low high : SpinMatrix} {L σ : ℝ}
    (D : CoulombTileReplacement μ ν M φ t low high ε η C L)
    (he : 0 < ε) (he' : ε ≤ 1) (hη : 0 ≤ η) (hC : 0 ≤ C) (hσ : σ = 1 ∨ σ = -1) :
    σ*energy (t.phaseField M φ).matrix ≤
      σ*energy (SSW.cutoffSpiral t.shape (if σ = 1 then low else high) t.wavevector) + D.error σ := by
  obtain ⟨hplus,hminus⟩ := coulomb_replacement D.low_pos D.high_pos D.lower D.upper D.gauge he he' hη hC
  obtain ⟨hφplus,hφminus⟩ := D.phaseGauge.signed he
  rcases hσ with rfl | rfl
  · simp only [CoulombTileReplacement.error, ite_true, one_mul]
    linarith only [hplus,hφplus]
  · norm_num [CoulombTileReplacement.error]
    linarith only [hminus,hφminus]

def comparisonTaper (T : AveragedTiles) (q c : Position) (K : Set Position)
    (outside : ∀ i x, x ∉ K → T.shape i (c-x) = 0) (i : T.Parameter) : SpiralTaper K where
  shape x := T.shape i (c-x)
  range x := T.shape_mem i (c-x)
  outside := outside i
  wavevector := q

/-- Supply the replacement field of the finite-tile TSGA argument using
pointwise Coulomb constructions on the indexed tapers. The remaining
averaged bound is on explicitly calculated island and gauge costs. -/
theorem coulomb_replacementAt (T : AveragedTiles) (F : GasEnergies) (functional : F.energy = energy)
    (M : Density) (φ : Phase) (q c : Position) (K : Set Position)
    (outside : ∀ i x, x ∉ K → T.shape i (c-x) = 0) (low high : SpinMatrix) {L σ R : ℝ}
    (D : ∀ i, CoulombTileReplacement μ ν M φ (comparisonTaper T q c K outside i) low high ε η C L)
    (he : 0 < ε) (he' : ε ≤ 1) (hη : 0 ≤ η) (hC : 0 ≤ C) (hσ : σ = 1 ∨ σ = -1)
    (hOrig : letI := T.space
             Integrable (fun i => T.weight i * energy ((comparisonTaper T q c K outside i).phaseField M φ).matrix) T.measure)
    (hErr : letI := T.space
            Integrable (fun i => T.weight i * (D i).error σ) T.measure)
    (hR : letI := T.space
          (∫ i, T.weight i * (D i).error σ ∂T.measure) ≤ R) :
    T.ReplacementAt F M φ (if σ = 1 then low else high) q c σ R := by
  let _ := T.space
  refine ⟨fun i => (D i).error σ, ?_, hErr, ?_, hR⟩
  · change Integrable (fun i => T.weight i * F.energy ((comparisonTaper T q c K outside i).phaseField M φ).matrix) T.measure
    rw [functional]
    exact hOrig
  · apply ae_of_all
    intro i
    change σ*F.energy ((comparisonTaper T q c K outside i).phaseField M φ).matrix ≤
      σ*F.energy (SSW.cutoffSpiral _ _ _) + _
    rw [functional]
    exact (D i).signed he he' hη hC hσ

end TSGA.ManyBody
