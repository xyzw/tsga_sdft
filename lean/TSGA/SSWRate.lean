import TSGA.SSWLocalization
import TSGA.DilationEndpoint

/-! # Finite-volume convergence rates for spiral tetrahedra

The upper rate comes from loss of interior tiles in the finite lower tiling
bound. The lower rate comes from the dilation-averaged upper tiling bound.
The outer smoothing width is fixed at one in both comparisons.
-/

noncomputable section

namespace TSGA.SSW

open Filter MeasureTheory
open scoped Topology ComplexOrder

/-- The density and wavevector powers in the skeleton and boundary fractions,
after factoring out one power of the charge. -/
def rateGrowth (ρ : ℝ) (q : Position) : ℝ :=
  ρ ^ (1/3 : ℝ) + ρ ^ (2/3 : ℝ) + ‖q‖ ^ 2

def lowerRateError (ρ : ℝ) (q : Position) (ℓ δ : ℝ) : ℝ :=
  ρ / ℓ * (δ⁻¹ + δ ^ 3 * ρ + δ * rateGrowth ρ q)

def upperRateError (ρ : ℝ) (q : Position) (ℓ δ : ℝ) : ℝ :=
  ρ / ℓ + lowerRateError ρ q ℓ δ

/-- The finite interior lower comparison at a fixed inner length and smoothing width. -/
def TileInteriorComparison (E : EnergyFunctional) (η : Mollifier) (K : ℝ) : Prop :=
  ∀ M : SpinMatrix, M.PosSemidef → ∀ (q : Position) (ℓ δ : ℝ),
    0 < ℓ → 0 < δ → δ * K ≤ ℓ →
    let ρ := M.trace.re
    ∀ᶠ L : ℝ in atTop,
      InteriorLower (tileEnergy E η M ℓ δ) ‖q‖ (K * (δ / ℓ + (ℓ + δ + 1) / L))
        (K * (ρ * ρ ^ (1/3 : ℝ)))
        (K * (ρ * ρ ^ (1/3 : ℝ)) * ((ℓ + δ + 1) / L) +
          K * (ρ / ℓ) * (1 + δ⁻¹ + δ ^ 3 * ρ)) (averagedTile E η M q L 1)

/-- Integrability on the finite interval of dilation parameters. -/
def TileDilationIntegrable (E : EnergyFunctional) (η : Mollifier) (K : ℝ) : Prop :=
  ∀ M : SpinMatrix, M.PosSemidef → ∀ (q : Position) (ℓ δ : ℝ),
    0 < ℓ → 0 < δ → δ * K ≤ ℓ →
    IntegrableOn (fun t => averagedTile E η M q (t * ℓ) (t * δ) * scaleWeight t) scaleInterval

/-- The upper comparison averaged over dilations of the inner tetrahedron. -/
def TileDilationComparison (E : EnergyFunctional) (η : Mollifier) (K : ℝ) : Prop :=
  ∀ M : SpinMatrix, M.PosSemidef → ∀ (q : Position) (ℓ δ : ℝ),
    0 < ℓ → 0 < δ → δ * K ≤ ℓ →
    let ρ := M.trace.re
    ∀ᶠ L : ℝ in atTop, ∀ α : ℝ, 0 < α → α < 1/2 → averagedTile E η M q L 1 ≤
      scaleAverageAt α (fun t => averagedTile E η M q (t * (ℓ - δ)) (t * δ)) +
      K * (ρ * rateGrowth ρ q * (δ / ℓ + (ℓ + δ + 1) / L) +
        ρ * (1 / (ℓ * δ) + 1 / L)) + (K * (δ ^ 3 * ρ ^ 2 / ℓ)) * Real.log α⁻¹

/-- Quantitative finite tiling comparisons. All three fields use the same
constant independently of charge, wavevector, smoothing and tile lengths.
The outer energy in each field is still a finite tetrahedron energy. -/
structure FiniteRateTiling (E : EnergyFunctional) (η : Mollifier) (K : ℝ) : Prop where
  one_le : 1 ≤ K
  rough : ∀ M : SpinMatrix, M.PosSemidef → ∀ (q : Position) (ℓ δ : ℝ), 0 < ℓ → 0 < δ →
    let ρ := M.trace.re
    (-K * (ρ * ρ ^ (1/3 : ℝ)) ≤ averagedTile E η M q ℓ δ) ∧
    averagedTile E η M q ℓ δ + K * (ρ * ρ ^ (1/3 : ℝ)) ≤
      K * (ρ * rateGrowth ρ q + ρ / (ℓ * δ))
  interior : TileInteriorComparison E η K
  dilation_integrable : TileDilationIntegrable E η K
  dilation : TileDilationComparison E η K

private theorem growth_nonneg {ρ : ℝ} (hr : 0 ≤ ρ) (q : Position) : 0 ≤ rateGrowth ρ q :=
  add_nonneg (add_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)) (sq_nonneg _)

private theorem bounded_reference {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (H : FiniteRateTiling E η K) {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) :
    atTop.IsBoundedUnder (· ≤ ·) (fun L => averagedTile E η M q L 1) ∧
    atTop.IsBoundedUnder (· ≥ ·) (fun L => averagedTile E η M q L 1) := by
  let ρ := M.trace.re
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have hK := zero_le_one.trans H.one_le
  have h := fun L (hL : 1 ≤ L) => H.rough M hM q L 1 (zero_lt_one.trans_le hL) zero_lt_one
  constructor
  · refine ⟨K * (ρ * rateGrowth ρ q + ρ), ?_⟩
    change ∀ᶠ L : ℝ in atTop, averagedTile E η M q L 1 ≤ K * (ρ * rateGrowth ρ q + ρ)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hu := (h L hL).2
    have hdiv : ρ / (L * 1) ≤ ρ := by rw [mul_one]; exact div_le_self hr hL
    have hmul := mul_le_mul_of_nonneg_left (add_le_add_right hdiv (ρ * rateGrowth ρ q)) hK
    have hf := mul_nonneg hK (mul_nonneg hr (Real.rpow_nonneg hr (1/3 : ℝ)))
    change averagedTile E η M q L 1 + K * (ρ * ρ ^ (1/3 : ℝ)) ≤ _ at hu
    linarith
  · exact ⟨-K * (ρ * ρ ^ (1/3 : ℝ)), (eventually_ge_atTop (1 : ℝ)).mono fun L hL => (h L hL).1⟩

private theorem pass_below {f : ℝ → ℝ} {a b : ℝ}
    (hb : atTop.IsBoundedUnder (· ≤ ·) f) (h : ∀ᶠ L : ℝ in atTop, a - b / L ≤ f L) :
    a ≤ limsup f atTop := by
  have ht : Tendsto (fun L : ℝ => a - b / L) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a) (f := (atTop : Filter ℝ))).sub (tendsto_id.const_div_atTop b)
  exact ht.limsup_eq ▸ limsup_le_limsup h ht.isCoboundedUnder_le hb

private theorem pass_above {f : ℝ → ℝ} {a b : ℝ}
    (hb : atTop.IsBoundedUnder (· ≥ ·) f) (h : ∀ᶠ L : ℝ in atTop, f L ≤ a + b / L) :
    limsup f atTop ≤ a := by
  have ht : Tendsto (fun L : ℝ => a + b / L) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a) (f := (atTop : Filter ℝ))).add (tendsto_id.const_div_atTop b)
  exact ht.limsup_eq ▸ limsup_le_limsup h hb.isCoboundedUnder_le ht.isBoundedUnder_le

/-- The upper estimate at fixed inner scale. The extra term from the cutoff
gradient in the rough inner energy is absorbed using δ ≤ ℓ. -/
theorem FiniteRateTiling.upper_rate {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (H : FiniteRateTiling E η K) {M : SpinMatrix} (hM : M.PosSemidef) (q : Position)
    {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hscale : δ * K ≤ ℓ) :
    averagedTile E η M q ℓ δ ≤ sswEnergy E η M q + (K ^ 2 + K) * upperRateError M.trace.re q ℓ δ := by
  let ρ := M.trace.re
  let e := averagedTile E η M q ℓ δ
  let floor := K * (ρ * ρ ^ (1/3 : ℝ))
  let rem := K * (ρ / ℓ) * (1 + δ⁻¹ + δ ^ 3 * ρ)
  let b := (ℓ + δ + 1) * (K * (e + floor) + floor)
  have hK := zero_le_one.trans H.one_le
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have hi : e - K * (δ / ℓ) * (e + floor) - rem ≤ sswEnergy E η M q := by
    apply pass_below (b := b) (bounded_reference H hM q).1
    filter_upwards [H.interior M hM q ℓ δ hℓ hδ hscale] with L hL
    have ht := hL.estimate
    change e - K * (δ / ℓ + (ℓ + δ + 1) / L) * (e + floor) -
      (floor * ((ℓ + δ + 1) / L) + rem) ≤ _ at ht
    convert ht using 1
    dsimp only [b]
    ring
  have hfrac : δ / ℓ ≤ 1 := (div_le_one hℓ).mpr ((le_mul_of_one_le_right hδ.le H.one_le).trans hscale)
  have hfactor := mul_nonneg hK (div_nonneg hδ.le hℓ.le)
  have rough := mul_le_mul_of_nonneg_left (H.rough M hM q ℓ δ hℓ hδ).2 hfactor
  change K * (δ / ℓ) * (e + floor) ≤ K * (δ / ℓ) * (K * (ρ * rateGrowth ρ q + ρ / (ℓ * δ))) at rough
  have hs := mul_le_mul_of_nonneg_right hfrac (show 0 ≤ K ^ 2 * (ρ / (ℓ * δ)) by positivity)
  have hy : 0 ≤ ρ / ℓ * (δ * rateGrowth ρ q) :=
    mul_nonneg (div_nonneg hr hℓ.le) (mul_nonneg hδ.le (growth_nonneg hr q))
  have comb : K * (δ / ℓ) * (K * (ρ * rateGrowth ρ q + ρ / (ℓ * δ))) + rem ≤
      (K ^ 2 + K) * upperRateError ρ q ℓ δ := by
    calc
      _ = K ^ 2 * (ρ / ℓ * (δ * rateGrowth ρ q)) +
          (δ / ℓ) * (K ^ 2 * (ρ / (ℓ * δ))) + rem := by ring
      _ ≤ K ^ 2 * (ρ / ℓ * (δ * rateGrowth ρ q)) + K ^ 2 * (ρ / (ℓ * δ)) + rem := by
        linarith only [hs]
      _ ≤ _ := by
        have hdiv : ρ / (ℓ * δ) = ρ / ℓ * δ⁻¹ := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        rw [hdiv]
        dsimp only [upperRateError, lowerRateError, rem]
        nlinarith only [mul_nonneg (sq_nonneg K) (div_nonneg hr hℓ.le),
          mul_nonneg (sq_nonneg K) (mul_nonneg (div_nonneg hr hℓ.le) (mul_nonneg (pow_nonneg hδ.le 3) hr)),
          mul_nonneg hK hy]
  change e ≤ _ + (K ^ 2 + K) * upperRateError ρ q ℓ δ
  linarith only [hi, rough, comb]

/-- Removing the vanishing boundary and outer-gradient errors before
replacing the upper tiling scale by ℓ + δ. -/
theorem FiniteRateTiling.lower_rate {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (H : FiniteRateTiling E η K) {M : SpinMatrix} (hM : M.PosSemidef) (q : Position)
    {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hscale : δ * K ≤ ℓ) :
    sswEnergy E η M q - K * lowerRateError M.trace.re q ℓ δ ≤
      scaleAverage (fun t => averagedTile E η M q (t * ℓ) (t * δ)) := by
  let ρ := M.trace.re
  let u := ℓ + δ
  let e := scaleAverage (fun t => averagedTile E η M q (t * ℓ) (t * δ))
  let b := K * (ρ * rateGrowth ρ q * (u + δ + 1) + ρ)
  have hu : 0 < u := add_pos hℓ hδ
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have hs : δ * K ≤ u := hscale.trans (le_add_of_nonneg_right hδ.le)
  have hi : sswEnergy E η M q ≤ e + K * lowerRateError ρ q u δ := by
    apply pass_above (b := b) (bounded_reference H hM q).2
    filter_upwards [H.dilation M hM q u δ hu hδ hs] with L hfinite
    have hut : u - δ = ℓ := add_sub_cancel_right ℓ δ
    rw [hut] at hfinite
    have hL := finite_upper_at_half_le_one (H.dilation_integrable M hM q ℓ δ hℓ hδ hscale)
      (mul_nonneg (zero_le_one.trans H.one_le) (div_nonneg (mul_nonneg (pow_nonneg hδ.le 3) (sq_nonneg ρ)) hu.le))
      hfinite
    change _ ≤ e + K * (ρ * rateGrowth ρ q * (δ / u + (u + δ + 1) / L) +
        ρ * (1 / (u * δ) + 1 / L)) + K * (δ ^ 3 * ρ ^ 2 / u) at hL
    convert hL using 1
    dsimp only [b, lowerRateError]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hmono : lowerRateError ρ q u δ ≤ lowerRateError ρ q ℓ δ :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hr hℓ (le_add_of_nonneg_right hδ.le))
      (add_nonneg (add_nonneg (inv_nonneg.mpr hδ.le) (mul_nonneg (pow_nonneg hδ.le _) hr))
        (mul_nonneg hδ.le (growth_nonneg hr q)))
  change _ - K * lowerRateError ρ q ℓ δ ≤ e
  linarith only [hi, mul_le_mul_of_nonneg_left hmono (zero_le_one.trans H.one_le)]

/-- Proposition `prop:rate_SSW`. The same constant works in the scale
threshold and both rate bounds, uniformly in matrix and wavevector. -/
theorem FiniteRateTiling.tetrahedron_rate {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (H : FiniteRateTiling E η K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : SpinMatrix, M.PosSemidef → ∀ (q : Position) (ℓ δ : ℝ),
      0 < ℓ → 0 < δ → δ ≤ ℓ / C →
      averagedTile E η M q ℓ δ ≤ sswEnergy E η M q + C * upperRateError M.trace.re q ℓ δ ∧
      sswEnergy E η M q - C * lowerRateError M.trace.re q ℓ δ ≤
        scaleAverage (fun t => averagedTile E η M q (t * ℓ) (t * δ)) := by
  have hK := H.one_le
  have hk : K ≤ K^2 + K := by linarith [sq_nonneg K]
  refine ⟨K^2 + K, hK.trans hk, ?_⟩
  intro M hM q ℓ δ hℓ hδ hscale
  have hs := (mul_le_mul_of_nonneg_left hk hδ.le).trans ((le_div_iff₀ (by linarith)).1 hscale)
  refine ⟨H.upper_rate hM q hℓ hδ hs, ?_⟩
  have hr := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have he : 0 ≤ lowerRateError M.trace.re q ℓ δ :=
    mul_nonneg (div_nonneg hr hℓ.le) (add_nonneg (add_nonneg (inv_nonneg.mpr hδ.le)
      (mul_nonneg (pow_nonneg hδ.le _) hr)) (mul_nonneg hδ.le (growth_nonneg hr q)))
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_right hk he) _).trans (H.lower_rate hM q hℓ hδ hs)

/-- Before simplifying the density powers to ρ+ρ², the finite bounds retain
the Lieb–Oxford floor and the Thomas–Fermi density power. -/
theorem FiniteRateTiling.ssw_power_bounds {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (H : FiniteRateTiling E η K) {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) :
    -K * (M.trace.re * M.trace.re ^ (1/3 : ℝ)) ≤ sswEnergy E η M q ∧
    sswEnergy E η M q ≤ K * (M.trace.re * rateGrowth M.trace.re q) := by
  have hK := zero_le_one.trans H.one_le
  let ρ := M.trace.re
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  obtain ⟨hub, hlb⟩ := bounded_reference H hM q
  have hfloor : 0 ≤ K * (ρ * ρ ^ (1/3 : ℝ)) := mul_nonneg hK (mul_nonneg hr (Real.rpow_nonneg hr _))
  have hlo : -K * (ρ * ρ ^ (1/3 : ℝ)) ≤ sswEnergy E η M q := by
    apply pass_below (b := 0) hub
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    simpa using (H.rough M hM q L 1 hL zero_lt_one).1
  have hhi : sswEnergy E η M q ≤ K * (ρ * rateGrowth ρ q) := by
    apply pass_above (b := K * ρ) hlb
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have h := (H.rough M hM q L 1 hL zero_lt_one).2
    change averagedTile E η M q L 1 + K * (ρ * ρ ^ (1/3 : ℝ)) ≤
      K * (ρ * rateGrowth ρ q + ρ / (L * 1)) at h
    simp only [mul_one] at h
    calc
      _ ≤ averagedTile E η M q L 1 + K * (ρ * ρ ^ (1/3 : ℝ)) := le_add_of_nonneg_right hfloor
      _ ≤ _ := h
      _ = _ := by ring
  exact ⟨hlo, hhi⟩

/-- Growth of the thermodynamic energy follows from the finite rough bounds.
The outer cutoff-gradient error vanishes and the same constant covers vacuum. -/
theorem FiniteRateTiling.gas_growth {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (H : FiniteRateTiling E η K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ M : SpinMatrix, M.PosSemidef → ∀ q : Position,
      |sswEnergy E η M q| ≤ A * (M.trace.re + M.trace.re ^ 2 + M.trace.re * ‖q‖ ^ 2) := by
  have hK := zero_le_one.trans H.one_le
  refine ⟨2 * K, by positivity, ?_⟩
  intro M hM q
  let ρ := M.trace.re
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  obtain ⟨hlo, hhi⟩ := H.ssw_power_bounds hM q
  change -K * (ρ * ρ ^ (1/3 : ℝ)) ≤ _ at hlo
  change _ ≤ K * (ρ * rateGrowth ρ q) at hhi
  have hpow (a : ℝ) (ha : 0 ≤ a) (h₁ : a ≤ 1) : ρ ^ a ≤ 1 + ρ := by
    by_cases h : ρ ≤ 1
    · exact (Real.rpow_le_one hr h ha).trans (le_add_of_nonneg_right hr)
    · exact (Real.rpow_one ρ ▸ Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) h₁).trans
        (by linarith)
  have hthird := mul_le_mul_of_nonneg_left (hpow (1/3) (by norm_num) (by norm_num)) hr
  have htwo := mul_le_mul_of_nonneg_left (hpow (2/3) (by norm_num) (by norm_num)) hr
  have hq := mul_nonneg hr (sq_nonneg ‖q‖)
  have hsmall : ρ * ρ ^ (1/3 : ℝ) ≤ 2 * (ρ + ρ ^ 2 + ρ * ‖q‖ ^ 2) := by
    nlinarith only [hthird, hr, sq_nonneg ρ, hq]
  have hbig : ρ * rateGrowth ρ q ≤ 2 * (ρ + ρ ^ 2 + ρ * ‖q‖ ^ 2) := by
    dsimp [rateGrowth]
    nlinarith only [hthird, htwo, hq]
  change |sswEnergy E η M q| ≤ 2 * K * (ρ + ρ ^ 2 + ρ * ‖q‖ ^ 2)
  exact abs_le.mpr ⟨by linarith only [hlo, mul_le_mul_of_nonneg_left hsmall hK],
    by linarith only [hhi, mul_le_mul_of_nonneg_left hbig hK]⟩

/-- Measurability along one reference sequence of finite tetrahedra suffices
for the local SSW integrand, including where the density is the vacuum. -/
theorem local_ssw_aestronglyMeasurable {E : EnergyFunctional} {η : Mollifier}
    (vacuum : E 0 = 0)
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position,
      FiniteLocalization E η M q) {D : Density} {φ : Phase}
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun x =>
      averagedTile E η (D.matrix x) (φ.grad x) (n : ℝ) 1) volume) :
    AEStronglyMeasurable (fun x => sswEnergy E η (D.matrix x) (φ.grad x)) volume := by
  apply aestronglyMeasurable_of_tendsto_ae atTop hmeas
  filter_upwards with x
  by_cases hr : 0 < (D.matrix x).trace.re
  · exact ((loc _ (D.positive x) hr _).tile_tendsto zero_lt_one).comp tendsto_natCast_atTop_atTop
  · have hpos := RCLike.nonneg_iff.mp (D.positive x).trace_nonneg
    have hm : D.matrix x = 0 := (D.positive x).trace_eq_zero_iff.mp
      (Complex.ext (le_antisymm (le_of_not_gt hr) hpos.1) hpos.2)
    have hz (k : Position) (L : ℝ) : tileEnergy E η 0 L 1 k = 0 := by
      have hf : cutoffSpiral (smoothedIndicator (tetrahedron L) η 1) 0 k = 0 :=
        funext (cutoffSpiral_zero_matrix _ k)
      simp [tileEnergy, hf, vacuum]
    have ht (L : ℝ) : tileEnergy E η 0 L 1 = fun _ => 0 := funext fun k => hz k L
    simp [hm, averagedTile, ht, sswEnergy_vacuum vacuum]

end TSGA.SSW
