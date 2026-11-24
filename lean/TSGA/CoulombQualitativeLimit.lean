import TSGA.CoulombUpperComparison
import TSGA.CoulombDilationMeasure
import TSGA.CoulombTransportModel

/-! # The SSW thermodynamic limit with a quadratic electrostatic error

At a fixed inner smoothing width δ the quadratic upper localization error
persists in the large-domain limit. The lower tiling theorem constructs the
same tetrahedral limit for every δ > 0. We can therefore let δ decrease to
zero after taking the domain limit.
-/

noncomputable section
namespace TSGA.ManyBody

open SSW MeasureTheory Filter Set Metric
open scoped Topology ComplexOrder

private theorem fixed_tile_bounds (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (diff : SobolevDifferenceBounds) (η : Mollifier) {M : SpinMatrix} (hM : M.PosSemidef)
    (q : Position) : TileBounds (averagedTile energy η M q) := by
  obtain ⟨K,hK,rough⟩ := H.exists_rough_constant sob diff η
  let ρ := M.trace.re
  let A := K*(ρ*ρ^(1/3:ℝ))
  let B := max (K*(ρ*rateGrowth ρ q)) (K*ρ)
  have hk : 0 ≤ K := zero_le_one.trans hK
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have ha : 0 ≤ A := mul_nonneg hk (mul_nonneg hr (Real.rpow_nonneg hr _))
  refine ⟨A,B,ha,(mul_nonneg hk hr).trans (le_max_right _ _),?_⟩
  intro ℓ δ he hd
  obtain ⟨hlo,hup⟩ := rough K le_rfl M hM q ℓ δ he hd
  refine ⟨by simpa only [A,ρ,neg_mul] using hlo,?_⟩
  calc
    _ ≤ averagedTile energy η M q ℓ δ + A := le_add_of_nonneg_right ha
    _ ≤ K*(ρ*rateGrowth ρ q+ρ/(ℓ*δ)) := hup
    _ = K*(ρ*rateGrowth ρ q)+(K*ρ)/(ℓ*δ) := by ring
    _ ≤ _ := add_le_add (le_max_left ..) (div_le_div_of_nonneg_right (le_max_right ..) (mul_pos he hd).le)

private theorem common_tile_limit {η : Mollifier} {M : SpinMatrix} {q : Position}
    (bounds : TileBounds (averagedTile energy η M q)) (two : TetrahedronTwoScale energy η M q)
    {δ : ℝ} (hd : 0 < δ) :
    Tendsto (fun ℓ => averagedTile energy η M q ℓ δ) atTop (𝓝 (sswEnergy energy η M q)) := by
  apply TileComparison.tendsto _ hd
  apply TileComparison.of_two_scales bounds.eventually_bounded
  intro δ d hδ hD
  obtain ⟨c,k,b,m,hc,h⟩ := two δ d hδ hD
  refine ⟨c,k,b,m,hc,?_⟩
  filter_upwards [h] with ℓ hℓ
  filter_upwards [hℓ] with L hL
  simpa only [averagedTile,sub_sub,add_assoc] using hL.estimate

private theorem lower_eventually {η : Mollifier} {M : SpinMatrix} {q : Position} (D : DomainSequence)
    (bounds : TileBounds (averagedTile energy η M q)) (two : TetrahedronTwoScale energy η M q)
    (lower : DomainLowerTiling energy η M q) {x : ℝ} (hx : x < sswEnergy energy η M q) :
    ∀ᶠ n in atTop, x < D.energyDensity energy M n q := by
  have htile := (common_tile_limit bounds two zero_lt_one).comp D.tileLength_tendsto
  have hsmall := D.tileLength_tendsto.inv_tendsto_atTop
  obtain ⟨a,ha,c,k,b,m,loc⟩ := lower D
  have hfrac := D.tileBoundaryLayer_tendsto_zero a ha
  have hw := (hsmall.add hfrac).const_mul c
  have h := (htile.sub (hw.mul (htile.add_const k))).sub ((hfrac.const_mul b).add
    (D.tileLength_tendsto.const_div_atTop m))
  simp only [Function.comp_apply,Pi.inv_apply,add_zero,mul_zero,zero_mul,sub_zero] at h
  filter_upwards [h.eventually_const_lt hx,loc] with n hn hloc
  exact hn.trans_le hloc.estimate

private theorem scale_limit_width {η : Mollifier} (borel : LevyLiebBorel) {M : SpinMatrix} {q : Position}
    (bounds : TileBounds (averagedTile energy η M q)) (two : TetrahedronTwoScale energy η M q)
    (D : DomainSequence) {δ : ℝ} (hd : 0 < δ) :
    Tendsto (fun n => scaleAverage (fun t => averagedTile energy η M q (t*(D.tileLength n-δ)) (t*δ)))
      atTop (𝓝 (sswEnergy energy η M q)) := by
  let len := fun n => D.tileLength n-δ+1
  have hlen : Tendsto len atTop atTop := tendsto_atTop_add_const_right atTop 1 (by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-δ) D.tileLength_tendsto)
  have hw : ∀ᶠ n in atTop, AEStronglyMeasurable (fun t =>
      averagedTile energy η M q (t*(len n-1)) (t*δ)) (volume.restrict scaleInterval) := by
    filter_upwards [D.tileLength_tendsto.eventually_gt_atTop δ] with n hn
    apply coulomb_dilation_aeMeasurable borel η M q _ hd
    dsimp [len]
    linarith
  let tile := fun ℓ t => averagedTile energy η M q ℓ (t*δ)
  have bound : ∃ B : ℝ, ∀ ℓ ≥ 1, ∀ t ∈ scaleInterval, |tile ℓ t| ≤ B := by
    obtain ⟨a,b,ha,hb,h⟩ := bounds
    refine ⟨max a (b+b/(δ/2)),?_⟩
    intro ℓ he t ht
    have ht' : 1/2 ≤ t := ht.1
    have htδ : 0 < t*δ := mul_pos (by linarith) hd
    have hden : δ/2 ≤ ℓ*(t*δ) := by
      have h₁ := mul_le_mul_of_nonneg_right ht' hd.le
      have h₂ := le_mul_of_one_le_left htδ.le he
      linarith
    obtain ⟨lo,up⟩ := h ℓ (t*δ) (zero_lt_one.trans_le he) htδ
    exact abs_le.mpr ⟨(neg_le_neg (le_max_left ..)).trans lo,
      (up.trans (add_le_add le_rfl (div_le_div_of_nonneg_left hb (by positivity) hden))).trans (le_max_right ..)⟩
  have ht := scaleAverage_tendsto (tile := tile) hlen (fun t ht => common_tile_limit bounds two (mul_pos ht hd)) hw bound
  simpa only [tile,len,add_sub_cancel_right] using ht

private theorem small_width {e b K ρ : ℝ} (hb : e < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ e+K*(δ^2*ρ^2) < b := by
  have cont : Continuous (fun d : ℝ => e+K*(d^2*ρ^2)) := by fun_prop
  have ht : Tendsto (fun d : ℝ => e+K*(d^2*ρ^2)) (𝓝[>] 0) (𝓝 e) := by
    simpa using cont.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have h1 : ∀ᶠ d in 𝓝[>] (0:ℝ), d < 1 := (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ d in 𝓝[>] (0:ℝ), 0 < d := self_mem_nhdsWithin
  exact (hpos.and (h1.and (ht.eventually_lt_const hb))).exists.imp
    fun d h => ⟨h.1,h.2.1.le,h.2.2⟩

/-- Convergence on every allowed outer domain from the quadratic upper
electrostatic estimate of the compensated tiling. -/
theorem coulomb_limit_of_quadratic_tiling {η : Mollifier} (L : CoulombLowerLocalization η)
    (U : CoulombUpperLocalization η .quadratic) (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (diff : SobolevDifferenceBounds) (borel : LevyLiebBorel) {M : SpinMatrix} (hM : M.PosSemidef)
    (q : Position) (D : DomainSequence) :
    Tendsto (fun n => D.energyDensity energy M n q) atTop (𝓝 (sswEnergy energy η M q)) := by
  let e := sswEnergy energy η M q
  let K := U.constant H
  let ρ := M.trace.re
  let P := ρ*rateGrowth ρ q
  let G := domainCutoffGradient sob diff D
  have bounds := fixed_tile_bounds H sob diff η hM q
  obtain ⟨K₀,_,h⟩ := L.comparisons H sob
  have two := (h K₀ le_rfl).1 M hM q
  refine tendsto_order.2 ⟨fun _ hb => lower_eventually D bounds two (L.domain_lower H sob hM q) hb,?_⟩
  intro b hb
  obtain ⟨δ,hd,hd1,hb'⟩ := small_width (e := e) (K := K) (ρ := ρ) hb
  obtain ⟨a,ha,upper⟩ := U.open_upper H sob D.mollifier
  let B := D.tileBoundaryFraction a
  let tile := fun n t => averagedTile energy η M q (t*(D.tileLength n-δ)) (t*δ)
  have hm := scale_limit_width borel bounds two D hd
  have hδ := D.tileLength_tendsto.const_div_atTop δ
  have hk := (D.tileLength_tendsto.const_div_atTop δ⁻¹).add G.cost_tendsto_zero
  have hconv := (hm.add (((hδ.add (D.tileBoundaryLayer_tendsto_zero a ha)).const_mul P).add
    (hk.const_mul ρ) |>.const_mul K)).add_const (K*(δ^2*ρ^2))
  simp only [add_zero,mul_zero] at hconv
  filter_upwards [hconv.eventually_lt_const hb',D.tileLength_tendsto.eventually_gt_atTop (2*δ)] with n hn hlen
  let ℓ := D.tileLength n
  have he : 0 < ℓ := D.tileLength_pos n
  have hint := coulomb_tileDilationIntegrable borel η H sob diff 0 M hM q (ℓ-δ) δ
    (by change 2*δ < ℓ at hlen; linarith) hd (by change 2*δ < ℓ at hlen; linarith)
  have hu := upper (D.region_open n) (D.region_bounded n) (D.vol_pos n) (D.delta_pos n) (G.grad n)
    (G.weak n) hd (show δ ≤ ℓ/2 by change 2*δ < ℓ at hlen; linarith) hM q hint
  have hK := U.constant_nonneg H
  have hraw := finite_upper_at_half_le_one hint (show 0 ≤ K*(δ^2*ρ^2) from mul_nonneg hK (by positivity)) hu
  let bd := Metric.thickening (a*(ℓ+δ+D.delta n)) (frontier (D.region n))
  have hfrac : regionVolume bd / D.vol n ≤ B n := by
    apply div_le_div_of_nonneg_right _ (D.vol_pos n).le
    exact measureReal_mono (μ := volume) (Metric.thickening_mono (mul_le_mul_of_nonneg_left
      (by linarith : ℓ+δ+D.delta n ≤ ℓ+1+D.delta n) ha.le) _)
      ((D.region_bounded n).closure.subset frontier_subset_closure).thickening.measure_lt_top.ne
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have hP : 0 ≤ P := mul_nonneg hr (add_nonneg (add_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)) (sq_nonneg _))
  have hcoef := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfrac hP) hK
  change D.energyDensity energy M n q ≤ scaleAverage (tile n) +
    K*(P*(δ/ℓ+regionVolume bd/D.vol n)+ρ*(1/(ℓ*δ)+G.cost n)) + K*(δ^2*ρ^2) at hraw
  change scaleAverage (tile n)+K*(P*(δ/ℓ+B n)+ρ*(δ⁻¹/ℓ+G.cost n))+K*(δ^2*ρ^2) < b at hn
  rw [show 1/(ℓ*δ) = δ⁻¹/ℓ by ring] at hraw
  linarith only [hraw,hcoef,hn]

/-- The full SSW gas theorem from qualitative localization, using the
quadratic Coulomb error. The quantitative convergence rate is independent. -/
theorem coulomb_sswGas_of_quadratic_tiling {η : Mollifier} (L : CoulombLowerLocalization η)
    (U : CoulombUpperLocalization η .quadratic) (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (diff : SobolevDifferenceBounds) (borel : LevyLiebBorel) : SSWGasTheorem (referenceEnergies energy η) :=
  sswGas_theorem_of_convergence η energy_vacuum (fun _ hM _ q D =>
    coulomb_limit_of_quadratic_tiling L U H sob diff borel hM q D) (DomainSequence.balls unitBallMollifier)
    (fun M ζ θ h n => (ballSpiralKinematics H sob (coulombSpiralTransport (DomainSequence.balls unitBallMollifier))
      M ζ θ h n).finiteSpinLaws)

end TSGA.ManyBody
