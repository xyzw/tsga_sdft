import TSGA.CoulombUpperTiling
import TSGA.CoulombLowerTiling
import TSGA.CoulombCutoffArea

/-! # The two upper comparisons from finite localized Coulomb trials

The same finite trial construction is used on a general open domain and on
the large reference tetrahedron. Keeping the interior-center integral
separate exposes the loss of its volume fraction when the tile energy is
negative.
-/

noncomputable section
namespace TSGA.ManyBody
open SSW TSGA.Localization MeasureTheory Filter Set Metric
open scoped ComplexOrder Topology

/-- Electrostatic error of the compensated tiling, either at the earlier
quadratic bound or at the cubic bound proved in the manuscript. -/
inductive CoulombTilingCost where
  | cubic
  | quadratic

def CoulombTilingCost.cost : CoulombTilingCost → ℝ → ℝ → ℝ
  | .cubic, ℓ, δ => δ^3/ℓ
  | .quadratic, _, δ => δ^2

theorem CoulombTilingCost.cost_nonneg (p : CoulombTilingCost) {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ) :
    0 ≤ p.cost ℓ δ := by
  cases p <;> dsimp [cost] <;> positivity

/-- Interior energy counted at the density of centers of the original cell.
The window is shrunken, but the denominator is the unshrunk tile volume. -/
def upperInteriorEnergy (O : TileOrientationLaw) (η : Mollifier) (I : Set Position)
    (M : SpinMatrix) (q : Position) (ℓ δ t : ℝ) : ℝ :=
  ∫ R, ∫ z in I, energy (cutoffSpiral (centeredWindow η (t*(ℓ-δ)) (t*δ) (O.frame R) z) M q) /
    regionVolume (tetrahedron (t*ℓ)) ∂volume ∂O.law

/-- Finite product-state input to the upper comparison. The interior term
sums the actual energies of whole localized tetrahedra over centers and frames.
The remaining state costs consist of boundary and skeleton kinetic energy and
the direct electrostatic error of the averaged product. -/
structure CoulombUpperLocalization (η : Mollifier) (p : CoulombTilingCost := .cubic) where
  orientations : TileOrientationLaw
  coefficient : ℝ
  nonneg : 0 ≤ coefficient
  trials : ∀ χ : Mollifier, ∃ a > 0, ∀ {Ω : Set Position}, IsOpen Ω → Bornology.IsBounded Ω →
    0 < regionVolume Ω → ∀ {d : ℝ}, 0 < d → ∀ (G : Position → Position),
    (∀ i, WeakPartialOn univ i (fun x => √(smoothedIndicator Ω χ d x)) (fun x => G x i)) →
    ∀ {ℓ δ : ℝ}, 0 < δ → δ ≤ ℓ/2 → ∀ {M : SpinMatrix}, M.PosSemidef → ∀ q : Position,
    ∀ α : ℝ, 0 < α → α < 1/2 → ∀ ε > 0,
    let V := regionVolume Ω
    let ρ := M.trace.re
    let F := cutoffSpiral (smoothedIndicator Ω χ d) M q
    let B := thickening (a*(ℓ+δ+d)) (frontier Ω)
    ∃ Γ : MixedState, feasible F Γ ∧
      localStateEnergy Γ F ≤ scaleAverageAt α (upperInteriorEnergy orientations η (Ω \ B) M q ℓ δ) +
        coefficient * (ρ*rateGrowth ρ q*(V*δ/ℓ + regionVolume B) +
          ρ*(V/(ℓ*δ) + ∫ x, ‖G x‖^2)) +
        (coefficient*p.cost ℓ δ)*(∫ x, (F x).trace.re^2)*Real.log α⁻¹ + ε

theorem upperInteriorEnergy_eq {η : Mollifier} (O : TileOrientationLaw)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (I : Set Position)
    {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) {ℓ δ t : ℝ} (hδ : 0 < δ)
    (hd : δ < ℓ) (ht : 0 < t) :
    upperInteriorEnergy O η I M q ℓ δ t =
      (regionVolume I * (1-δ/ℓ)^3) * averagedTile energy η M q (t*(ℓ-δ)) (t*δ) := by
  let V := regionVolume (tetrahedron (t*ℓ))
  let v := regionVolume (tetrahedron (t*(ℓ-δ)))
  have he : 0 < ℓ := hδ.trans hd
  have hv : 0 < v := tetrahedron_volume_pos (mul_pos ht (sub_pos.mpr hd))
  have hV : 0 < V := tetrahedron_volume_pos (mul_pos ht he)
  have ratio : v / V = (1-δ/ℓ)^3 := by
    dsimp only [v,V]
    rw [tetrahedron_volume (mul_pos ht (sub_pos.mpr hd)),tetrahedron_volume (mul_pos ht he)]
    field_simp [he.ne',ht.ne']
  let E := tileEnergy energy η M (t*(ℓ-δ)) (t*δ)
  have step (R : O.Frames) (z : Position) :
      energy (cutoffSpiral (centeredWindow η (t*(ℓ-δ)) (t*δ) (O.frame R) z) M q) / V =
        (1-δ/ℓ)^3 * E (O.frame R q) := by
    have hstate : energy (cutoffSpiral (centeredWindow η (t*(ℓ-δ)) (t*δ)
        (O.frame R) z) M q) / v = E (O.frame R q) :=
      centered_energy η _ _ _ z M q
    rw [← ratio,← hstate]
    field_simp [hv.ne',hV.ne']
  have hr := O.average E (coulomb_continuous_tile H sob η (mul_pos ht (sub_pos.mpr hd))
    (mul_pos ht hδ) hM) q
  unfold upperInteriorEnergy
  change (∫ R, ∫ z in I, _ / V ∂volume ∂O.law) = _
  simp_rw [step, setIntegral_const,smul_eq_mul, ← mul_assoc]
  rw [integral_const_mul,hr.2]
  rfl

private theorem interval_subset {α : ℝ} (hα : α < 1/2) : Icc (1-α) (1+α) ⊆ scaleInterval := by
  intro t ht
  exact ⟨by linarith [ht.1],by linarith [ht.2]⟩

private theorem averageAt_const_lower {α k : ℝ} (hα : 0 < α) (hsmall : α < 1/2)
    {f : ℝ → ℝ} (hi : IntegrableOn (fun t => f t * scaleWeight t) scaleInterval)
    (hfloor : ∀ t ∈ scaleInterval, -k ≤ f t) : -k ≤ scaleAverageAt α f := by
  let J := Icc (1-α) (1+α)
  have hsub : J ⊆ scaleInterval := interval_subset hsmall
  have hw := scaleWeight_integrableOn.mono_set hsub
  have hp : 0 < ∫ t in J, scaleWeight t := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae _ hw).2
    · have hs : J ⊆ Function.support scaleWeight := by
        intro t ht
        have hl := (hsub ht).1
        exact inv_ne_zero (pow_ne_zero _ (by linarith))
      rw [inter_eq_right.mpr hs,Real.volume_Icc]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    · exact ae_of_all _ fun t => inv_nonneg.mpr (by positivity : 0 ≤ t^4)
  apply (le_div_iff₀ hp).2
  rw [← integral_const_mul]
  apply integral_mono_ae (hw.const_mul _) (hi.mono_set hsub)
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (s := J) measurableSet_Icc] with t ht
  exact mul_le_mul_of_nonneg_right (hfloor t (hsub ht)) (inv_nonneg.mpr (by positivity : 0 ≤ t^4))

private theorem averageAt_congr_mul {α c : ℝ} {f g : ℝ → ℝ}
    (h : ∀ t ∈ Icc (1-α) (1+α), f t = c*g t) : scaleAverageAt α f = c*scaleAverageAt α g := by
  unfold scaleAverageAt
  have e : (∫ t in Icc (1-α) (1+α), f t * scaleWeight t) =
      ∫ t in Icc (1-α) (1+α), c * (g t * scaleWeight t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
    rw [h t ht,mul_assoc]
  rw [e,integral_const_mul]
  ring

private theorem averaged_floor (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (η : Mollifier) {M : SpinMatrix} (hM : M.PosSemidef) (q : Position)
    {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ) :
    -(H.loCoeff*M.trace.re^(4/3:ℝ)) ≤ averagedTile energy η M q ℓ δ := by
  let k := H.loCoeff*M.trace.re^(4/3:ℝ)
  have h := direction_mono_add (f := fun _ => -k) (d := 0) (integrable_const (-k))
    (continuous_direction_integrable (coulomb_continuous_tile H sob η he hd hM) q)
    (fun ω => by rw [add_zero]; exact tile_floor H sob η he hd hM _)
  simpa only [averagedTile,directionAverage_const,add_zero] using h

private theorem rhoGrowth_nonneg {ρ : ℝ} (hr : 0 ≤ ρ) (q : Position) : 0 ≤ ρ*rateGrowth ρ q :=
  mul_nonneg hr (add_nonneg (add_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)) (sq_nonneg _))

/-- Uniform coefficient after adding the Lieb–Oxford cost of the missing
interior fraction. -/
def CoulombUpperLocalization.constant {η : Mollifier} {p : CoulombTilingCost} (U : CoulombUpperLocalization η p)
    (H : FiniteEnergyInputs) : ℝ := U.coefficient + 3*H.loCoeff

theorem CoulombUpperLocalization.constant_nonneg {η : Mollifier} {p : CoulombTilingCost} (U : CoulombUpperLocalization η p)
    (H : FiniteEnergyInputs) : 0 ≤ U.constant H := by
  unfold constant
  linarith [U.nonneg,H.lo_nonneg]

/-- Open-domain estimate before inserting either boundary geometry. -/
theorem CoulombUpperLocalization.open_upper {η : Mollifier} {p : CoulombTilingCost} (U : CoulombUpperLocalization η p)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (χ : Mollifier) :
    ∃ a > 0, ∀ {Ω : Set Position}, IsOpen Ω → Bornology.IsBounded Ω → 0 < regionVolume Ω →
    ∀ {d : ℝ}, 0 < d → ∀ (G : Position → Position),
    (∀ i, WeakPartialOn univ i (fun x => √(smoothedIndicator Ω χ d x)) (fun x => G x i)) →
    ∀ {ℓ δ : ℝ}, 0 < δ → δ ≤ ℓ/2 → ∀ {M : SpinMatrix}, M.PosSemidef → ∀ q : Position,
    let V := regionVolume Ω
    let ρ := M.trace.re
    let f := fun t => averagedTile energy η M q (t*(ℓ-δ)) (t*δ)
    IntegrableOn (fun t => f t * scaleWeight t) scaleInterval →
    ∀ α : ℝ, 0 < α → α < 1/2 →
    energy (cutoffSpiral (smoothedIndicator Ω χ d) M q) / V ≤ scaleAverageAt α f +
      U.constant H*(ρ*rateGrowth ρ q*(δ/ℓ + regionVolume (thickening (a*(ℓ+δ+d)) (frontier Ω))/V) +
        ρ*(1/(ℓ*δ) + (∫ x, ‖G x‖^2)/V)) +
      (U.constant H*(p.cost ℓ δ*ρ^2))*Real.log α⁻¹ := by
  obtain ⟨a,ha,trial⟩ := U.trials χ
  refine ⟨a,ha,?_⟩
  intro Ω hop hbd hV d hd G hw ℓ δ hδ hs M hM q V ρ f hi α hα hhalf
  let B := thickening (a*(ℓ+δ+d)) (frontier Ω)
  let I := Ω \ B
  let F := cutoffSpiral (smoothedIndicator Ω χ d) M q
  let C := U.coefficient
  let K := U.constant H
  let b := regionVolume B / V
  let g := (∫ x, ‖G x‖^2)/V
  let e := scaleAverageAt α f
  let r := δ/ℓ
  let w := centerWeight Ω B (1-(1-r)^3)
  let k := H.loCoeff*ρ^(4/3:ℝ)
  have he : 0 < ℓ := by linarith
  have hlt : δ < ℓ := by linarith
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have hk : 0 ≤ k := mul_nonneg H.lo_nonneg (Real.rpow_nonneg hr _)
  have hg : 0 ≤ g := div_nonneg (integral_nonneg fun _ => sq_nonneg _) hV.le
  have hb : 0 ≤ b := div_nonneg ENNReal.toReal_nonneg hV.le
  have hC : 0 ≤ C := U.nonneg
  have hCK : C ≤ K := by dsimp [K,C,constant]; linarith [H.lo_nonneg]
  have hlog : 0 ≤ Real.log α⁻¹ := Real.log_nonneg ((one_le_inv₀ hα).mpr (by linarith))
  have hpow : ρ^(4/3:ℝ) = ρ*ρ^(1/3:ℝ) := by
    calc
      _ = ρ^((1:ℝ)+1/3) := by norm_num
      _ = _ := by rw [Real.rpow_add' hr (by norm_num),Real.rpow_one]
  have hkg : k ≤ H.loCoeff*(ρ*rateGrowth ρ q) := by
    unfold k
    rw [hpow]
    apply mul_le_mul_of_nonneg_left _ H.lo_nonneg
    apply mul_le_mul_of_nonneg_left _ hr
    dsimp [rateGrowth]
    linarith [Real.rpow_nonneg hr (2/3:ℝ),sq_nonneg ‖q‖]
  have hr0 : 0 ≤ r := div_nonneg hδ.le he.le
  have hr1 : r ≤ 1 := (div_le_one he).2 hlt.le
  have hreg : volume B ≠ ⊤ :=
    ((hbd.closure.subset frontier_subset_closure).thickening).measure_lt_top.ne
  have hmass : (1-r)^3 ∈ Icc 0 1 := ⟨pow_nonneg (sub_nonneg.mpr hr1) _,pow_le_one₀
    (sub_nonneg.mpr hr1) (by linarith)⟩
  have hc := centerWeight_bounds (B := B) isOpen_thickening.measurableSet hbd.measure_lt_top.ne hreg hV
    (loss := 1-(1-r)^3) ⟨by linarith [hmass.2],by linarith [hmass.1]⟩
  have defic : 1-w ≤ 3*r+b := by
    have h₁ := CutoffSide.deficit .upper hr0 hr1
    change 1-(1-r)^3 ≤ 3*r at h₁
    have h₂ : 1-((1-(1-r)^3)+b) ≤ w := hc.2.1
    linarith
  have hf := averageAt_const_lower hα hhalf hi (k := k) (fun t ht => by
    have ht' : 0 < t := by linarith [ht.1]
    exact averaged_floor H sob η hM q (mul_pos ht' (sub_pos.mpr hlt)) (mul_pos ht' hδ))
  have miss : w*e ≤ e + (3*r+b)*k := by
    have hu : w ≤ 1 := hc.2.2
    nlinarith only [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ e+k by linarith [hf]),
      mul_le_mul_of_nonneg_right defic hk]
  let cost := ρ*rateGrowth ρ q*(r+b) + ρ*(1/(ℓ*δ)+g)
  have cost₀ : 0 ≤ cost := add_nonneg (mul_nonneg (rhoGrowth_nonneg hr q) (add_nonneg hr0 hb))
    (mul_nonneg hr (add_nonneg (by positivity) hg))
  have misscost : (3*r+b)*k + C*cost ≤ K*cost := by
    have cmp := mul_le_mul_of_nonneg_left hkg (show 0 ≤ 3*r+b by positivity)
    have grow := rhoGrowth_nonneg hr q
    have oth : 0 ≤ ρ*(1/(ℓ*δ)+g) := mul_nonneg hr (add_nonneg (by positivity) hg)
    have delta : (3*r+b)*(ρ*rateGrowth ρ q) ≤ 3*cost := by
      dsimp [cost]
      nlinarith only [mul_nonneg grow hb, oth]
    have comb := mul_le_mul_of_nonneg_left delta H.lo_nonneg
    dsimp only [K,constant,C] at *
    linarith only [cmp,comb]
  let vol := regionVolume I * (1-r)^3
  have av := averageAt_congr_mul (α := α) (c := vol) (f := upperInteriorEnergy U.orientations η I M q ℓ δ)
    (g := f) (fun t ht => upperInteriorEnergy_eq U.orientations H sob I hM q hδ hlt (by linarith [ht.1]))
  have hvol : vol/V = w := by dsimp [vol,w,centerWeight,I,r,V]; ring
  have charge := (cutoff_charge_integrals hop hbd hV χ hd M q).2
  change (∫ x, (F x).trace.re^2) ≤ V*ρ^2 at charge
  have hp0 := p.cost_nonneg he hδ
  have hcharge := mul_le_mul_of_nonneg_left charge (show 0 ≤ C*p.cost ℓ δ by positivity)
  have hcharge' := mul_le_mul_of_nonneg_right hcharge hlog
  have hmain : energy F ≤ vol*e + C*(ρ*rateGrowth ρ q*(V*δ/ℓ+regionVolume B)+
      ρ*(V/(ℓ*δ) + ∫ x, ‖G x‖^2)) + (C*p.cost ℓ δ)*(V*ρ^2)*Real.log α⁻¹ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨Γ,hΓ,htrial⟩ := trial hop hbd hV hd G hw hδ hs hM q α hα hhalf ε hε
    change localStateEnergy Γ F ≤ scaleAverageAt α (upperInteriorEnergy U.orientations η I M q ℓ δ) +
      C*(ρ*rateGrowth ρ q*(V*δ/ℓ+regionVolume B)+ρ*(V/(ℓ*δ)+∫ x, ‖G x‖^2)) +
      (C*p.cost ℓ δ)*(∫ x, (F x).trace.re^2)*Real.log α⁻¹+ε at htrial
    rw [av] at htrial
    have hz : energy F ≤ localStateEnergy Γ F := sub_le_sub_right (levyLieb_le hΓ) _
    dsimp only [e] at *
    linarith only [htrial,hz,hcharge']
  have hn : energy F/V ≤ w*e+C*cost+(C*(p.cost ℓ δ*ρ^2))*Real.log α⁻¹ := by
    apply (div_le_iff₀ hV).2
    apply hmain.trans_eq
    rw [← hvol]
    dsimp only [cost,r,b,g]
    field_simp [show V ≠ 0 from hV.ne']
    ring
  have es := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK
    (show 0 ≤ p.cost ℓ δ*ρ^2 by positivity)) hlog
  change energy F/V ≤ e+K*cost+(K*(p.cost ℓ δ*ρ^2))*Real.log α⁻¹
  linarith only [hn,miss,misscost,es]

/-- Upper comparison on arbitrary admissible domains by fixing the inner
width to one and using the left limit at α = 1/2. -/
theorem CoulombUpperLocalization.domain_upper {η : Mollifier} (U : CoulombUpperLocalization η)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (diff : SobolevDifferenceBounds)
    {J : ℝ} (hi : TileDilationIntegrable energy η J) {M : SpinMatrix} (hM : M.PosSemidef)
    (q : Position) : DomainUpperTiling energy η M q := by
  intro D
  obtain ⟨a,ha,hh⟩ := U.open_upper H sob D.mollifier
  let G := domainCutoffGradient sob diff D
  let K := U.constant H
  let ρ := M.trace.re
  refine ⟨G,a,ha,K*(ρ*rateGrowth ρ q),K*ρ,K*ρ^2,?_⟩
  filter_upwards [D.tileLength_tendsto.eventually_ge_atTop (max 3 (J+1))] with n hn
  let ℓ := D.tileLength n
  have hℓ : 3 ≤ ℓ := (le_max_left _ _).trans hn
  have hJ : J ≤ ℓ-1 := by linarith [(le_max_right 3 (J+1)).trans hn]
  let f := fun t => averagedTile energy η M q (t*(ℓ-1)) t
  have hint : IntegrableOn (fun t => f t * scaleWeight t) scaleInterval := by
    simpa only [one_mul,mul_one,f] using hi M hM q (ℓ-1) 1 (by linarith) zero_lt_one (by linarith)
  let E := D.energyDensity energy M n q
  let b := D.tileBoundaryFraction a n
  have hu (α : ℝ) (hp : 0 < α) (hlt : α < 1/2) :
      E ≤ scaleAverageAt α f + K*(ρ*rateGrowth ρ q*(1/ℓ+b)+ρ*(1/ℓ+G.cost n)) +
        (K*(ρ^2/ℓ))*Real.log α⁻¹ := by
    have hv := hh (D.region_open n) (D.region_bounded n) (D.vol_pos n) (D.delta_pos n)
      (G.grad n) (G.weak n) (ℓ := ℓ) zero_lt_one (by linarith) hM q
    have hfield : D.spiralField M n q = cutoffSpiral (smoothedIndicator (D.region n) D.mollifier (D.delta n)) M q := rfl
    simpa only [one_pow,mul_one,one_mul,f,hfield,DomainSequence.tileBoundaryFraction,b,
      DomainSequence.energyDensity,DomainSequence.totalEnergy,E,
      CutoffGradient.cost,ℓ,ρ,K,DomainSequence.vol,CoulombTilingCost.cost,div_mul_eq_mul_div] using hv (by simpa only [mul_one] using hint) α hp hlt
  have hK := U.constant_nonneg H
  have bound := finite_upper_at_half_le_one hint (show 0 ≤ K*(ρ^2/ℓ) by
    dsimp only [K]; positivity [show 0 < ℓ by linarith]) hu
  apply bound.trans_eq
  change scaleAverage f + K*(ρ*rateGrowth ρ q*(1/ℓ+b)+ρ*(1/ℓ+G.cost n)) +
    K*(ρ^2/ℓ) = scaleAverage f +
    (K*(ρ*rateGrowth ρ q)*(ℓ⁻¹+b)+K*ρ*(ℓ⁻¹+G.cost n)+(K*ρ^2)/ℓ)
  ring

/-- Quantitative tetrahedral comparison. The geometric coefficient covers
the four-face boundary volume and the Fisher cost of the outer width one. -/
theorem CoulombUpperLocalization.dilation_comparison {η : Mollifier} (U : CoulombUpperLocalization η)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (diff : SobolevDifferenceBounds)
    {J : ℝ} (hi : TileDilationIntegrable energy η J) :
    ∃ K₀ ≥ 2, ∀ K ≥ K₀, TileDilationComparison energy η K := by
  obtain ⟨a,ha,hh⟩ := U.open_upper H sob η
  obtain ⟨c,hc,area⟩ := tileCutoffAreaBound_of_sobolev sob diff η
  let C := U.constant H
  let A := 27744*a
  have hC : 0 ≤ C := U.constant_nonneg H
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let K₀ := max (max 2 (J+1)) (C*(1+A+c))
  refine ⟨K₀,(le_max_left 2 _).trans (le_max_left _ _),?_⟩
  intro K hK M hM q ℓ δ he hd hs ρ
  have h₂ : 2 ≤ K := ((le_max_left 2 _).trans (le_max_left _ _)).trans hK
  have hJ : J+1 ≤ K := ((le_max_right 2 _).trans (le_max_left _ _)).trans hK
  have hbig : C*(1+A+c) ≤ K := (le_max_right _ _).trans hK
  have hCK : C ≤ K := (by nlinarith only [hbig,mul_nonneg hC hA,mul_nonneg hC hc])
  have hAC : C*A ≤ K := by nlinarith only [hbig,hC,mul_nonneg hC hc]
  have hCc : C*c ≤ K := by nlinarith only [hbig,hC,mul_nonneg hC hA]
  have hδ : δ ≤ ℓ/2 := by nlinarith only [hs,mul_le_mul_of_nonneg_left h₂ hd.le]
  have hsJ : δ*J ≤ ℓ-δ := by nlinarith only [hs,mul_le_mul_of_nonneg_left hJ hd.le]
  let f := fun t => averagedTile energy η M q (t*(ℓ-δ)) (t*δ)
  have hint := hi M hM q (ℓ-δ) δ (by linarith) hd hsJ
  let b := ℓ+δ+1
  let w := a*b
  have hb : 0 < b := by dsimp [b]; positivity
  have hw : 0 < w := mul_pos ha hb
  have hr : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  filter_upwards [eventually_ge_atTop w] with L hL
  have hpos := hw.trans_le hL
  let V := regionVolume (tetrahedron L)
  have hv : 0 < V := tetrahedron_volume_pos hpos
  let B := thickening w (frontier (tetrahedron L))
  obtain ⟨g,hg,_,hgarea⟩ := area L 1 hpos zero_lt_one
  have hcost : (∫ x, ‖g x‖^2)/V ≤ c/L := by
    apply (div_le_iff₀ hv).2
    apply hgarea.trans_eq
    change c*V/(L*1) = c/L*V
    ring
  have hbdy : regionVolume B/V ≤ A*(b/L) := by
    apply (div_le_iff₀ hv).2
    apply (tetrahedron_boundary_volume hw hL).trans_eq
    dsimp only [V,A,w]
    rw [tetrahedron_volume hpos]
    field_simp [hpos.ne']
    ring
  have coef :
      C*(ρ*rateGrowth ρ q*(δ/ℓ+regionVolume B/V)+ρ*(1/(ℓ*δ)+(∫ x, ‖g x‖^2)/V)) ≤
        K*(ρ*rateGrowth ρ q*(δ/ℓ+b/L)+ρ*(1/(ℓ*δ)+1/L)) := by
    let D := ρ*rateGrowth ρ q
    have hD : 0 ≤ D := rhoGrowth_nonneg hr q
    have hbd := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbdy hD) hC
    have hcg := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcost hr) hC
    have h₁ := mul_le_mul_of_nonneg_right hCK (mul_nonneg hD (div_nonneg hd.le he.le))
    have h₂ := mul_le_mul_of_nonneg_right hAC (mul_nonneg hD (div_nonneg hb.le hpos.le))
    have h₃ := mul_le_mul_of_nonneg_right hCK (mul_nonneg hr (by positivity : 0 ≤ 1/(ℓ*δ)))
    have h₄ := mul_le_mul_of_nonneg_right hCc (mul_nonneg hr (by positivity : 0 ≤ 1/L))
    change C*(D*(δ/ℓ+regionVolume B/V)+ρ*(1/(ℓ*δ)+(∫ x, ‖g x‖^2)/V)) ≤
      K*(D*(δ/ℓ+b/L)+ρ*(1/(ℓ*δ)+1/L))
    ring_nf at hbd hcg h₁ h₂ h₃ h₄ ⊢
    linarith only [hbd,hcg,h₁,h₂,h₃,h₄]
  intro α hα hhalf
  let rhs := scaleAverageAt α f + K*(ρ*rateGrowth ρ q*(δ/ℓ+b/L)+ρ*(1/(ℓ*δ)+1/L)) +
    (K*(δ^3*ρ^2/ℓ))*Real.log α⁻¹
  have each (k : Position) (hk : ‖k‖ = ‖q‖) : tileEnergy energy η M L 1 k ≤ rhs := by
    have h := hh (tetrahedron_open L) (isBounded_closedBall.subset (tetrahedron_subset hpos)) hv
      zero_lt_one g hg hd hδ hM k
    have ef : (fun t => averagedTile energy η M k (t*(ℓ-δ)) (t*δ)) = f := by
      funext t; simp only [averagedTile,f,hk]
    have eg : rateGrowth ρ k = rateGrowth ρ q := by simp only [rateGrowth,hk]
    have hintk : IntegrableOn (fun t => averagedTile energy η M k (t*(ℓ-δ)) (t*δ)*scaleWeight t)
        scaleInterval := by
      simpa only [averagedTile,hk,f] using hint
    have raw := h hintk α hα hhalf
    change tileEnergy energy η M L 1 k ≤ scaleAverageAt α (fun t => averagedTile energy η M k (t*(ℓ-δ)) (t*δ)) +
      C*(ρ*rateGrowth ρ k*(δ/ℓ+regionVolume B/V)+ρ*(1/(ℓ*δ)+(∫ x, ‖g x‖^2)/V)) +
      (C*((δ^3/ℓ)*ρ^2))*Real.log α⁻¹ at raw
    rw [ef,show δ^3/ℓ*ρ^2=δ^3*ρ^2/ℓ by ring,eg] at raw
    have ec := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK (show 0 ≤ δ^3*ρ^2/ℓ by positivity))
      (Real.log_nonneg ((one_le_inv₀ hα).mpr (by linarith)))
    exact raw.trans (add_le_add (add_le_add (le_refl _) coef) ec)
  have result := direction_mono_add (f := tileEnergy energy η M L 1) (g := fun _ => rhs) (d := 0)
    (continuous_direction_integrable (coulomb_continuous_tile H sob η hpos zero_lt_one hM) q)
    (integrable_const rhs) (fun ω => by
      rw [add_zero]
      apply each
      simp [norm_smul,mem_sphere_zero_iff_norm.mp ω.property])
  simpa only [directionAverage_const,add_zero,averagedTile,rhs,f,b] using result

end TSGA.ManyBody
