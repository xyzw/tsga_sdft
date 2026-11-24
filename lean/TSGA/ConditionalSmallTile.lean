import TSGA.RegularSmallTile

/-! # Zero-phase freezing under the conjectured endpoint Lipschitz bound -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW PhaseLocalization Metric Set
open scoped ComplexOrder

private theorem zero_gas_at_point {η : Mollifier} {N : Density} {R p θ J : ℝ} {c : Position}
    {s : SmallBallScale N R c} (m : SmallBallMatrices s)
    (hθ : 0 < θ) (hle : θ ≤ 1) (hp : 0 < p) (hpθ : 2 ≤ p*θ) (hJ : 0 ≤ J)
    (lip : ∀ A B : SpinMatrix, A.PosSemidef → B.PosSemidef →
      let r := max A.trace.re B.trace.re
      |sswEnergy energy η A 0-sswEnergy energy η B 0| ≤ J*(r^(1/3:ℝ)+r^(2/3:ℝ))*hilbertSchmidt (A-B))
    (small : s.omega θ ≤ s.r^θ) {F : SpinMatrix} (hF : F.PosSemidef) (sel : F=m.low ∨ F=m.high)
    {x : Position} (hx : x ∈ closedBall c R) :
    |sswEnergy energy η F 0-sswEnergy energy η (N.matrix x) 0| ≤
      (6*J/θ)*smallGasBulk s.r (s.omega θ) θ (BulkRegime.minority.holderPower p θ) := by
  let t := max F.trace.re (N.charge x)
  let r := s.r
  let u := s.omega θ/r^θ
  let a := BulkRegime.minority.holderPower p θ
  have hr : 0 ≤ r := s.r_nonneg
  have ht : 0 ≤ t := (N.charge_nonneg x).trans (le_max_right ..)
  have cap : t ≤ 2*r := max_le (m.trace_range sel).2 ((s.cap x hx).trans (by linarith))
  have hu : 0 ≤ u := div_nonneg (s.omega_nonneg _ hθ) (Real.rpow_nonneg hr _)
  have hu' : u ≤ 1 := div_le_one_of_le₀ small (Real.rpow_nonneg hr _)
  have ha : 0 ≤ a := by
    apply le_min zero_le_one
    exact div_nonneg hp.le (by linarith only [hpθ,mul_comm p θ])
  have mono : u ≤ u^a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' hu hu' ha (show a ≤ 1 from min_le_left ..)
  have coeff : 0 ≤ 6*J/θ := by positivity
  have pos : 0 ≤ (r^(4/3:ℝ)+r^(5/3:ℝ)) := add_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)
  have h := lip F (N.matrix x) hF (N.positive x)
  change _ ≤ J*(t^(1/3:ℝ)+t^(2/3:ℝ))*hilbertSchmidt (F-N.matrix x) at h
  have factor (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1) : t^b ≤ 2*r^b := by
    have H := Real.rpow_le_rpow ht cap hb
    rw [Real.mul_rpow (by norm_num) hr] at H
    exact H.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) hb') (Real.rpow_nonneg hr _))
  have growth : t^(1/3:ℝ)+t^(2/3:ℝ) ≤ 2*(r^(1/3:ℝ)+r^(2/3:ℝ)) := by
    linarith only [factor (1/3) (by norm_num) (by norm_num),factor (2/3) (by norm_num) (by norm_num)]
  have d := (m.matrix_dist sel x hx).trans (mul_le_mul_of_nonneg_left (s.omega_one_le θ hθ hle) (by norm_num))
  change _ ≤ (6*J/θ)*((r^(4/3:ℝ)+r^(5/3:ℝ))*u^a)
  rcases hr.eq_or_lt with hz | hr'
  · have dz : hilbertSchmidt (F-N.matrix x) ≤ 0 := by
      linarith only [m.matrix_dist sel x hx,s.small,show s.r=0 from hz.symm]
    exact (h.trans (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hJ (add_nonneg (Real.rpow_nonneg ht _) (Real.rpow_nonneg ht _))) dz)).trans
      (mul_nonneg coeff (mul_nonneg pos (Real.rpow_nonneg hu _)))
  have identity (b : ℝ) : r^b*r^(1-θ)*s.omega θ = r^(b+1)*u := by
    rw [Real.rpow_sub hr',Real.rpow_one,Real.rpow_add_one hr'.ne']
    dsimp only [u]
    ring
  calc
    _ ≤ (J*(2*(r^(1/3:ℝ)+r^(2/3:ℝ))))*(3*((1/θ*r^(1-θ))*s.omega θ)) :=
      h.trans (mul_le_mul (mul_le_mul_of_nonneg_left growth hJ) d (Real.sqrt_nonneg _)
        (by positivity))
    _ = (6*J/θ)*(r^(1/3:ℝ)*r^(1-θ)*s.omega θ + r^(2/3:ℝ)*r^(1-θ)*s.omega θ) := by ring
    _ = (6*J/θ)*((r^(4/3:ℝ)+r^(5/3:ℝ))*u) := by
      rw [identity,identity,show (1/3:ℝ)+1=4/3 by norm_num,show (2/3:ℝ)+1=5/3 by norm_num]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left mono pos) coeff

private theorem zero_gas_comparison {η : Mollifier} {K p θ J : ℝ} (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (hp : 0 < p)
    (hθ : 0 < θ) (hle : θ ≤ 1) (hpθ : 2 ≤ p*θ) (hJ : 0 < J)
    (lip : ∀ A B : SpinMatrix, A.PosSemidef → B.PosSemidef →
      let r := max A.trace.re B.trace.re
      |sswEnergy energy η A 0-sswEnergy energy η B 0| ≤ J*(r^(1/3:ℝ)+r^(2/3:ℝ))*hilbertSchmidt (A-B)) :
    PhaseGasComparison η .minority p θ 0 K (6*J/θ) Phase.zero := by
  intro ε he he' D N G c s m e cn cp phase regime small F hF sel P support σ
  let b := smallGasBulk s.r (s.omega θ) θ (BulkRegime.minority.holderPower p θ)
  let V := 6*J/θ
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hb : 0 ≤ b := by
    dsimp only [b,smallGasBulk]
    positivity [s.r_nonneg,s.omega_nonneg θ hθ]
  have hm := bounded_cutoff_integral P c (f := fun _ => V*b) aestronglyMeasurable_const
    (mul_nonneg hV hb) (ae_of_all _ fun _ _ => (abs_of_nonneg (mul_nonneg hV hb)).le)
  refine ⟨fun _ => V*b,L.local_cutoff_integrable H sob e cn phase P c σ _ (by positivity) support,hm.1,?_,?_⟩
  · filter_upwards [e] with x ex
    intro hcut
    change |sswEnergy energy η F 0-sswEnergy energy η (D.matrix x) 0| ≤ V*b
    rw [← ex]
    exact zero_gas_at_point m hθ hle hp hpθ hJ.le lip small hF sel (support x hcut)
  · obtain ⟨_,_,hosc,_⟩ := tilePhaseOscillation_attained phase c (inv_pos.mpr he)
    have v0 : tilePhaseOscillation Phase.zero c ε⁻¹ = 0 := by simpa [Phase.zero] using hosc
    have hK := L.rate.one_le
    have lhs : V ≤ smallGasConstant V K := by unfold smallGasConstant; linarith
    refine hm.2.trans ?_
    change V*b ≤ smallGasConstant V K*(b+smallBallPhaseCost s.r (s.omega (1/p)/s.r^(1/p)) ε
      (tilePhaseOscillation Phase.zero c ε⁻¹) 0)
    rw [v0]
    simpa only [smallBallPhaseCost,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,zero_div,add_zero]
      using (mul_le_mul_of_nonneg_right lhs hb)

/-- A linear zero-wavevector endpoint modulus gives the minority-case
bulk exponent for every spin density on a small ball, including vacuum. -/
theorem actual_small_oscillation_of_zero_phase_lipschitz {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι]
    {K a p θ Cmat Cvec g : ℝ} {η : Mollifier} (L : CoulombGasInputs η K) (F : IslandFockInputs μ)
    (support : Function.support η.kernel ⊆ closedBall 0 (1/100))
    (laws : TetraPoissonLaws μ ι η support g) (hg : 0 ≤ g)
    (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct) (prod : WeakScalarMatrixProduct)
    (borel : LevyLiebBorel) (comp : SobolevLipschitzComposition) (W : WindowSobolevRules)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (localComp : ∀ (c : Position) (R : ℝ), 0 < R → SobolevCompositionOn (closedBall c R))
    (ha : 0 ≤ a) (area : TileCutoffAreaBound η a) 
    (M : MatrixSobolevMorrey p Cmat) (V : VectorMorreyOnBalls p Cvec)
    (hM : 0 ≤ Cmat) (hV : 0 ≤ Cvec) (hp : 3 < p) (hθ : 0 < θ) (hθ' : θ ≤ 1)
    (hpθ : 2 ≤ p*θ) (J : ℝ) (hJ : 0 < J)
    (lip : ∀ A B : SpinMatrix, A.PosSemidef → B.PosSemidef →
      let r := max A.trace.re B.trace.re
      |sswEnergy energy η A 0-sswEnergy energy η B 0| ≤ J*(r^(1/3:ℝ)+r^(2/3:ℝ))*hilbertSchmidt (A-B)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {D : Density} {S T : MatrixGradient},
      DensityRegular D p θ S T →
      ∀ {ε : ℝ} (he : 0 < ε) (hle : ε ≤ 1/2), ε*(K+1) ≤ 1 →
      ∀ (side : CutoffSide) (P : TileProfile),
      P.cutoff = (actualTiles O frames η side he (by linarith)).cutoffProfile →
      ∀ c, SmallPowerOscillation D θ (θ/64) (3*ε⁻¹) c →
      let tiles := actualTiles O frames η side he (by linarith)
      let gas := referenceEnergies energy η
      let σ := tileSign side
      σ*(tiles.energy gas D Phase.zero c - cutoffAverage P.cutoff (localEnergy gas D Phase.zero) c) ≤
        A*smallBallErrorDensity .minority D Phase.zero S T 0 p θ ε Cmat c := by
  have hp₀ : 0 < p := by linarith
  have law : PhaseGasComparison η .minority p θ 0 K (6*J/θ) Phase.zero := zero_gas_comparison L F.oneBody sob hp₀ hθ hθ' hpθ hJ lip
  obtain ⟨A,hA,estimate⟩ := actual_small_oscillation_for_phases (ν := 0) L F support laws hg leibniz chain prod
    borel comp W O frames sob quant localComp ha area .minority M V hM hV hp hθ hθ' hpθ
    (by intro h; contradiction) (fun φ => φ=Phase.zero) (show 0<6*J/θ by positivity)
    (fun φ eq => eq ▸ law)
  refine ⟨A,hA,?_⟩
  intro D S T reg ε he hle adm side P profile c small
  have minor : RegimeHyp .minority 0 D 0 p := ae_of_all _ fun x => by
    simpa only [zero_mul,Complex.ofReal_zero,zero_smul,sub_zero] using D.positive x
  exact (estimate reg (phaseAdmissible_zero D hp₀ 0) minor rfl he hle adm side P profile c small).2

end TSGA.ManyBody
