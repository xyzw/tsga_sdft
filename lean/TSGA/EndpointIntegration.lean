import TSGA.EndpointFreezing

/-! # Summing the intermediate endpoint error and choosing the localization scale -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization SSW

private def lsdaScaleCost (D : Density) (S T : MatrixGradient) (p b ε : ℝ) : ℝ :=
  ε*(∫ x, massDensity D Phase.zero x)+(∫ x, kineticDensity S x)/ε+(∫ x, rootPower T p x)/ε^b

private theorem endpoint_majorant {D : Density} {S T : MatrixGradient} {p θ α C V ε : ℝ}
    (reg : DensityRegular D p θ S T) (hp : 0 < p) (he : 0 < ε) (hle : ε ≤ 1/2)
    (hC : 0 ≤ C) (hV : 0 ≤ V) :
    let b := endpointBulkExponent p θ α
    let extra := fun c => V*endpointTileCost D T p b ε C c
    let cost := lsdaScaleCost D S T p b ε
    Integrable extra ∧ (∀ c, 0 ≤ extra c) ∧ integratedScaleCost .minority D Phase.zero S T 0 p θ ε ≤ cost ∧
      (∫ c, extra c) ≤ (V*(1+tileMorreyCoefficient p C))*cost := by
  intro b extra cost
  let R := 3*ε⁻¹
  let B := tileMorreyCoefficient p C
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (ballVolume_pos zero_lt_one).le (Real.rpow_nonneg (by norm_num) _)) hC
  have hm := massDensity_integrable reg (phaseAdmissible_zero D hp (0 : MatrixGradient))
  have hu := rootPower_integrable hp reg.theta_Lp
  have mi := (ballAverage_integrable R hm).const_mul ε
  have ui := ((ballAverage_integrable R hu).const_mul B).div_const (ε^b)
  let mass := ε*(∫ x, massDensity D Phase.zero x)
  let kin := (∫ x, kineticDensity S x)/ε
  let bulk := (∫ x, rootPower T p x)/ε^b
  have hm₀ : 0 ≤ mass := mul_nonneg he.le (integral_nonneg (massDensity_nonneg D Phase.zero))
  have hk₀ : 0 ≤ kin := div_nonneg (integral_nonneg fun _ => sq_nonneg _) he.le
  have hu₀ : 0 ≤ bulk := div_nonneg (integral_nonneg (rootPower_nonneg T p)) (Real.rpow_nonneg he.le _)
  have base : cost = mass+kin+bulk := rfl
  refine ⟨(mi.add ui).const_mul V,fun c => mul_nonneg hV (add_nonneg
    (mul_nonneg he.le (ballAverage_nonnegative _ (massDensity_nonneg D Phase.zero) c))
    (div_nonneg (mul_nonneg hB (ballAverage_nonnegative _ (rootPower_nonneg T p) c)) (Real.rpow_nonneg he.le _))),?_,?_⟩
  · have hb : polarizedBulkExponent p θ ≤ b := by
      unfold polarizedBulkExponent b endpointBulkExponent
      exact sub_le_sub_right (max_le_max (le_max_left ..) le_rfl) _
    have bound : (∫ x, rootPower T p x)/ε^(polarizedBulkExponent p θ) ≤ (∫ x, rootPower T p x)/ε^b := div_le_div_of_nonneg_left (integral_nonneg (rootPower_nonneg T p))
      (Real.rpow_pos_of_pos he b) (Real.rpow_le_rpow_of_exponent_ge he (by linarith) hb)
    simpa [integratedScaleCost,BulkRegime.exponent,bulkDensity,phaseDensity,Phase.zero,Phase.hessianNorm,
      weightedRoot,Real.zero_rpow hp.ne',cost,lsdaScaleCost,mass,kin,massDensity] using add_le_add (le_refl (mass+kin)) bound
  · change (∫ c, V*(ε*ballAverage R (massDensity D Phase.zero) c+B*ballAverage R (rootPower T p) c/ε^b)) ≤ _
    rw [integral_const_mul,integral_add mi ui,integral_const_mul,integral_div,integral_const_mul,
      integral_ballAverage (by positivity) hm,integral_ballAverage (by positivity) hu,mul_div_assoc]
    change V*(mass+B*bulk) ≤ (V*(1+B))*cost
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hV
    rw [base]
    nlinarith only [hu₀,hk₀,mul_nonneg hB (add_nonneg hm₀ hk₀)]

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {η : Mollifier}

/-- A zero-wavevector modulus on the comparison matrices implies the LSDA
error at the interpolated bulk exponent for all spin densities. -/
theorem CoulombModelInputs.lsda_of_endpoint_tile_bound {p θ α J K : ℝ}
    (P : CoulombModelInputs μ ι η) (L : CoulombGasInputs η K)
    (hp : 3 < p) (hθ : 0 < θ) (hθ' : θ ≤ 1) (hα : 0 < α) (hpθ : 2 ≤ p*θ)
    (hJ : 0 ≤ J) (lip : PowerEndpointTileBound η θ α J) :
    ∃ C > 0, LSDAEstimate (referenceEnergies energy η) (fun _ => True) p θ (endpointBulkExponent p θ α) C := by
  have hp₀ : 0 < p := by linarith
  obtain ⟨C,hC,M⟩ := P.matrixMorrey p hp
  obtain ⟨V,hV,vec⟩ := P.vectorMorrey p hp
  obtain ⟨a,ha,area⟩ := tileCutoffAreaBound_of_sobolev P.difference P.directional.toDifferenceBounds η
  obtain ⟨A,hA,small⟩ := P.endpoint_small_tiles L hp hθ hθ' hα hpθ M vec hC hV ha area hJ lip
  let b := endpointBulkExponent p θ α
  let W := 8*smallGasConstant J K
  have hW : 0 ≤ W := by dsimp [W,smallGasConstant]; positivity [zero_le_one.trans L.rate.one_le]
  obtain ⟨B,hB,τ,hτ,allCenters⟩ := P.integrate_balls_with_error L .minority hp hθ hpθ M hC ha area hA
    (fun D T ε c => W*endpointTileCost D T p b ε C c) (fun D _ S T _ ε => lsdaScaleCost D S T p b ε)
    (V := W*(1+tileMorreyCoefficient p C)) (allow := fun φ G => φ=Phase.zero ∧ G=0) (by
      intro D φ S T G ε reg phase hr allowed he hle
      obtain ⟨rfl,rfl⟩ := allowed
      exact endpoint_majorant reg hp₀ he hle hC hW) small
  obtain ⟨A₀,hA₀,rough⟩ := L.aPriori P.fock.oneBody P.phaseProduct P.difference
  let Z₀ := max (2*A₀) B
  have hZ : 0 < Z₀ := (zero_lt_one.trans_le hB).trans_le (le_max_right ..)
  obtain ⟨C',hc,scale⟩ := extend_small_scale hZ hτ b 0
  refine ⟨C',hc,?_⟩
  intro D S T _ reg ε he
  let F := referenceEnergies energy η
  have phase := phaseAdmissible_zero D hp₀ (0 : MatrixGradient)
  have hr : RegimeHyp .minority 0 D 0 p := ae_of_all _ fun x => by simpa using D.positive x
  obtain ⟨hi,hrough⟩ := rough.rough_bound hA₀ hp hθ reg phase
  have eq : localEnergy F D Phase.zero = fun x => F.ueg (D.matrix x) := funext fun x => F.zero_mode _ (D.positive x)
  have mass : 0 ≤ ∫ x, massDensity D Phase.zero x := integral_nonneg (massDensity_nonneg D Phase.zero)
  have kin : 0 ≤ ∫ x, kineticDensity S x := integral_nonneg fun _ => sq_nonneg _
  have bulk : 0 ≤ ∫ x, rootPower T p x := integral_nonneg (rootPower_nonneg T p)
  have h := scale mass kin bulk (le_refl 0)
    (hrough.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (add_nonneg mass kin))) (by
      intro δ hδ hδτ
      have cmp := allCenters D Phase.zero S T 0 reg phase hr ⟨rfl,rfl⟩ δ hδ hδτ
      have nn : 0 ≤ lsdaScaleCost D S T p b δ := add_nonneg
        (add_nonneg (mul_nonneg hδ.le mass) (div_nonneg kin hδ.le)) (div_nonneg bulk (Real.rpow_nonneg hδ.le _))
      simpa only [lsdaScaleCost,zero_div,add_zero] using cmp.trans (mul_le_mul_of_nonneg_right (le_max_right (2*A₀) B) nn)) ε he
  refine ⟨eq ▸ hi,?_⟩
  change |rotatedEnergy F D Phase.zero - ∫ x, localEnergy F D Phase.zero x| ≤ _ at h
  rw [eq] at h
  simpa [F,rotatedEnergy,Phase.zero,lsdaError,kineticDensity,rootPower,massDensity,b] using h

end TSGA.ManyBody
