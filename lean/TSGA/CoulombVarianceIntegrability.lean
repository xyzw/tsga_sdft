import TSGA.CoulombUpperTrialAssembly
import TSGA.CoulombLatticeShell

/-! # Integrability of the physical direct error over frames and dilations -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW Set Metric

theorem measurable_shift_average {P : Type*} [MeasurableSpace P]
    {b : P → ℝ} (hb : Measurable b) {F : P × Position → ℝ} (hF : Measurable F) :
    Measurable (fun p => ∫ τ, F (p,τ) ∂latticeShiftMeasure (b p)) := by
  classical
  let S := {z : P × Position | ∀ i : Fin 3, |z.2 i| < b z.1/2}
  have hm : MeasurableSet S := by
    change MeasurableSet {z : P × Position | ∀ i : Fin 3, |z.2 i| < b z.1/2}
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_lt _ ((hb.comp measurable_fst).div_const 2)
    exact continuous_abs.measurable.comp ((EuclideanSpace.proj i).continuous.measurable.comp measurable_snd)
  have h (p : P) : (∫ τ, F (p,τ) ∂latticeShiftMeasure (b p)) =
      ((ENNReal.ofReal ((b p)^3))⁻¹).toReal * ∫ τ, S.indicator F (p,τ) := by
    rw [latticeShiftMeasure,integral_smul_measure,smul_eq_mul]
    congr 1
    rw [← integral_indicator (latticeCube_measurable _ _)]
    apply integral_congr_ae (ae_of_all _ fun τ => ?_)
    have mem : (p,τ) ∈ S ↔ τ ∈ latticeCube (b p) 0 := by simp [S,latticeCube]
    by_cases hc : τ ∈ latticeCube (b p) 0 <;> simp [Set.indicator,hc,mem]
  simp_rw [h]
  exact ((((hb.pow_const 3).ennreal_ofReal).inv).ennreal_toReal).mul
    ((hF.indicator hm).stronglyMeasurable.integral_prod_right'.measurable)

private theorem modulated_hartree_family {P : Type*} [MeasurableSpace P]
    (g : P × Position → ℝ) (hg : Measurable g) (hbound : ∀ p, |g p| ≤ 2)
    {charge : Position → ℝ} (hc : Measurable charge)
    (hi : Integrable (directKernel charge charge) pairVolume) :
    let h (p : P) := hartree (fun x => g (p,x)*charge x)
    Measurable h ∧ ∀ p, ‖h p‖ ≤ 2*(∫ z, |directKernel charge charge z| ∂pairVolume) := by
  intro h
  let k := fun z : P × PairSpace => (g (z.1,z.2.1)*g (z.1,z.2.2))*directKernel charge charge z.2
  have hm : Measurable k := by unfold k directKernel; fun_prop
  have eqn (p) (z : PairSpace) :
      directKernel (fun x => g (p,x)*charge x) (fun x => g (p,x)*charge x) z = k (p,z) := by
    unfold k directKernel
    ring
  have hb (p) (z : PairSpace) : ‖k (p,z)‖ ≤ 4*|directKernel charge charge z| := by
    unfold k
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact (mul_le_mul (hbound _) (hbound _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hj := hi.abs.const_mul 4
  have he (p) : h p = (∫ z, k (p,z) ∂pairVolume)/2 := by
    have hii : Integrable (fun z => k (p,z)) pairVolume :=
      hj.mono' (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (ae_of_all _ (hb p))
    change hartree _ = _
    have fun_eq := funext (eqn p)
    rw [hartree_eq_pair _ (fun_eq.symm ▸ hii),fun_eq]
  rw [show h = _ from funext he]
  refine ⟨(hm.stronglyMeasurable.integral_prod_right' (ν := pairVolume)).measurable.div_const 2,fun p => ?_⟩
  have H := norm_integral_le_of_norm_le hj (ae_of_all _ (hb p))
  rw [integral_const_mul] at H
  rw [norm_div,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

/-- A bounded charge with finite absolute direct energy provides an integrable
majorant for both the spherical average and the weighted dilation average. -/
theorem lattice_variance_integrable (O : TileOrientationLaw)
    (action : Measurable (fun z : O.Frames × Position => O.frame z.1 z.2))
    {η : Mollifier} (hk : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {ℓ δ : ℝ} (hδ : 0 < δ) (hsc : δ ≤ ℓ/2) {charge : Position → ℝ}
    (hc : Measurable charge) (hi : Integrable (directKernel charge charge) pairVolume) :
    (∀ t ∈ scaleInterval, Integrable (fun u => ∫ τ, hartree (fun x =>
      (latticeTotalWindow (t*ℓ) (t*δ) η (O.frame u x-τ)-1)*charge x)
      ∂latticeShiftMeasure (t*ℓ)) O.law) ∧
    IntegrableOn (fun t => latticeVariance O η charge ℓ δ t * scaleWeight t) scaleInterval := by
  let s := δ/ℓ
  have he : 0 < ℓ := by linarith
  have hs : 0 < s := div_pos hδ he
  have hu : s ≤ 1/2 := (div_le_iff₀ he).mpr (by linarith)
  let P := (ℝ × O.Frames) × Position
  let g := fun z : P × Position => latticeTotalWindow 1 s η
    ((z.1.1.1*ℓ)⁻¹ • (O.frame z.1.1.2 z.2-z.1.2)) - 1
  have gm : Measurable g := by
    apply (latticeTotalWindow_measurable 1 hs η).comp _ |>.sub measurable_const
    exact ((measurable_fst.comp (measurable_fst.comp measurable_fst)).mul_const ℓ).inv.smul
      ((action.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)).sub
        (measurable_snd.comp measurable_fst))
  have gb (p) : |g p| ≤ 2 := by
    have h := latticeTotalWindow_bounds hs hu hk ((p.1.1.1*ℓ)⁻¹ • (O.frame p.1.1.2 p.2-p.1.2))
    exact abs_le.mpr ⟨by dsimp only [g]; linarith [h.1],by dsimp only [g]; linarith [h.2]⟩
  let C := 2*(∫ z, |directKernel charge charge z| ∂pairVolume)
  let H := fun p : P => hartree (fun x => g (p,x)*charge x)
  obtain ⟨Hm,Hb⟩ := modulated_hartree_family g gm gb hc hi
  let F := fun z : ℝ × O.Frames => ∫ τ, H (z,τ) ∂latticeShiftMeasure (z.1*ℓ)
  have Fm : Measurable F := measurable_shift_average (measurable_fst.mul_const ℓ) Hm
  have hb (t : ℝ) (ht : t ∈ scaleInterval) : 0 < t := by linarith [ht.1]
  have bound (t) (ht : t ∈ scaleInterval) (u) : ‖F (t,u)‖ ≤ C := by
    have : IsProbabilityMeasure (latticeShiftMeasure (t*ℓ)) := latticeShiftMeasure_probability (mul_pos (hb t ht) he)
    simpa [F,C] using norm_integral_le_of_norm_le_const (μ := latticeShiftMeasure (t*ℓ))
      (ae_of_all _ (fun τ => Hb ((t,u),τ)))
  have Fn (t u τ) (ht : t ∈ scaleInterval) :
      hartree (fun x => (latticeTotalWindow (t*ℓ) (t*δ) η (O.frame u x-τ)-1)*charge x) = H ((t,u),τ) := by
    unfold H
    apply congrArg hartree
    funext x
    apply congrArg (fun a : ℝ => a * charge x)
    have h := lattice_fluctuation_dilate (mul_pos (hb t ht) he) 1 s η ((t*ℓ)⁻¹ • (O.frame u x-τ))
    simpa only [g,latticeTotalWindow,mul_one,show (t*ℓ)*s = t*δ by dsimp [s]; field_simp,
      smul_inv_smul₀ (mul_pos (hb t ht) he).ne'] using h
  constructor
  · intro t ht
    simp_rw [Fn _ _ _ ht]
    exact (integrable_const C).mono' (Fm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (ae_of_all _ (bound t ht))
  · let f (t : ℝ) := ∫ u, F (t,u) ∂O.law
    have fm : Measurable f := Fm.stronglyMeasurable.integral_prod_right'.measurable
    have b (t) (ht : t ∈ scaleInterval) : ‖f t‖ ≤ C := by
      simpa [f] using norm_integral_le_of_norm_le_const (μ := O.law) (ae_of_all _ (bound t ht))
    have eqn (t) (ht : t ∈ scaleInterval) : latticeVariance O η charge ℓ δ t = f t := by
      unfold latticeVariance
      simp_rw [Fn _ _ _ ht]
      rfl
    have wm : Measurable scaleWeight := by unfold scaleWeight; fun_prop
    have fint : IntegrableOn (fun t => f t * scaleWeight t) scaleInterval := by
      apply (scaleWeight_integrableOn.const_mul C).mono' (fm.mul wm).aestronglyMeasurable
      filter_upwards [ae_restrict_mem (show MeasurableSet scaleInterval from measurableSet_Icc)] with t ht
      have wpos : 0 ≤ scaleWeight t := inv_nonneg.mpr (pow_nonneg (by linarith [hb t ht]) 4)
      change ‖f t * scaleWeight t‖ ≤ C * scaleWeight t
      rw [norm_mul,Real.norm_of_nonneg wpos]
      exact mul_le_mul_of_nonneg_right (b t ht) wpos
    apply fint.congr
    filter_upwards [ae_restrict_mem (show MeasurableSet scaleInterval from measurableSet_Icc)] with t ht
    rw [eqn t ht]

/-- The variance also applies to charges given only as almost-everywhere
measurable representatives. Every modulated direct integral respects
almost-everywhere equality. -/
theorem lattice_variance_integrable_ae (O : TileOrientationLaw)
    (action : Measurable (fun z : O.Frames × Position => O.frame z.1 z.2))
    {η : Mollifier} (hk : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {ℓ δ : ℝ} (hδ : 0 < δ) (hsc : δ ≤ ℓ/2) {charge : Position → ℝ}
    (hc : AEMeasurable charge volume) (hi : Integrable (directKernel charge charge) pairVolume) :
    (∀ t ∈ scaleInterval, Integrable (fun u => ∫ τ, hartree (fun x =>
      (latticeTotalWindow (t*ℓ) (t*δ) η (O.frame u x-τ)-1)*charge x)
      ∂latticeShiftMeasure (t*ℓ)) O.law) ∧
    IntegrableOn (fun t => latticeVariance O η charge ℓ δ t * scaleWeight t) scaleInterval := by
  let r := hc.mk charge
  have eqr : charge =ᵐ[volume] r := hc.ae_eq_mk
  have eqK : directKernel charge charge =ᵐ[pairVolume] directKernel r r := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae eqr,
      (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae eqr] with z hx hy
    simp [directKernel,show charge z.1 = r z.1 from hx,show charge z.2 = r z.2 from hy]
  have eqH (w : Position → ℝ) : hartree (fun x => w x*charge x) = hartree (fun x => w x*r x) :=
    hartree_congr (eqr.mono fun x hx => congrArg (fun q : ℝ => w x*q) hx)
  obtain ⟨fr,sc⟩ := lattice_variance_integrable O action hk hδ hsc hc.measurable_mk (hi.congr eqK)
  unfold latticeVariance at *
  simp_rw [eqH]
  exact ⟨fr,sc⟩

end TSGA.ManyBody
