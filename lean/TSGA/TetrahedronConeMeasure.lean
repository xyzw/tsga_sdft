import TSGA.CoulombShellTransport

/-! # Cone measure of the reference tetrahedron

Intersecting any measurable angular sector with the tetrahedron of radius r
multiplies its volume by r³. On each sector the cube of the homothetic radius
therefore has constant density. -/

noncomputable section
namespace TSGA.SSW

open MeasureTheory Set Metric Skeleton
open scoped Pointwise ENNReal

private def conePoint (x : Position) := (tetrahedronRadius x)⁻¹ • x

private theorem measurable_conePoint : Measurable conePoint :=
  continuous_tetrahedronRadius.measurable.inv.smul measurable_id

private theorem radius_nonneg (x : Position) : 0 ≤ tetrahedronRadius x := by
  have h₁ : 4*(|x 2|-x 1) ≤ tetrahedronRadius x := le_max_left _ _
  have h₂ : 8*(x 1-x 0) ≤ tetrahedronRadius x := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : 8*x 0 ≤ tetrahedronRadius x := (le_max_right _ _).trans (le_max_right _ _)
  linarith [abs_nonneg (x 2)]

private theorem conePoint_smul {r : ℝ} (hr : 0 < r) (x : Position) :
    conePoint (r • x) = conePoint x := by
  simp [conePoint,tetrahedronRadius_smul hr.le,smul_smul,hr.ne',mul_comm]

private theorem conePoint_bound (x : Position) : ‖conePoint x‖ ≤ 2 := by
  by_cases h : tetrahedronRadius x = 0
  · simp [conePoint,h]
  have hr := lt_of_le_of_ne (radius_nonneg x) (Ne.symm h)
  have hr' : tetrahedronRadius (conePoint x) = 1 := by
    rw [conePoint,tetrahedronRadius_smul (inv_nonneg.mpr hr.le),inv_mul_cancel₀ h]
  apply le_of_forall_pos_le_add
  intro ε hε
  have he : 0 < 1+ε/2 := by linarith
  have hx := tetrahedron_subset he (tetrahedronRadius_lt.mp (show tetrahedronRadius (conePoint x)<1+ε/2 by rw [hr']; linarith))
  have hh := mem_closedBall_zero_iff.mp hx
  linarith

private def coneSector (r : ℝ) (A : Set Position) := conePoint ⁻¹' A ∩ tetrahedron r

private theorem measurableSet_coneSector (r : ℝ) {A : Set Position} (hA : MeasurableSet A) :
    MeasurableSet (coneSector r A) := (hA.preimage measurable_conePoint).inter (tetrahedron_open r).measurableSet

private theorem coneSector_mono {a b : ℝ} (h : a ≤ b) (A : Set Position) :
    coneSector a A ⊆ coneSector b A := inter_subset_inter_right _ (tetrahedron_mono h)

private theorem volume_coneSector {r : ℝ} (hr : 0 < r) (A : Set Position) :
    volume (coneSector r A) = ENNReal.ofReal (r^3)*volume (coneSector 1 A) := by
  have he : coneSector r A = r • coneSector 1 A := by
    ext x
    constructor
    · rintro ⟨hx,hrx⟩
      refine ⟨r⁻¹ • x,⟨?_,?_⟩,smul_inv_smul₀ hr.ne' x⟩
      · change conePoint (r⁻¹ • x) ∈ A
        rwa [conePoint_smul (inv_pos.mpr hr)]
      · apply tetrahedronRadius_lt.mp
        rw [tetrahedronRadius_smul (inv_nonneg.mpr hr.le),← div_eq_inv_mul,div_lt_one hr]
        exact tetrahedronRadius_lt.mpr hrx
    · rintro ⟨y,⟨hy,hry⟩,rfl⟩
      refine ⟨?_,tetrahedronRadius_lt.mp ?_⟩
      · change conePoint (r • y) ∈ A
        rwa [conePoint_smul hr]
      · rw [tetrahedronRadius_smul hr.le]
        simpa using mul_lt_mul_of_pos_left (tetrahedronRadius_lt.mpr hry) hr
  rw [he,Measure.addHaar_smul_of_nonneg _ hr.le]
  simp [finrank_euclideanSpace]

private def cubeUniform : Measure ℝ := volume.restrict (Ico 0 1)

private instance : IsProbabilityMeasure cubeUniform :=
  ⟨by simp [cubeUniform, Real.volume_Ico]⟩

private def angleVolume : Measure Position := (volume.restrict (tetrahedron 1)).map conePoint

private theorem angleVolume_apply {A : Set Position} (hA : MeasurableSet A) :
    angleVolume A = volume (coneSector 1 A) := by
  rw [angleVolume,Measure.map_apply measurable_conePoint hA,
    Measure.restrict_apply (hA.preimage measurable_conePoint)]
  rfl

private theorem angleVolume_univ : angleVolume univ = volume (tetrahedron 1) := by
  simp [angleVolume,Measure.map_apply measurable_conePoint]

private theorem unitVolume_pos : 0 < volume (tetrahedron 1) :=
  (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos (by norm_num : (0:ℝ)<1))).1

private theorem unitVolume_finite : volume (tetrahedron 1) ≠ ∞ :=
  (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos (by norm_num : (0:ℝ)<1))).2.ne

private instance : IsFiniteMeasure angleVolume := ⟨by rw [angleVolume_univ]; exact unitVolume_finite.lt_top⟩

private def unitSpans : cubeUniform.FiniteSpanningSetsIn (range Iio) where
  set n := Iio (n : ℝ)
  set_mem _ := mem_range_self _
  finite _ := measure_lt_top _ _
  spanning := iUnion_eq_univ_iff.mpr fun x => exists_nat_gt x

private def shellCoords (s : ℝ) (x : Position) : ℝ × Position :=
  ((tetrahedronRadius x^3-(1-s)^3) / shellFraction s, conePoint x)

private theorem measurable_shellCoords (s : ℝ) : Measurable (shellCoords s) :=
  (((continuous_tetrahedronRadius.measurable.pow_const 3).sub_const _).div_const _).prodMk measurable_conePoint

private def clip (t : ℝ) := max 0 (min 1 t)

private theorem clip_mem (t : ℝ) : clip t ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

private theorem cubeUniform_Iio (t : ℝ) : cubeUniform (Iio t) = ENNReal.ofReal (clip t) := by
  rw [cubeUniform, Measure.restrict_apply measurableSet_Iio, inter_comm, Ico_inter_Iio,Real.volume_Ico,sub_zero]
  by_cases h : 0 ≤ min 1 t
  · simp [clip,max_eq_right h]
  · simp [clip,max_eq_left (le_of_not_ge h),ENNReal.ofReal_eq_zero.mpr (le_of_not_ge h)]

private theorem shellQuantile_cube {s v : ℝ} (_hs : 0 < s) (hu : s < 1) (hv : v ∈ Icc (0:ℝ) 1) :
    shellQuantile s v ^ 3 = (1-s)^3+shellFraction s*v := by
  unfold shellQuantile shellFraction
  have h : 0 ≤ (1-v)*(1-s)^3+v := add_nonneg (mul_nonneg (sub_nonneg.mpr hv.2) (pow_nonneg (sub_pos.mpr hu).le 3)) hv.1
  have hpow := Real.rpow_inv_natCast_pow h (by decide : 3 ≠ 0)
  norm_num only [Nat.cast_ofNat] at hpow
  rw [hpow]
  ring

private theorem lt_clip_iff {v : ℝ} (hv : v ∈ Ico (0:ℝ) 1) (t : ℝ) : v < clip t ↔ v < t := by
  simp [clip,lt_max_iff,lt_min_iff,not_lt.mpr hv.1,hv.2]

private theorem shellCoords_rectangle {s : ℝ} (hs : 0 < s) (hu : s < 1)
    (t : ℝ) (A : Set Position) :
    shellCoords s ⁻¹' (Iio t ×ˢ A) ∩ (tetrahedron 1 \ tetrahedron (1-s)) =
       coneSector (shellQuantile s (clip t)) A \ coneSector (1-s) A := by
  let a := 1-s
  let b := shellFraction s
  let c := shellQuantile s (clip t)
  have ha : 0 < a := sub_pos.mpr hu
  have hb : 0 < b := shellFraction_pos hs hu.le
  have hc := shellQuantile_bounds (show s ∈ Icc (0:ℝ) 1 from ⟨hs.le,hu.le⟩) (clip_mem t)
  have hc' : c^3 = a^3+b*clip t := shellQuantile_cube hs hu (clip_mem t)
  ext x
  let r := tetrahedronRadius x
  have hr := radius_nonneg x
  have hp : r < c ↔ r^3 < c^3 := (pow_lt_pow_iff_left₀ hr (ha.le.trans hc.1) (by decide : 3 ≠ 0)).symm
  have hv (hl : a ≤ r) (hh : r < 1) : (r^3-a^3)/b ∈ Ico (0:ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha.le hl 3)) hb.le, (div_lt_one hb).mpr ?_⟩
    have h := pow_lt_pow_left₀ hh hr (by decide : 3 ≠ 0)
    change r^3-(1-s)^3 < 1-(1-s)^3
    linarith [show r^3 < 1 from by simpa using h]
  change (((r^3-a^3)/b < t ∧ conePoint x ∈ A) ∧ x ∈ tetrahedron 1 ∧ x ∉ tetrahedron a) ↔
    (conePoint x ∈ A ∧ x ∈ tetrahedron c) ∧ ¬(conePoint x ∈ A ∧ x ∈ tetrahedron a)
  simp only [← tetrahedronRadius_lt,not_lt]
  change (((r^3-a^3)/b < t ∧ _) ∧ r < 1 ∧ a ≤ r) ↔ (_ ∧ r < c) ∧ ¬(_ ∧ r < a)
  constructor
  · rintro ⟨⟨ht,hA⟩,h1,ha⟩
    have h := (div_lt_iff₀ hb).mp ((lt_clip_iff (hv ha h1) t).mpr ht)
    exact ⟨⟨hA,hp.mpr (by rw [hc']; linarith)⟩, fun hh => (not_lt.mpr ha) hh.2⟩
  · rintro ⟨⟨hA,hc1⟩,h0⟩
    have h1 := hc1.trans_le hc.2
    have ha := le_of_not_gt (fun h => h0 ⟨hA,h⟩)
    have h := hp.mp hc1
    rw [hc'] at h
    exact ⟨⟨(lt_clip_iff (hv ha h1) t).mp ((div_lt_iff₀ hb).mpr (by linarith)),hA⟩,h1,ha⟩

private theorem shellCoords_map {s : ℝ} (hs : 0 < s) (hu : s < 1) :
    (volume.restrict (tetrahedron 1 \ tetrahedron (1-s))).map (shellCoords s) =
      cubeUniform.prod (ENNReal.ofReal (shellFraction s) • angleVolume) := by
  classical
  let : IsFiniteMeasure (ENNReal.ofReal (shellFraction s) • angleVolume) :=
    angleVolume.smul_finite ENNReal.ofReal_ne_top
  symm
  apply Measure.prod_eq_generateFrom ((borel_eq_generateFrom_Iio _).symm.trans BorelSpace.measurable_eq.symm)
    MeasurableSpace.generateFrom_measurableSet isPiSystem_Iio MeasurableSpace.isPiSystem_measurableSet unitSpans
    (ENNReal.ofReal (shellFraction s) • angleVolume).toFiniteSpanningSetsIn
  rintro _ ⟨t,rfl⟩ A hA
  change MeasurableSet A at hA
  let a := 1-s
  let b := shellFraction s
  let c := shellQuantile s (clip t)
  have ha : 0 < a := sub_pos.mpr hu
  have hb : 0 < b := shellFraction_pos hs hu.le
  have hc := shellQuantile_bounds (show s ∈ Icc (0:ℝ) 1 from ⟨hs.le,hu.le⟩) (clip_mem t)
  have hfin : volume (coneSector 1 A) ≠ ∞ := measure_ne_top_of_subset inter_subset_right unitVolume_finite
  have hfina : volume (coneSector a A) ≠ ∞ :=
    measure_ne_top_of_subset (coneSector_mono (show a ≤ 1 from by dsimp [a]; linarith) A) hfin
  have hcs : c^3-a^3=b*clip t := by
    change shellQuantile s (clip t)^3-(1-s)^3 = shellFraction s*clip t
    rw [shellQuantile_cube hs hu (clip_mem t)]
    ring
  rw [Measure.map_apply (measurable_shellCoords s) (measurableSet_Iio.prod hA),
    Measure.restrict_apply ((measurableSet_Iio.prod hA).preimage (measurable_shellCoords s)),
    shellCoords_rectangle hs hu,measure_sdiff (coneSector_mono hc.1 A) (measurableSet_coneSector _ hA).nullMeasurableSet hfina,
    volume_coneSector (ha.trans_le hc.1), volume_coneSector ha,cubeUniform_Iio,Measure.smul_apply,
    smul_eq_mul,angleVolume_apply hA,← ENNReal.sub_mul (fun _ _ => hfin),
    ← ENNReal.ofReal_sub _ (pow_nonneg ha.le 3)]
  change ENNReal.ofReal (c^3-a^3)*_ = _
  rw [hcs,ENNReal.ofReal_mul hb.le]
  ac_rfl

private def angleLaw := (volume (tetrahedron 1))⁻¹ • angleVolume

private instance : IsProbabilityMeasure angleLaw := ⟨by
  rw [angleLaw,Measure.smul_apply,smul_eq_mul,angleVolume_univ,
    ENNReal.inv_mul_cancel unitVolume_pos.ne' unitVolume_finite]⟩

private theorem shellCoords_map_prob {s : ℝ} (hs : 0 < s) (hu : s < 1) :
    (volume.restrict (tetrahedron 1 \ tetrahedron (1-s))).map (shellCoords s) =
      (volume (tetrahedron 1)*ENNReal.ofReal (shellFraction s)) • cubeUniform.prod angleLaw := by
  rw [shellCoords_map hs hu,angleLaw,Measure.prod_smul_right,Measure.prod_smul_right,smul_smul]
  have h := ENNReal.mul_inv_cancel unitVolume_pos.ne' unitVolume_finite
  have he : volume (tetrahedron 1)*ENNReal.ofReal (shellFraction s)*(volume (tetrahedron 1))⁻¹ =
      ENNReal.ofReal (shellFraction s) := by
    rw [mul_right_comm,h,one_mul]
  rw [he]

private theorem shellCoords_inverse {s : ℝ} (hs : 0 < s) (hu : s < 1) {x : Position}
    (hx : x ∈ tetrahedron 1 \ tetrahedron (1-s)) :
    shellQuantile s (shellCoords s x).1 • (shellCoords s x).2 = x := by
  let r := tetrahedronRadius x
  let a := 1-s
  let b := shellFraction s
  have ha : 0 < a := sub_pos.mpr hu
  have hb : 0 < b := shellFraction_pos hs hu.le
  have hr : a ≤ r := le_of_not_gt fun h => hx.2 (tetrahedronRadius_lt.mp h)
  have hr1 : r < 1 := tetrahedronRadius_lt.mpr hx.1
  have hv : (r^3-a^3)/b ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha.le hr 3)) hb.le, (div_le_one hb).mpr ?_⟩
    dsimp [a,b,shellFraction]
    linarith only [pow_le_pow_left₀ (ha.le.trans hr) hr1.le 3]
  have hv' := shellQuantile_cube hs hu hv
  have he : shellQuantile s ((r^3-a^3)/b)^3 = r^3 := by
    change _ = a^3 + b*((r^3-a^3)/b) at hv'
    rw [hv']
    field_simp [hb.ne']
    ring
  have hq := shellQuantile_bounds (show s ∈ Icc (0:ℝ) 1 from ⟨hs.le,hu.le⟩) hv
  have h := (pow_left_inj₀ (ha.le.trans hq.1) (ha.le.trans hr) (by decide : 3 ≠ 0)).mp he
  change shellQuantile s ((r^3-a^3)/b) • r⁻¹ • x = x
  rw [h,smul_inv_smul₀ (ha.trans_le hr).ne']

/-- The normalized Euclidean cone measure of the actual tetrahedron,
together with the independent uniform cubic volume coordinate. -/
def tetrahedronCone : TetrahedronCone where
  law := cubeUniform.prod angleLaw
  probability := inferInstance
  support := by
    have h₁ : ∀ᵐ v ∂cubeUniform, v ∈ Icc (0:ℝ) 1 := (ae_restrict_mem measurableSet_Ico).mono fun _ h => ⟨h.1,h.2.le⟩
    have h₂ : ∀ᵐ x ∂angleVolume, ‖x‖ ≤ 2 :=
      (ae_map_iff measurable_conePoint.aemeasurable (measurableSet_le measurable_norm measurable_const)).mpr
        (ae_of_all _ conePoint_bound)
    have h₃ : ∀ᵐ x ∂angleLaw, ‖x‖ ≤ 2 :=
      Measure.ae_smul_measure h₂ (volume (tetrahedron 1))⁻¹
    exact ((Measure.quasiMeasurePreserving_fst (μ := cubeUniform) (ν := angleLaw)).ae h₁).and
      ((Measure.quasiMeasurePreserving_snd (μ := cubeUniform) (ν := angleLaw)).ae h₃)
  integrate := by
    intro s hs hu f
    let μ := volume.restrict (tetrahedron 1 \ tetrahedron (1-s))
    let F := fun z : ℝ × Position => f (shellQuantile s z.1 • z.2)
    have hF : Continuous F := by unfold F shellQuantile; fun_prop (disch := norm_num)
    have hinv : (∫ x, f x ∂μ) = ∫ x, F (shellCoords s x) ∂μ :=
      integral_congr_ae ((ae_restrict_mem ((tetrahedron_open _).measurableSet.diff (tetrahedron_open _).measurableSet)).mono
        (fun _ hx => congrArg (fun y => f y) (shellCoords_inverse hs hu hx).symm))
    rw [hinv, ← integral_map (measurable_shellCoords s).aemeasurable hF.aestronglyMeasurable]
    rw [show μ.map (shellCoords s) = _ from shellCoords_map_prob hs hu,integral_smul_measure,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal (shellFraction_pos hs hu.le).le]
    rfl

end TSGA.SSW
