import TSGA.RescaledFields
import TSGA.PhaseLocalization

/-! # The phase and weak derivatives under particle-number scaling

The factor L multiplying the phase preserves the local wavevector. Its
Hessian and the weak gradient of the matrix root each acquire one inverse
length. The root derivative is transported on the rescaled active set.
-/

noncomputable section
namespace TSGA
open MeasureTheory MeasureTheory.Measure Metric Set PhaseLocalization
open scoped ContDiff ENNReal

/-- The dilation φ_L(x) = L φ(x/L) used in the spiral example. -/
def Phase.spiralDilate (φ : Phase) (L : ℝ) : Phase where
  value x := L*φ.value (L⁻¹ • x)
  grad x := φ.grad (L⁻¹ • x)
  hessian x i j := L⁻¹ * φ.hessian (L⁻¹ • x) i j

private theorem preimage_dilated_ball (x : Position) (r : ℝ) {L : ℝ} (hL : 0 < L) :
    (fun z : Position => L⁻¹ • z) ⁻¹' ball (L⁻¹ • x) r = ball x (L*r) := by
  ext y
  change dist (L⁻¹ • y) (L⁻¹ • x) < r ↔ dist y x < L*r
  rw [dist_smul₀,Real.norm_of_nonneg (inv_nonneg.mpr hL.le),← div_eq_inv_mul,
    div_lt_iff₀ hL,mul_comm r]

private theorem indicator_pullback {F : Type*} [Zero F] (U : Set Position) (f : Position → F) (L : ℝ) :
    (fun y => U.indicator f (L⁻¹ • y)) =
    ((fun y : Position => L⁻¹ • y) ⁻¹' U).indicator (fun y => f (L⁻¹ • y)) := by
  classical
  funext y
  by_cases h : L⁻¹ • y ∈ U <;> simp [Set.indicator,h]

private theorem dilationLp {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}
    {f : Position → F} (h : MemLp f p) {L : ℝ} (hL : 0 < L) :
    MemLp (fun y : Position => f (L⁻¹ • y)) p := by
  let e := (Homeomorph.smul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hL.ne')).unit : ℝˣ) :
    Position ≃ₜ Position).toMeasurableEquiv
  apply e.memLp_map_measure_iff.mp
  change MemLp f p (Measure.map (fun y : Position => L⁻¹ • y) volume)
  rw [map_addHaar_smul _ (inv_ne_zero hL.ne')]
  exact h.smul_measure ENNReal.ofReal_ne_top

private theorem dilationLpOn {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}
    {f : Position → F} {U : Set Position} (hU : MeasurableSet U) (h : MemLp f p (volume.restrict U))
    {L : ℝ} (hL : 0 < L) :
    MemLp (fun y : Position => f (L⁻¹ • y)) p (volume.restrict ((fun y : Position => L⁻¹ • y) ⁻¹' U)) := by
  have eq := indicator_pullback U f L
  have hu : MemLp (U.indicator f) p volume := (memLp_indicator_iff_restrict hU).mpr h
  have hf := dilationLp (f := U.indicator f) hu hL
  rw [eq] at hf
  exact (memLp_indicator_iff_restrict (hU.preimage (measurable_const_smul _))).mp hf

private theorem localLp_spiral {p L : ℝ} {f : Position → ℝ} (h : LocalLpOn univ p f)
    (hL : 0 < L) (a : ℝ) : LocalLpOn univ p (fun y => a*f (L⁻¹ • y)) := by
  intro x _
  obtain ⟨r,hr,_,mem⟩ := h (L⁻¹ • x) (mem_univ _)
  refine ⟨L*r,mul_pos hL hr,subset_univ _,?_⟩
  rw [← preimage_dilated_ball x r hL]
  exact (dilationLpOn measurableSet_ball mem hL).const_mul a

private theorem dilated_setIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Position → F) {U : Set Position} (hu : MeasurableSet U) {L : ℝ} (hL : 0 < L) :
    (∫ x in (fun y : Position => L⁻¹ • y) ⁻¹' U, f (L⁻¹ • x)) = L^3 • ∫ x in U, f x := by
  rw [← integral_indicator (hu.preimage (measurable_const_smul _)),← indicator_pullback,← integral_indicator hu]
  simpa only [finrank_euclideanSpace,Fintype.card_fin] using
    Measure.integral_comp_inv_smul_of_nonneg volume (U.indicator f) hL.le

private theorem dilationLocalL1 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Position → F} {U : Set Position} (hU : IsOpen U) (hf : LocallyIntegrableOn f U)
    {L : ℝ} (hL : 0 < L) :
    LocallyIntegrableOn (fun y => f (L⁻¹ • y)) ((fun y : Position => L⁻¹ • y) ⁻¹' U) := by
  let e : Position ≃ₜ Position := Homeomorph.smul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hL.ne')).unit : ℝˣ)
  apply (locallyIntegrableOn_iff (hU.preimage e.continuous).isLocallyClosed).2
  intro k hsub hk
  have hc := hk.image e.continuous
  have hi := (integrable_indicator_iff hc.measurableSet).2
    (hf.integrableOn_compact_subset (show e '' k ⊆ U from image_subset_iff.mpr hsub) hc)
  apply (integrable_indicator_iff hk.measurableSet).1
  have eq (x : Position) : (e '' k).indicator f (L⁻¹ • x) = k.indicator (fun y => f (L⁻¹ • y)) x := by
    change (e '' k).indicator f (e x) = _
    by_cases hx : x ∈ k <;> simp [Set.indicator, hx]
    rfl
  simpa only [eq] using hi.comp_smul (inv_ne_zero hL.ne')

/-- Distributional chain rule for dilation on an open set. It applies to
the matrix entries on the active balls as well as the global phase. -/
theorem WeakPartialOn.dilate_open {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set Position} {i : Fin 3} {f g : Position → F} (h : WeakPartialOn U i f g)
    (hU : IsOpen U) {L : ℝ} (hL : 0 < L) :
    WeakPartialOn ((fun y : Position => L⁻¹ • y) ⁻¹' U) i (fun y => f (L⁻¹ • y))
      (fun y => L⁻¹ • g (L⁻¹ • y)) := by
  refine ⟨dilationLocalL1 hU h.1 hL,(dilationLocalL1 hU h.2.1 hL).smul L⁻¹,?_⟩
  intro ψ smooth compact supp
  let A : Position →L[ℝ] Position := L • ContinuousLinearMap.id ℝ Position
  let e : Position ≃ₜ Position := Homeomorph.smul ((isUnit_iff_ne_zero.mpr hL.ne').unit : ℝˣ)
  let χ (y : Position) := ψ (A y)
  let v : Position := PiLp.single 2 i 1
  have ds (y : Position) : fderiv ℝ χ y v = L*fderiv ℝ ψ (L • y) v := by
    change fderiv ℝ (ψ ∘ A) y v = _
    rw [((smooth.differentiable (by simp) (A y)).hasFDerivAt.comp y A.hasFDerivAt).fderiv,ContinuousLinearMap.comp_apply]
    exact map_smul (fderiv ℝ ψ (A y)) L v
  have support : tsupport χ ⊆ U := by
    change tsupport (ψ ∘ e) ⊆ U
    rw [tsupport_comp_eq_preimage]
    intro y hy
    have hsup := supp hy
    change L⁻¹ • (L • y) ∈ U at hsup
    simpa only [inv_smul_smul₀ hL.ne'] using hsup
  have hw := h.2.2 χ (smooth.comp A.contDiff) (compact.comp_homeomorph e) support
  have h1 (x : Position) : (fderiv ℝ ψ x) v • f (L⁻¹ • x) =
      L⁻¹ • ((fderiv ℝ χ (L⁻¹ • x)) v • f (L⁻¹ • x)) := by
    rw [ds,smul_inv_smul₀ hL.ne',smul_smul,inv_mul_cancel_left₀ hL.ne']
  have h2 (x : Position) : ψ x • L⁻¹ • g (L⁻¹ • x) = L⁻¹ • (χ (L⁻¹ • x) • g (L⁻¹ • x)) := by
    change _ = L⁻¹ • (ψ (L • L⁻¹ • x) • _)
    rw [smul_inv_smul₀ hL.ne',smul_comm]
  change (∫ x in _, (fderiv ℝ ψ x) v • f (L⁻¹ • x)) = _
  simp only [h1,h2,integral_smul]
  rw [dilated_setIntegral (fun y => (fderiv ℝ χ y) v • f y) hU.measurableSet hL,
      dilated_setIntegral (fun y => χ y • g y) hU.measurableSet hL,hw,smul_neg,smul_neg]

private theorem weak_mul_real {U : Set Position} {i : Fin 3} {f g : Position → ℝ}
    (h : WeakPartialOn U i f g) (b : ℝ) :
    WeakPartialOn U i (fun x => b * f x) (fun x => b * g x) := by
  refine ⟨h.1.smul b,h.2.1.smul b,?_⟩
  intro ψ hd hc hs
  have hw := h.2.2 ψ hd hc hs
  simp only [smul_eq_mul] at hw ⊢
  simp_rw [mul_left_comm _ b,integral_const_mul,hw,mul_neg]

theorem Phase.Regular.spiralDilate {φ : Phase} {p L : ℝ} (h : φ.Regular p) (hL : 0 < L) :
    (φ.spiralDilate L).Regular p where
  continuous_grad := h.continuous_grad.comp (continuous_const_smul _)
  value_Lp := localLp_spiral h.value_Lp hL L
  grad_Lp i := by simpa only [Phase.spiralDilate, one_mul] using localLp_spiral (h.grad_Lp i) hL 1
  hessian_Lp i j := localLp_spiral (h.hessian_Lp i j) hL L⁻¹
  weak_grad i := by
    have hw := (h.weak_grad i).dilate_open isOpen_univ hL
    rw [preimage_univ] at hw
    simpa only [Phase.spiralDilate, smul_eq_mul, ← mul_assoc,mul_inv_cancel₀ hL.ne',one_mul] using weak_mul_real hw L
  weak_hessian i j := by
    simpa only [Phase.spiralDilate,preimage_univ,smul_eq_mul] using (h.weak_hessian i j).dilate_open isOpen_univ hL

theorem dilatedGradient_memLp (G : MatrixGradient) {p : ℝ≥0∞} {L : ℝ} (hL : 0 < L)
    (h : MemLp (matrixGradNorm G) p) : MemLp (matrixGradNorm (dilatedGradient G L)) p := by
  simpa only [funext (matrixGradNorm_dilate G hL)] using (dilationLp h hL).const_mul L⁻¹

theorem Phase.hessianNorm_spiralDilate (φ : Phase) {L : ℝ} (hL : 0 < L) (x : Position) :
    (φ.spiralDilate L).hessianNorm x = L⁻¹*φ.hessianNorm (L⁻¹ • x) := by
  simp only [Phase.spiralDilate,Phase.hessianNorm,mul_pow,← Finset.mul_sum,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (inv_nonneg.mpr hL.le)]

private theorem spiral_curvature (D : Density) (φ : Phase) (p : ℝ) {L : ℝ} (hL : 0 < L) (x : Position) :
    (D.dilate L).charge x * (φ.spiralDilate L).hessianNorm x^p =
      L⁻¹^p*(D.charge (L⁻¹ • x)*φ.hessianNorm (L⁻¹ • x)^p) := by
  rw [Density.charge_dilate,Phase.hessianNorm_spiralDilate φ hL,
    Real.mul_rpow (inv_nonneg.mpr hL.le) (show 0 ≤ φ.hessianNorm (L⁻¹ • x) from Real.sqrt_nonneg _) ]
  ring

private theorem spiral_root (φ : Phase) (G : MatrixGradient) (p : ℝ) {L : ℝ} (hL : 0 < L) (x : Position) :
    weightedRoot (φ.spiralDilate L) (dilatedGradient G L) p x = L⁻¹^p*weightedRoot φ G p (L⁻¹ • x) := by
  simp only [weightedRoot,rootPower,Phase.spiralDilate,matrixGradNorm_dilate G hL,
    Real.mul_rpow (inv_nonneg.mpr hL.le) (show 0 ≤ matrixGradNorm G (L⁻¹ • x) from Real.sqrt_nonneg _)]
  ring

private theorem root_regular_dilate {D : Density} {φ : Phase} {G : MatrixGradient} {p L : ℝ}
    (h : RootRegularOn φ.active D p G) (hL : 0 < L) :
    RootRegularOn (φ.spiralDilate L).active (D.dilate L) p (dilatedGradient G L) := by
  intro x act
  obtain ⟨r,hr,inside,weak,flp,glp⟩ := h (L⁻¹ • x) act
  refine ⟨L*r,mul_pos hL hr,?_,?_,?_,?_⟩
  all_goals rw [← preimage_dilated_ball x r hL]
  · exact preimage_mono inside
  · exact fun i j k => (weak i j k).dilate_open isOpen_ball hL
  · exact fun j k => dilationLpOn measurableSet_ball (flp j k) hL
  · simpa only [funext (matrixGradNorm_dilate G hL)] using (dilationLpOn measurableSet_ball glp hL).const_mul L⁻¹

theorem PhaseAdmissible.spiralDilate {D : Density} {φ : Phase} {G : MatrixGradient} {p L : ℝ}
    (h : PhaseAdmissible D p φ G) (hL : 0 < L) :
    PhaseAdmissible (D.dilate L) p (φ.spiralDilate L) (dilatedGradient G L) where
  regular := h.regular.spiralDilate hL
  root_regular := root_regular_dilate h.root_regular hL
  kinetic := h.kinetic.comp_smul (inv_ne_zero hL.ne')
  curvature := by
    rw [funext (spiral_curvature D φ p hL)]
    exact (h.curvature.comp_smul (inv_ne_zero hL.ne')).const_mul _
  root_weighted := by
    change IntegrableOn (weightedRoot (φ.spiralDilate L) (dilatedGradient G L) p) _
    rw [funext (spiral_root φ G p hL)]
    exact (((integrable_weightedRoot h).comp_smul (inv_ne_zero hL.ne')).const_mul _).integrableOn

private theorem integral_spiral_power (f : Position → ℝ) (p : ℝ) {L : ℝ} (hL : 0 < L) :
    (∫ x : Position, L⁻¹^p*f (L⁻¹ • x)) = L^(3-p)*∫ x, f x := by
  rw [integral_const_mul]
  have hw := dilated_setIntegral f MeasurableSet.univ hL
  simp only [preimage_univ,Measure.restrict_univ,smul_eq_mul] at hw
  rw [hw,← mul_assoc,← Real.rpow_neg_eq_inv_rpow,← Real.rpow_natCast L 3,← Real.rpow_add hL]
  congr 2
  norm_num
  ring

theorem integral_spiral_curvature (D : Density) (φ : Phase) (p : ℝ) {L : ℝ} (hL : 0 < L) :
    (∫ x, (D.dilate L).charge x*(φ.spiralDilate L).hessianNorm x^p) =
      L^(3-p)*∫ x, D.charge x*φ.hessianNorm x^p := by
  simp only [spiral_curvature D φ p hL]
  exact integral_spiral_power (fun x => D.charge x * φ.hessianNorm x^p) p hL

theorem integral_spiral_weightedRoot (φ : Phase) (G : MatrixGradient) (p : ℝ) {L : ℝ} (hL : 0 < L) :
    (∫ x in (φ.spiralDilate L).active, ‖(φ.spiralDilate L).grad x‖^2*matrixGradNorm (dilatedGradient G L) x^p) =
      L^(3-p)*∫ x in φ.active, ‖φ.grad x‖^2*matrixGradNorm G x^p := by
  rw [← integral_weightedRoot_active,← integral_weightedRoot_active]
  simp only [spiral_root φ G p hL]
  exact integral_spiral_power _ p hL

end TSGA
