import TSGA.FrozenTile
import TSGA.PhaseLocalization
import TSGA.SpectralLipschitz
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! # Sobolev representatives on comparison balls

Recover the continuous density from its Sobolev power. The essential charge
supremum and the essential pairwise test on the open ball can then be
evaluated on its closure, including at points on its boundary.
-/

noncomputable section

namespace TSGA.Localization

open MeasureTheory Set Metric Filter PhaseLocalization
open scoped ComplexOrder

/-- The homogeneous Sobolev embedding and the scalar and matrix forms of
Morrey's inequality on Euclidean balls. The matrix derivatives are taken
entrywise and measured in Hilbert–Schmidt norm. -/
structure MatrixSobolevMorrey (p C : ℝ) : Prop where
  representative : 3 < p → ∀ (u : Position → SpinMatrix) (G : MatrixGradient),
    IsMatrixGradientOn univ u G → MemLp (matrixGradNorm G) (ENNReal.ofReal p) →
    ∃ v : Position → SpinMatrix, Continuous v ∧ v =ᵐ[volume] u
  matrix_pair : 3 < p → ∀ (u : Position → SpinMatrix) (G : MatrixGradient) (U : Set Position),
    IsOpen U → Continuous u →
    (∀ x ∈ U, ∃ V : Set Position, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      IsMatrixGradientOn V u G ∧ MemLp (matrixGradNorm G) (ENNReal.ofReal p) (volume.restrict V)) →
    ∀ (c : Position) (R : ℝ), 0 < R → closedBall c R ⊆ U →
    ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R,
      hilbertSchmidt (u x - u y)^p ≤ C * R^(p-3) * ∫ z in closedBall c R, rootPower G p z
  scalar_pair : 3 < p → ∀ (u : Position → ℝ) (g : Position → Position), Continuous u →
    ∀ (c : Position) (R : ℝ), 0 < R →
    (∀ i, WeakPartialOn (ball c R) i u (fun z => g z i)) →
    MemLp g (ENNReal.ofReal p) (volume.restrict (ball c R)) →
    ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R,
      |u x-u y|^p ≤ C * R^(p-3) * ∫ z in closedBall c R, ‖g z‖^p

theorem MatrixSobolevMorrey.global_pair {p C R : ℝ} (H : MatrixSobolevMorrey p C)
    {u : Position → SpinMatrix} {G : MatrixGradient} {c : Position} (hp : 3 < p)
    (grad : IsMatrixGradientOn univ u G) (lp : MemLp (matrixGradNorm G) (ENNReal.ofReal p))
    (hc : Continuous u) (hR : 0 < R)
    (x : Position) (hx : x ∈ closedBall c R) (y : Position) (hy : y ∈ closedBall c R) :
    hilbertSchmidt (u x - u y)^p ≤ C * R^(p-3) * ∫ z in closedBall c R, rootPower G p z := by
  apply H.matrix_pair hp _ _ univ isOpen_univ hc _ c R hR (subset_univ _) x hx y hy
  exact fun z _ => ⟨univ, isOpen_univ, mem_univ z, Subset.rfl, grad, by simpa using lp⟩

theorem MatrixSobolevMorrey.theta_pair {p C θ R : ℝ} (H : MatrixSobolevMorrey p C)
    {D : Density} {S T : MatrixGradient} {c : Position} (hp : 3 < p)
    (reg : DensityRegular D p θ S T) (hc : Continuous (D.power θ)) (hR : 0 < R)
    (x : Position) (hx : x ∈ closedBall c R) (y : Position) (hy : y ∈ closedBall c R) :
    hilbertSchmidt (D.power θ x - D.power θ y)^p ≤
      C * R^(p-3) * ∫ z in closedBall c R, rootPower T p z :=
  H.global_pair hp reg.theta_gradient reg.theta_Lp hc hR x hx y hy

theorem MatrixSobolevMorrey.root_pair {p C R : ℝ} (H : MatrixSobolevMorrey p C)
    {D : Density} {G : MatrixGradient} {U : Set Position} {c : Position} (hp : 3 < p)
    (hU : IsOpen U) (reg : RootRegularOn U D p G) (hc : Continuous (D.power (1/p)))
    (hR : 0 < R) (sub : closedBall c R ⊆ U)
    (x : Position) (hx : x ∈ closedBall c R) (y : Position) (hy : y ∈ closedBall c R) :
    hilbertSchmidt (D.power (1/p) x - D.power (1/p) y)^p ≤
      C * R^(p-3) * ∫ z in closedBall c R, rootPower G p z := by
  apply H.matrix_pair hp _ _ U hU hc _ c R hR sub x hx y hy
  intro z hz
  obtain ⟨s, hs, hsub, hgrad, _, hLp⟩ := reg z hz
  exact ⟨ball z s, isOpen_ball, mem_ball_self hs, hsub, hgrad, hLp⟩

theorem densityCharge_ae_congr {N D : Density} (h : N.matrix =ᵐ[volume] D.matrix) :
    N.charge =ᵐ[volume] D.charge :=
  h.mono fun _ he => congrArg (fun M : SpinMatrix => M.trace.re) he

theorem densityPower_ae_congr {N D : Density} (h : N.matrix =ᵐ[volume] D.matrix) (a : ℝ) :
    N.power a =ᵐ[volume] D.power a := by
  have eq {A B : SpinMatrix} (e : A = B) (hA : A.PosSemidef) (hB : B.PosSemidef) :
      hA.1.cfc (fun t => t ^ a) = hB.1.cfc (fun t => t ^ a) := by subst B; rfl
  exact h.mono fun x he => eq he (N.positive x) (D.positive x)

section Powers

open scoped MatrixOrder Matrix.Norms.L2Operator

private theorem cfc_power_pos {A : SpinMatrix} (h : A.PosSemidef) (a : ℝ) :
    (cfc (fun t : ℝ => t ^ a) A).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply cfc_nonneg
  intro t ht
  obtain ⟨i, rfl⟩ := h.1.spectrum_real_eq_range_eigenvalues ▸ ht
  exact Real.rpow_nonneg (h.eigenvalues_nonneg i) _

private theorem continuous_cfc_power (D : Density) (hc : Continuous D.matrix) {a : ℝ}
    (ha : 0 < a) : Continuous (D.power a) := by
  have e : D.power a = (fun x => cfc (fun t : ℝ => t ^ a) (D.matrix x)) :=
    funext fun x => ((D.positive x).1.cfc_eq _).symm
  rw [e]
  exact hc.cfc_of_mem_nhdsSet (fun t : ℝ => t^a) (s := univ) univ_mem
    (fun x => (D.positive x).1.isSelfAdjoint) (Real.continuous_rpow_const ha.le).continuousOn

/-- Invert the positive density power after taking its continuous Sobolev
representative. Closedness of the positive cone extends positivity to every
point, so this construction also applies at rank-deficient matrices. -/
theorem MatrixSobolevMorrey.density_representative {p C θ : ℝ} (H : MatrixSobolevMorrey p C)
    {D : Density} {S T : MatrixGradient} (hp : 3 < p) (hθ : 0 < θ)
    (reg : DensityRegular D p θ S T) :
    ∃ N : Density, N.matrix =ᵐ[volume] D.matrix ∧ Continuous N.matrix ∧
      ∀ a, 0 < a → Continuous (N.power a) := by
  obtain ⟨v, hv, heq⟩ := H.representative hp _ _ reg.theta_gradient reg.theta_Lp
  have pae : ∀ᵐ x, (v x).PosSemidef := by
    filter_upwards [heq] with x hx
    rw [hx, Density.power, ← (D.positive x).1.cfc_eq]
    exact cfc_power_pos (D.positive x) θ
  have pos : ∀ x, (v x).PosSemidef := by
    have dense := Measure.dense_of_ae (μ := volume) pae
    intro x
    have hx := dense x
    change x ∈ closure (v ⁻¹' {A : SpinMatrix | A.PosSemidef}) at hx
    rwa [(isClosed_setOfPred_posSemidef.preimage hv).closure_eq] at hx
  let V : Density := ⟨v, pos⟩
  let N : Density := ⟨V.power θ⁻¹, fun x => by
    rw [Density.power, ← (V.positive x).1.cfc_eq]
    exact cfc_power_pos (V.positive x) _⟩
  have hc : Continuous N.matrix := continuous_cfc_power V hv (inv_pos.mpr hθ)
  refine ⟨N, ?_, hc, fun _ ha => continuous_cfc_power N hc ha⟩
  filter_upwards [heq] with x hx
  dsimp only [N, V, Density.power]
  rw [← (pos x).1.cfc_eq]
  rw [hx, Density.power, ← (D.positive x).1.cfc_eq,
    ← cfc_comp (fun t : ℝ => t^θ⁻¹) (fun t : ℝ => t^θ) _ (D.positive x).1.isSelfAdjoint
      (Real.continuous_rpow_const (inv_nonneg.mpr hθ.le)).continuousOn
      (Real.continuous_rpow_const hθ.le).continuousOn]
  apply Eq.trans _ (cfc_id' ℝ _ (D.positive x).1.isSelfAdjoint)
  apply cfc_congr
  intro t ht
  obtain ⟨i, rfl⟩ := (D.positive x).1.spectrum_real_eq_range_eigenvalues ▸ ht
  simp [← Real.rpow_mul ((D.positive x).eigenvalues_nonneg i), hθ.ne']

end Powers

private theorem le_on_closedBall_of_ae {f : Position → ℝ} {a R : ℝ} {c : Position}
    (hf : Continuous f) (hR : 0 < R)
    (h : ∀ᵐ x ∂volume.restrict (ball c R), f x ≤ a) :
    ∀ x ∈ closedBall c R, f x ≤ a := by
  have eq : (fun x => min (f x) a) =ᵐ[volume.restrict (ball c R)] f :=
    h.mono fun x hx => min_eq_left hx
  have hb := Measure.eqOn_open_of_ae_eq eq isOpen_ball (hf.min continuous_const).continuousOn hf.continuousOn
  have sub : ball c R ⊆ {x | f x ≤ a} :=
    fun x hx => min_eq_left_iff.mp (hb hx)
  rw [← closure_ball c hR.ne']
  exact closure_minimal sub (isClosed_le hf continuous_const)

/-- The essential supremum for the original field is attained by the
continuous representative even if its maximizer lies on the boundary. -/
theorem exists_charge_max_on_ball {N D : Density} {R : ℝ} {c : Position}
    (hND : N.matrix =ᵐ[volume] D.matrix) (hN : Continuous N.matrix) (hR : 0 < R) :
    ∃ z ∈ closedBall c R, N.charge z = essSup D.charge (volume.restrict (ball c R)) ∧
      ∀ x ∈ closedBall c R, N.charge x ≤ N.charge z := by
  let μ := volume.restrict (ball c R)
  have hc : Continuous N.charge := by unfold Density.charge; fun_prop
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall c R).exists_isMaxOn
    ⟨c, mem_closedBall_self hR.le⟩ hc.continuousOn
  have bound := isMaxOn_iff.mp hmax
  have hu : ∀ᵐ x ∂μ, N.charge x ≤ N.charge z :=
    (ae_restrict_mem measurableSet_ball).mono fun x hx => bound x (ball_subset_closedBall hx)
  have : NeZero μ := ⟨fun he => (isOpen_ball.measure_ne_zero volume ⟨c, mem_ball_self hR⟩)
    (Measure.restrict_eq_zero.mp he)⟩
  have hl := le_on_closedBall_of_ae hc hR (ae_le_essSup (μ := μ) ⟨N.charge z, hu⟩) z hz
  have he : essSup N.charge μ = essSup D.charge μ :=
    essSup_congr_ae (ae_restrict_of_ae (densityCharge_ae_congr hND))
  refine ⟨z, hz, ?_, bound⟩
  exact (le_antisymm hl (essSup_le_of_ae_le _ hu
    (isCoboundedUnder_le_of_le _ N.charge_nonneg))).trans he

/-- The nested almost-everywhere test is equivalent to testing all pairs
of the continuous power on the closed comparison ball. -/
theorem smallPowerOscillation_iff_closedBall {N D : Density} {a κ R : ℝ} {c : Position}
    (hND : N.matrix =ᵐ[volume] D.matrix) (_hN : Continuous N.matrix)
    (ha : Continuous (N.power a)) (hR : 0 < R) :
    SmallPowerOscillation D a κ R c ↔
      ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R, hilbertSchmidt (N.power a x - N.power a y) ≤
        κ * (essSup D.charge (volume.restrict (ball c R)))^a := by
  let μ := volume.restrict (ball c R)
  let b := κ * (essSup D.charge μ)^a
  have hpow : N.power a =ᵐ[μ] D.power a := ae_restrict_of_ae (densityPower_ae_congr hND a)
  have hs : Continuous hilbertSchmidt := by unfold hilbertSchmidt; fun_prop
  change (∀ᵐ x ∂μ, ∀ᵐ y ∂μ, hilbertSchmidt (D.power a x - D.power a y) ≤ b) ↔ _
  constructor
  · intro h
    have point : ∀ᵐ x ∂μ, ∀ y ∈ closedBall c R, hilbertSchmidt (N.power a x - N.power a y) ≤ b := by
      filter_upwards [h, hpow] with x hx hex
      apply le_on_closedBall_of_ae (f := fun y => hilbertSchmidt (N.power a x - N.power a y))
        (hs.comp (continuous_const.sub ha)) hR
      filter_upwards [hx, hpow] with y hy hey
      rw [hex, hey]
      exact hy
    intro x hx y hy
    exact le_on_closedBall_of_ae (f := fun z => hilbertSchmidt (N.power a z - N.power a y))
      (hs.comp (ha.sub continuous_const)) hR
      (point.mono fun z hz => hz y hy) x hx
  · intro h
    have mem : ∀ᵐ x ∂μ, x ∈ closedBall c R :=
      (ae_restrict_mem measurableSet_ball).mono fun _ hx => ball_subset_closedBall hx
    filter_upwards [mem, hpow] with x hx hex
    filter_upwards [mem, hpow] with y hy hey
    rw [← hex, ← hey]
    exact h x hx y hy

end TSGA.Localization
