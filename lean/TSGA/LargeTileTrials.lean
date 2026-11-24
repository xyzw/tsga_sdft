import TSGA.VariableWindowTrial
import TSGA.CoulombFrozenTile

/-! # Trial states on large-oscillation tiles -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW

/-- The named gradient of the rotated square root retains its pointwise
bound when integrated over a tile. -/
theorem axial_sqrt_regular (chain : WeakPhaseProduct) {D : Density} {φ : Phase} {p : ℝ}
    {S : MatrixGradient} (reg : SqrtRegular D S) (hφ : φ.Regular p)
    (phase : Integrable fun x => D.charge x*‖φ.grad x‖^2) :
    SqrtRegular (rotatedDensity D φ) (axialGradient D φ S) := by
  have hw : IsMatrixGradientOn Set.univ ((rotatedDensity D φ).power (1/2)) (axialGradient D φ S) := by
    intro i j k
    simpa only [rotated_power D φ (by norm_num : 0 ≤ (1/2 : ℝ)),rotate_by_entry,axialGradient]
      using chain φ hφ (axialWeight j k) i _ _ (reg.weak i j k)
  have hm (i j k) := (locallyIntegrableOn_univ.mp (hw i j k).2.1).aestronglyMeasurable.aemeasurable
  have hs : AEMeasurable (matrixGradNorm (axialGradient D φ S)) volume :=
    Real.continuous_sqrt.measurable.comp_aemeasurable <|
      Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ =>
        Finset.aemeasurable_fun_sum _ fun k _ => (hm i j k).norm.pow_const 2
  have hi : Integrable (kineticDensity S) := reg.grad.integrable_sq
  refine ⟨by rw [show (rotatedDensity D φ).charge = D.charge from funext (rotated_charge D φ)]; exact reg.charge,hw,
    (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).2 ?_⟩
  apply ((hi.const_mul 2).add (phase.const_mul 2)).mono' (hs.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun x => (Real.norm_of_nonneg (sq_nonneg _)).le.trans (axial_kinetic_pointwise D φ S x)

def roughTrialCoeff (H : FiniteEnergyInputs) (K : ℝ) : ℝ :=
  K + H.loCoeff + 5*H.interiorConstant

/-- Both signs of the energy of an individual window are controlled by the
same three positive terms. The state in the upper estimate has the exact
tapered, phase-rotated density. -/
theorem FiniteEnergyInputs.large_window_trial (H : FiniteEnergyInputs)
    (product : WeakScalarMatrixProduct) (chain : WeakPhaseProduct) {D : Density} {S : MatrixGradient}
    (reg : SqrtRegular D S) {φ : Phase} {p K : ℝ} (hφ : φ.Regular p) (hK : 0 ≤ K)
    (p₄ : Integrable fun x => D.charge x^(4/3:ℝ)) (p₅ : Integrable fun x => D.charge x^(5/3:ℝ))
    (phase : Integrable fun x => D.charge x*‖φ.grad x‖^2)
    {f : Position → ℝ} (hf : ∀ x, f x ∈ Set.Icc 0 1) {g : Position → Position}
    (weak : ∀ i, WeakPartialOn Set.univ i (fun x => √(f x)) (fun x => g x i))
    (fisher : Integrable fun x => D.charge x*‖g x‖^2) :
    let N := windowDensity (rotatedDensity D φ) f fun x => (hf x).1
    let C := roughTrialCoeff H K*(∫ x, roughTileDensity D φ x*f x) +
      4*H.interiorConstant*(∫ x, kineticDensity S x*f x) + 2*H.interiorConstant*(∫ x, D.charge x*‖g x‖^2)
    ∃ Γ, feasible N.matrix Γ ∧ Γ.kinetic + Γ.interaction - hartree N.charge ≤ C ∧
      H.loCoeff*chargeMoment N (4/3) ≤ C ∧ |energy N.matrix| ≤ C := by
  intro N C
  have rot := axial_sqrt_regular chain reg hφ phase
  let A := axialGradient D φ S
  have ea : Integrable (kineticDensity A) := rot.grad.integrable_sq
  have es : Integrable (kineticDensity S) := reg.grad.integrable_sq
  have hm := window_measurable f (fun x => (hf x).1) weak
  have win {u : Position → ℝ} (hu : Integrable u) : Integrable (fun x => f x*u x) :=
    window_product_integrable hf hm hu
  have er : Integrable (roughTileDensity D φ) := (p₄.add p₅).add phase
  let R := ∫ x, f x*roughTileDensity D φ x
  let T := ∫ x, f x*kineticDensity S x
  let Q := ∫ x, f x*(D.charge x*‖φ.grad x‖^2)
  let G := ∫ x, D.charge x*‖g x‖^2
  have nonneg (x) := D.charge_nonneg x
  have n₄ (x) := Real.rpow_nonneg (nonneg x) (4/3:ℝ)
  have n₅ (x) := Real.rpow_nonneg (nonneg x) (5/3:ℝ)
  have nq (x) := mul_nonneg (nonneg x) (sq_nonneg ‖φ.grad x‖)
  have bound {u : Position → ℝ} (hu : Integrable u) (h : ∀ x, u x ≤ roughTileDensity D φ x) :
      (∫ x, f x*u x) ≤ R :=
    integral_mono (win hu) (win er) fun x => mul_le_mul_of_nonneg_left (h x) (hf x).1
  have l4 := bound p₄ fun x => by unfold roughTileDensity; linarith only [n₅ x,nq x]
  have l5 := bound p₅ fun x => by unfold roughTileDensity; linarith only [n₄ x,nq x]
  have lq : Q ≤ R := bound phase fun x => by unfold roughTileDensity; linarith only [n₄ x,n₅ x]
  have hR : 0 ≤ R := (integral_nonneg fun x => mul_nonneg (hf x).1 (n₄ x)).trans l4
  have hT : 0 ≤ T := integral_nonneg fun x => mul_nonneg (hf x).1 (sq_nonneg _)
  have hG : 0 ≤ G := integral_nonneg fun x => mul_nonneg (nonneg x) (sq_nonneg _)
  have a : (∫ x, f x*kineticDensity A x) ≤ 2*T+2*Q := by
    have up := ((win es).const_mul 2).add ((win phase).const_mul 2)
    have h := integral_mono (win ea) up fun x => (mul_le_mul_of_nonneg_left
      (axial_kinetic_pointwise D φ S x) (hf x).1).trans_eq (by change _ = 2*(f x*_)+2*(f x*_); ring)
    simpa only [Pi.add_apply,integral_add ((win es).const_mul 2) ((win phase).const_mul 2),
      integral_const_mul] using h
  obtain ⟨Γ,rep,exchange,kin⟩ := H.window_trial product rot hf weak (by simpa only [rotated_charge] using fisher)
    (by simpa only [rotated_charge] using p₅)
  have moment := (window_charge_moment (D := rotatedDensity D φ) hf hm
    (by simpa only [rotated_charge] using p₄) (by norm_num : (1:ℝ) ≤ 4/3)).2
  simp only [rotated_charge,Real.one_rpow,one_mul] at kin moment
  have id : C = roughTrialCoeff H K*R+4*H.interiorConstant*T+2*H.interiorConstant*G := by
    simp only [C,R,T,G,mul_comm (f _)]
  have c₀ := H.interiorConstant_nonneg
  have lo : H.loCoeff*chargeMoment N (4/3) ≤ C := by
    rw [id]
    dsimp only [roughTrialCoeff]
    have hl := mul_le_mul_of_nonneg_left (moment.trans l4) H.lo_nonneg
    linarith only [hl,mul_nonneg hK hR,mul_nonneg c₀ hR,mul_nonneg c₀ hT,mul_nonneg c₀ hG]
  have up : Γ.kinetic+Γ.interaction-hartree N.charge ≤ C := by
    rw [id]
    dsimp only [roughTrialCoeff]
    have hsum : (∫ x, f x*D.charge x^(5/3:ℝ))+2*(∫ x, f x*kineticDensity A x)+2*G ≤ 5*R+4*T+2*G := by
      linarith only [l5,a,lq]
    have h := kin.trans (mul_le_mul_of_nonneg_left hsum c₀)
    linarith only [h,exchange,mul_nonneg hK hR,mul_nonneg H.lo_nonneg hR]
  have low := le_levyLieb (M := N.matrix) ⟨_,rep⟩ (a := hartree N.charge-H.loCoeff*chargeMoment N (4/3))
    fun γ hγ => (H.liebOxford N γ hγ).trans (le_add_of_nonneg_left γ.kinetic_nonneg)
  refine ⟨Γ,rep,up,lo,abs_le.mpr ⟨?_,?_⟩⟩
  · change -C ≤ levyLieb N.matrix - hartree N.charge
    linarith only [low,lo]
  · change levyLieb N.matrix - hartree N.charge ≤ C
    linarith only [levyLieb_le rep,up]

end TSGA.ManyBody
