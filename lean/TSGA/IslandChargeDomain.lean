import TSGA.IslandMasks

/-! # Coulomb form domains of the random charges in Appendix C -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {v : ℝ}

structure IslandMasks.MeasurableFields (m : IslandMasks μ v) : Prop where
  outside : Measurable (Function.uncurry m.outside)
  first : Measurable (Function.uncurry m.first)
  core : Measurable (Function.uncurry m.core)

/-- Absolute domination by the deterministic total charge. The constant
may depend on the filling fraction in the form-domain argument. -/
structure IslandChargeControl (ρ : Position → ℝ) (f : Ω → Position → ℝ) : Prop where
  measurable : Measurable (Function.uncurry f)
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ ω x, |f ω x| ≤ C*ρ x

namespace IslandChargeControl
variable {ρ : Position → ℝ} {f g : Ω → Position → ℝ}

theorem add (hf : IslandChargeControl ρ f) (hg : IslandChargeControl ρ g) :
    IslandChargeControl ρ (fun ω x => f ω x + g ω x) := by
  obtain ⟨A,ha,h₁⟩ := hf.bound
  obtain ⟨B,hb,h₂⟩ := hg.bound
  refine ⟨hf.measurable.add hg.measurable,A+B,add_nonneg ha hb,fun ω x => ?_⟩
  rw [add_mul]; exact (abs_add_le _ _).trans (add_le_add (h₁ ω x) (h₂ ω x))

theorem sub (hf : IslandChargeControl ρ f) (hg : IslandChargeControl ρ g) :
    IslandChargeControl ρ (fun ω x => f ω x - g ω x) := by
  obtain ⟨A,ha,h₁⟩ := hf.bound
  obtain ⟨B,hb,h₂⟩ := hg.bound
  refine ⟨hf.measurable.sub hg.measurable,A+B,add_nonneg ha hb,fun ω x => ?_⟩
  rw [add_mul]; exact (abs_sub _ _).trans (add_le_add (h₁ ω x) (h₂ ω x))

theorem coeff (hf : IslandChargeControl ρ f) (a : Ω → Position → ℝ)
    (hm : Measurable (Function.uncurry a)) (C : ℝ) (hc : 0 ≤ C) (h : ∀ ω x, |a ω x| ≤ C) :
    IslandChargeControl ρ (fun ω x => a ω x * f ω x) := by
  obtain ⟨A,ha,hf'⟩ := hf.bound
  refine ⟨hm.mul hf.measurable,C*A,mul_nonneg hc ha,?_⟩
  intro ω x
  rw [abs_mul,mul_assoc]
  exact mul_le_mul (h _ _) (hf' _ _) (abs_nonneg _) hc

theorem joint (hf : IslandChargeControl ρ f) (hg : IslandChargeControl ρ g)
    (hρ : ∀ x, 0 ≤ ρ x) (hD : Integrable (directKernel ρ ρ) pairVolume) :
    Integrable (fun z : Ω × PairSpace => directKernel (f z.1) (g z.1) z.2) (μ.prod pairVolume) := by
  obtain ⟨A,ha,h₁⟩ := hf.bound
  obtain ⟨B,hb,h₂⟩ := hg.bound
  have hm₁ : Measurable (fun z : Ω × PairSpace => f z.1 z.2.1) :=
    hf.measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hm₂ : Measurable (fun z : Ω × PairSpace => g z.1 z.2.2) :=
    hg.measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  apply ((hD.comp_snd μ).const_mul (A*B)).mono'
  · unfold directKernel
    exact ((hm₁.mul hm₂).div ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd)).norm).aestronglyMeasurable
  apply ae_of_all
  rintro ⟨ω,x,y⟩
  change ‖f ω x*g ω y / ‖x-y‖‖ ≤ A*B*(ρ x*ρ y/‖x-y‖)
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (norm_nonneg _)]
  have hu := mul_le_mul (h₁ ω x) (h₂ ω y) (abs_nonneg _) (mul_nonneg ha (hρ x))
  calc
    _ ≤ (A*ρ x*(B*ρ y))/‖x-y‖ := div_le_div_of_nonneg_right hu (norm_nonneg _)
    _ = _ := by ring

theorem triple {h : Ω → Position → ℝ} (hf : IslandChargeControl ρ f) (hg : IslandChargeControl ρ g)
    (hh : IslandChargeControl ρ h) (hρ : ∀ x, 0 ≤ ρ x) (hD : Integrable (directKernel ρ ρ) pairVolume) :
    ∀ᵐ ω ∂μ, TripleDirectIntegrable (f ω) (g ω) (h ω) := by
  have self {a : Ω → Position → ℝ} (ha : IslandChargeControl ρ a) := (ha.joint (μ := μ) ha hρ hD).prod_right_ae
  filter_upwards [self hf,self hg,self hh,self ((hf.add hg).add hh),self (hf.sub hg),self (hf.sub hh),self (hg.sub hh)]
    with ω h₁ h₂ h₃ hsum ha hb hc
  exact ⟨h₁,h₂,h₃,hsum,ha,hb,hc⟩

end IslandChargeControl

/-- A deterministic Coulomb form-domain hypothesis, shared by every random
configuration and all polarized fluctuation terms. For L¹∩L² charges it
follows from the usual scalar Coulomb convolution bound. -/
structure IslandChargeDomain (B D : Density) : Prop where
  background : Measurable B.charge
  added : Measurable D.charge
  direct : Integrable (directKernel (B.charge+D.charge) (B.charge+D.charge)) pairVolume

namespace IslandMasks
variable (m : IslandMasks μ v) {B D : Density} (M : m.MeasurableFields) (H : IslandChargeDomain B D)

private theorem base (a : Position → ℝ) (ha : Measurable a) (hp : ∀ x, 0 ≤ a x)
    (h : ∀ x, a x ≤ (B.charge+D.charge) x) : IslandChargeControl (B.charge+D.charge) (fun (_ : Ω) x => a x) :=
  ⟨ha.comp measurable_snd,1,zero_le_one,fun _ x => by rw [one_mul,abs_of_nonneg (hp x)]; exact h x⟩

include M H in
theorem controls :
    let Q := IslandChargeControl (B.charge+D.charge) (Ω := Ω)
    Q (m.outerCharge B) ∧ Q (m.innerCharge B D) ∧ Q (fun _ x => B.charge x + D.charge x) ∧
    Q (m.firstFluct B) ∧ Q (m.shellFluct B) ∧ Q (m.coreFluct D) := by
  intro Q
  have hb := base B.charge H.background B.charge_nonneg (D := D) (B := B)
    (fun x => le_add_of_nonneg_right (D.charge_nonneg x)) (Ω := Ω)
  have hd := base D.charge H.added D.charge_nonneg (D := D) (B := B)
    (fun x => le_add_of_nonneg_left (B.charge_nonneg x)) (Ω := Ω)
  have out := hb.coeff _ M.outside 1 zero_le_one (fun ω x => by rw [abs_of_nonneg (m.outside_range ω x).1]; exact (m.outside_range ω x).2)
  have mask {a : Ω → Position → ℝ} (hm : Measurable (Function.uncurry a)) (hr : ∀ ω x, a ω x ∈ Set.Icc 0 1)
      (c k : ℝ) : Measurable (Function.uncurry (fun ω x => c*(a ω x-k))) ∧
        ∀ ω x, |c*(a ω x-k)| ≤ |c| * (1+|k|) := by
    refine ⟨measurable_const.mul (hm.sub measurable_const),?_⟩
    intro ω x
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact (abs_sub _ _).trans (add_le_add ((abs_of_nonneg (hr ω x).1).le.trans (hr ω x).2) le_rfl)
  have mb (c k : ℝ) := mask M.first m.first_range c k
  have md (c k : ℝ) := mask M.core m.core_range c k
  have cb (c k : ℝ) := hb.coeff _ (mb c k).1 _ (mul_nonneg (abs_nonneg _) (by positivity)) (mb c k).2
  have cd (c k : ℝ) := hd.coeff _ (md c k).1 _ (mul_nonneg (abs_nonneg _) (by positivity)) (md c k).2
  have ins : Q (m.innerCharge B D) := by
    change IslandChargeControl (B.charge+D.charge) (fun ω x =>
      (m.c₁*m.first ω x)*B.charge x+(m.c₂*m.core ω x)*D.charge x)
    simpa only [sub_zero] using (cb m.c₁ 0).add (cd m.c₂ 0)
  have hsum := hb.add hd
  have first := cb (m.c₁-1) m.meanFirst
  have core := cd m.c₂ m.meanCore
  refine ⟨out,ins,hsum,first,?_,core⟩
  have he : m.shellFluct B = fun ω x =>
      (m.outerCharge B ω x + m.innerCharge B D ω x - (B.charge x + D.charge x)) - m.firstFluct B ω x - m.coreFluct D ω x := by
    funext ω x
    linarith only [m.fluctuation_split B D ω x]
  rw [he]
  exact ((((out.add ins).sub hsum).sub first).sub core)

theorem fluctuation_domains (M : m.MeasurableFields) (H : IslandChargeDomain B D) :
    JointDirectIntegrable μ (m.firstFluct B) ∧ JointDirectIntegrable μ (m.shellFluct B) ∧
    JointDirectIntegrable μ (m.coreFluct D) ∧ ∀ᵐ ω ∂μ,
      TripleDirectIntegrable (m.firstFluct B ω) (m.shellFluct B ω) (m.coreFluct D ω) := by
  obtain ⟨_,_,_,a,b,c⟩ := m.controls M H
  have hp (x) : 0 ≤ (B.charge+D.charge) x := add_nonneg (B.charge_nonneg x) (D.charge_nonneg x)
  exact ⟨a.joint a hp H.direct,b.joint b hp H.direct,c.joint c hp H.direct,a.triple b c hp H.direct⟩

end IslandMasks
end TSGA.ManyBody
