import TSGA.SmallBallAlignment
import TSGA.SmallBallReplacement
import TSGA.SmallBallGaugeCost
import TSGA.SmallBallCostDefinitions
import TSGA.VariableWindowTrial
import TSGA.ReplacementInterpolation

/-! # Fixed-wavevector comparison on a single free-size window

The window volume, Fisher integral and tapered density gradient are kept separately.
The energy scale ε is independent of the geometric radius of the comparison ball.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW PhaseLocalization Set Metric
open scoped ComplexOrder MatrixOrder

/-- Unaveraged signed replacement on one taper, prior to scalar interpolation. -/
theorem SmallBallMatrices.free_window_raw {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι]
    {ε C p θ R : ℝ} {c : Position} {N : Density} {S T : MatrixGradient}
    (F : IslandFockInputs μ) (radii : CoulombIslandRadii μ ι ε C)
    (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct) (sob : SobolevLipschitzComposition)
    (localComp : SobolevCompositionOn (closedBall c R)) (hR : 0 < R)
    (reg : DensityRegular N p θ S T) (cont : Continuous N.matrix) (one : Continuous (N.power 1))
    {s : SmallBallScale N R c} (m : SmallBallMatrices s) (t : SpiralTaper (closedBall c R))
    (tr : FrozenTaperRegular t) (hp : 1 ≤ p) (he : 0 < ε) (hle : ε ≤ 1)
    (hE : exteriorFormConstant F.oneBody ≤ C) (hI : F.oneBody.interiorConstant ≤ C)
    (σ : ℝ) (sign : σ=1 ∨ σ=-1) :
    let V := ∫ x, t.shape x
    let J := ∫ x in closedBall c R, ‖tr.grad x‖^2
    let k := ∫ x, t.shape x*kineticDensity S x
    let d := s.omega (1/p)/s.r^(1/p)
    σ * energy (t.field N).matrix ≤
      σ * energy (cutoffSpiral t.shape (if σ=1 then m.low else m.high) t.wavevector) +
        smallReplacementCost F.oneBody C ε V J k ‖t.wavevector‖ s.r (3*s.omega 1) d p 0 := by
  intro V J k d
  let q := t.wavevector
  let φ := frozenLinearPhase q
  let L := F.oneBody
  let r := s.r
  let dist := 3*s.omega 1
  have hd : 0 ≤ dist := mul_nonneg (by norm_num) (s.omega_nonneg 1 zero_lt_one)
  have hr := s.r_nonneg
  have hC := L.interiorConstant_nonneg.trans hI
  have sqr : SqrtRegular N S := ⟨reg.charge_L1, reg.sqrt_gradient, reg.sqrt_L2⟩
  have axes := m.axes t tr.mass reg hp hR localComp
  have osc : ∀ x ∈ closedBall c R, ‖φ.grad x-t.wavevector‖ ≤ 0 := fun x _ => by simp [φ, frozenLinearPhase, q]
  obtain ⟨A,_,bg,low,high,g1,g2,p1,p2⟩ := small_ball_replacement F radii leibniz chain sob tr sqr cont
    one axes m.low_pos m.high_pos (frozenLinearPhase_regular q) m.ordered
    (fun x hx => ⟨(m.trace_range (Or.inl rfl)).2,(s.cap x hx).trans (by linarith)⟩) osc he hle hd hE hI
  let W := alignmentCost t S r ((96/(1/p))*d)
  have ww : 0 ≤ W := by
    have hk : 0 ≤ k := integral_nonneg fun x => mul_nonneg (t.range x).1 (sq_nonneg _)
    have hv : 0 ≤ V := integral_nonneg fun x => (t.range x).1
    change 0 ≤ 2*192^2*k + (2*r*‖q‖^2*((96/(1/p))*d)^2)*V
    positivity
  have axis : m.axisCost t S p ≤ W := m.axisCost_le t S p
  have island : (if σ=1 then A.lower.cost else A.upper.cost) ≤ frozenAdditionCost t S tr.grad ε C dist r := by
    split
    · exact low
    · exact high
  have phase₁ : A.phaseGauge.forwardCost ≤ 0 := by simp [p1]
  have phase₂ : A.phaseGauge.inverseCost ≤ 0 := by simp [p2]
  have bound := small_replacement_error L A he hle hr s.cap tr.mass σ sign island bg ww le_rfl
    (g1.le.trans axis) (g2.le.trans axis) phase₁ phase₂
  have scale : A.error σ ≤ smallReplacementCost L C ε V J k ‖q‖ r dist d p 0 := by
    convert bound using 1
    simp [smallReplacementCost, smallAdditionCost, smallAffineCost,
      frozenAdditionCost, affineSpiralKinetic, W, alignmentCost, V, J, k, q, r]
  exact (A.signed he hle hd hC sign).trans (add_le_add le_rfl scale)

private def windowCoefficient (H : FiniteEnergyInputs) (C p : ℝ) : ℝ :=
  (12*C+2*C^2)*(96+(40+4*(3*p+1))+9) + 6*(29*H.interiorConstant+H.loCoeff) +
    16*192^2 + 16*(96*p)^2

private theorem windowCoefficient_nonneg (H : FiniteEnergyInputs) {C p : ℝ} (hc : 0 ≤ C) (hp : 0 ≤ p) :
    0 ≤ windowCoefficient H C p := by unfold windowCoefficient; positivity [H.interiorConstant_nonneg,H.lo_nonneg]

private def windowControl (ε V J k Q r b d : ℝ) : ℝ :=
  ε*(r+r^2)*V + r*J + k/ε + (r*Q^2*V)*(ε+d+d^2/ε) + (2*b*V)*(√(2*b/ε)+2*b/ε)

set_option maxHeartbeats 1000000 in
private theorem window_scalar (H : FiniteEnergyInputs) {C p ε V J k Q r b d : ℝ}
    (hc : 0 ≤ C) (hp : 1 ≤ p) (he : 0 < ε) (hle : ε ≤ 1) (hv : 0 ≤ V) (hj : 0 ≤ J)
    (hk : 0 ≤ k) (hr : 0 ≤ r) (hb : 0 ≤ b) (hd : 0 ≤ d) (bc : b ≤ r) (bd : b ≤ 3*p*(r*d)) :
    smallReplacementCost H C ε V J k Q r b d p 0 ≤ windowCoefficient H C p * windowControl ε V J k Q r b d := by
  let E := windowControl ε V J k Q r b d
  let mass := ε*(r+r^2)*V
  let kin := k/ε
  let U := r*Q^2*V
  let res := (2*b*V)*(√(2*b/ε)+2*b/ε)
  have zM : 0 ≤ mass := by dsimp [mass]; positivity
  have zK : 0 ≤ kin := by dsimp [kin]; positivity
  have zU : 0 ≤ U := by dsimp [U]; positivity
  have zS : 0 ≤ res := by dsimp [res]; positivity
  have zJ : 0 ≤ r*J := mul_nonneg hr hj
  have zε := mul_nonneg zU he.le
  have zd := mul_nonneg zU hd
  have zD := mul_nonneg zU (div_nonneg (sq_nonneg d) he.le)
  have eqE : E = mass + r*J + kin + (U*ε+U*d+U*(d^2/ε)) + res := by
    dsimp [E,windowControl,mass,kin,U,res]; ring
  have M : mass ≤ E := by linarith only [eqE,zJ,zK,zε,zd,zD,zS]
  have J' : r*J ≤ E := by linarith only [eqE,zM,zK,zε,zd,zD,zS]
  have K : kin ≤ E := by linarith only [eqE,zM,zJ,zε,zd,zD,zS]
  have P : U*ε ≤ E := by linarith only [eqE,zM,zJ,zK,zd,zD,zS]
  have P' : U*d ≤ E := by linarith only [eqE,zM,zJ,zK,zε,zD,zS]
  have P'' : U*(d^2/ε) ≤ E := by linarith only [eqE,zM,zJ,zK,zε,zd,zS]
  have R : res ≤ E := by linarith only [eqE,zM,zJ,zK,zε,zd,zD]
  have bJ := (mul_le_mul_of_nonneg_right bc hj).trans J'
  have eJ := (mul_le_of_le_one_left zJ hle).trans J'
  have ek : ε*k ≤ E := ((mul_le_of_le_one_left hk hle).trans
    ((le_div_iff₀ he).2 (mul_le_of_le_one_right hk hle))).trans K
  have hp₀ : 0 < p := by linarith
  have qb : Q^2*b*V ≤ 3*p*E := by
    calc
      _ ≤ Q^2*(3*p*(r*d))*V := by gcongr
      _ = 3*p*(U*d) := by dsimp [U]; ring
      _ ≤ _ := by gcongr
  let bg := smallAffineCost V J k Q 1 (2*r)
  let mi := smallAffineCost V J k Q ε⁻¹ (2*b+ε*(2*r))
  have bgBound : ε*bg ≤ 28*E := by
    calc
      _ = 8*(ε*k+2*(ε*(r*J)))+4*(U*ε) := by dsimp [bg,smallAffineCost,U]; ring
      _ ≤ 8*(E+2*E)+4*E := by gcongr
      _ = _ := by ring
  have mixBound : mi ≤ (40+4*(3*p+1))*E := by
    calc
      _ = 8*(kin+2*(b*J)+2*(ε*(r*J)))+4*(Q^2*b*V+U*ε) := by
        dsimp [mi,smallAffineCost,kin,U]; rw [div_eq_inv_mul]; ring
      _ ≤ 8*(E+2*E+2*E)+4*(3*p*E+E) := by gcongr
      _ = _ := by ring
  have sm : ε*((2*r+(2*r)^2)*V) ≤ 4*E := by
    dsimp only [mass] at M
    nlinarith only [M,mul_nonneg (mul_nonneg he.le hr) hv]
  have br : ε*b*V ≤ E := by
    dsimp only [mass] at M
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bc he.le) hv,
      mul_nonneg (mul_nonneg he.le (sq_nonneg r)) hv,M]
  have zC : 0 ≤ 12*C+2*C^2 := by positivity
  have isl : smallAdditionCost C ε V J k Q r b ≤ (12*C+2*C^2)*(96+(40+4*(3*p+1))+9)*E := by
    calc
      _ = (12*C+2*C^2)*(3*(ε*((2*r+(2*r)^2)*V)+ε*bg)+mi+3*(2*(ε*b*V)+res)) := by
        dsimp [smallAdditionCost,bg,mi,res]; ring
      _ ≤ (12*C+2*C^2)*(3*(4*E+28*E)+(40+4*(3*p+1))*E+3*(2*E+E)) := by gcongr
      _ = _ := by ring
  let I := H.interiorConstant
  let L := H.loCoeff
  have zi : 0 ≤ I := H.interiorConstant_nonneg
  have zl : 0 ≤ L := H.lo_nonneg
  have base : 6*((I+L)*mass+I*(ε*bg)) ≤ 6*(29*I+L)*E := by
    calc
      _ ≤ 6*((I+L)*E+I*(28*E)) := by gcongr
      _ = _ := by ring
  have gauge : 16*192^2*kin + 16*(96*p)^2*(U*(d^2/ε)) ≤ (16*192^2+16*(96*p)^2)*E := by
    calc
      _ ≤ 16*192^2*E + 16*(96*p)^2*E := by gcongr
      _ = _ := by ring
  calc
    _ = smallAdditionCost C ε V J k Q r b + 6*((I+L)*mass+I*(ε*bg)) +
        (16*192^2*kin+16*(96*p)^2*(U*(d^2/ε))) := by
      dsimp only [smallReplacementCost,I,L,bg,mass,kin,U]
      rw [show (96:ℝ)/(1/p)=96*p by field_simp]
      field_simp; ring
    _ ≤ _ := by dsimp only [windowCoefficient,I,L] at *; linarith only [isl,base,gauge]

private theorem window_residual {N : Density} {R θ ε p V G : ℝ} {z : Position}
    (s : SmallBallScale N R z) (hp : 3 < p) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hθp : 2 ≤ θ*p)
    (he : 0 < ε) (hv : 0 ≤ V) (hG : 0 ≤ G) (small : s.omega θ ≤ s.r^θ)
    (morrey : V*(s.omega θ)^p ≤ G) :
    let a := 6*s.omega 1
    let exp := max p (3*θ*p-3)-1
    V*a*(√(a/ε)+a/ε) ≤ ((6/θ)^(3/2:ℝ)+(6/θ)^2)*(ε*V*(s.r+s.r^2)+G/ε^exp) := by
  intro a exp
  let B := ε*V*(s.r+s.r^2)+G/ε^exp
  have ha : 0 ≤ a := mul_nonneg (by norm_num) (s.omega_nonneg _ zero_lt_one)
  have hL : 0 ≤ 6/θ := by positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity [s.r_nonneg]
  have cap : a ≤ (6/θ)*(s.r^(1-θ)*s.omega θ) := by
    calc
      _ ≤ 6*((1/θ*s.r^(1-θ))*s.omega θ) := mul_le_mul_of_nonneg_left (s.omega_one_le θ hθ hθ₁) (by norm_num)
      _ = _ := by ring
  rcases s.r_nonneg.eq_or_lt with hz | hr
  · have az : a=0 := le_antisymm (by dsimp [a]; linarith only [s.small,hz]) ha
    rw [az,mul_zero,zero_mul]
    exact mul_nonneg (add_nonneg (Real.rpow_nonneg hL _) (sq_nonneg _)) hB
  · have bnd (m : ℝ) (hm : m ∈ Icc (3/2:ℝ) 2) : V*(ε^(1-m)*a^m) ≤ (6/θ)^m*B := by
      have h := residual_charge_interpolation hp hθp hm he hr hv hL ha (s.omega_nonneg θ hθ) small cap morrey
      have id : ε^(1-max p (3*θ*p-3))*G = G/ε^exp := by
        rw [show 1-max p (3*θ*p-3) = -exp by dsimp [exp]; ring, Real.rpow_neg he.le, inv_mul_eq_div]
      simpa only [← mul_assoc,id,B] using h
    have h₁ := bnd (3/2) (by constructor <;> norm_num)
    have h₂ := bnd 2 (by constructor <;> norm_num)
    have e₁ : ε^(1-(3/2:ℝ))*a^(3/2:ℝ) = a*√(a/ε) := by
      rw [Real.sqrt_eq_rpow,Real.div_rpow ha he.le,show (3/2:ℝ)=1/2+1 by norm_num,
        Real.rpow_add_one' ha (by norm_num : (1/2:ℝ)+1≠0),show (1:ℝ)-(1/2+1)=-(1/2) by norm_num,Real.rpow_neg he.le]
      ring
    have e₂ : ε^(1-(2:ℝ))*a^(2:ℝ) = a*(a/ε) := by
      rw [show (1:ℝ)-2= -(1:ℝ) by norm_num, Real.rpow_neg he.le,Real.rpow_one,Real.rpow_two]; ring
    rw [e₁] at h₁
    rw [e₂,Real.rpow_two] at h₂
    change _ ≤ _*B
    nlinarith only [h₁,h₂]

private theorem window_volume {R : ℝ} {c : Position} (hR : 0 < R)
    (t : SpiralTaper (closedBall c R)) (tr : FrozenTaperRegular t) :
    (∫ x, t.shape x) ≤ ballVolume 1*R^3 := by
  let B := closedBall c R
  have support : B.indicator t.shape = t.shape := funext fun x => by
    by_cases h : x ∈ B
    · simp [h]
    · simp [h,t.outside x h]
  have hi : IntegrableOn (fun _ : Position => (1:ℝ)) B :=
    integrableOn_const (isCompact_closedBall c R).measure_lt_top.ne
  have h := integral_mono_ae tr.mass.integrableOn hi (Filter.Eventually.of_forall fun x => (t.range x).2)
  rw [setIntegral_const,smul_eq_mul,mul_one,← integral_indicator measurableSet_closedBall,support] at h
  have vol : volume.real B = ballVolume R := by
    rw [Measure.real,Measure.addHaar_closedBall_eq_addHaar_ball]
    exact Measure.addHaar_real_ball_center volume c R
  have hv := ballVolume_scaled hR 1
  rw [mul_one] at hv
  exact h.trans_eq (vol.trans (hv.trans (mul_comm ..)))

private theorem window_weights {N : Density} {R p θ : ℝ} {S T : MatrixGradient} {c : Position}
    (reg : DensityRegular N p θ S T) (s : SmallBallScale N R c) (t : SpiralTaper (closedBall c R))
    (tr : FrozenTaperRegular t) :
    (s.r+s.r^2)*(∫ x, t.shape x) ≤ 4*(∫ x, t.shape x*(N.charge x+(N.charge x)^2)) ∧
    s.r*(∫ x in closedBall c R, ‖tr.grad x‖^2) ≤ 2*(∫ x in closedBall c R, N.charge x*‖tr.grad x‖^2) := by
  have mass := window_product_integrable t.range tr.shape.aemeasurable (reg.charge_L1.add reg.charge_L2.integrable_sq)
  have h := integral_mono (tr.mass.const_mul (s.r+s.r^2)) (mass.const_mul 4) fun x => by
    change (s.r+s.r^2)*t.shape x ≤ 4*(t.shape x*(N.charge x + (N.charge x)^2))
    by_cases hx : x ∈ closedBall c R
    · have a : s.r ≤ 2*N.charge x := by linarith only [s.comparable x hx]
      have a₂ := pow_le_pow_left₀ s.r_nonneg a 2
      have cap : s.r+s.r^2 ≤ 4*(N.charge x+(N.charge x)^2) := by nlinarith only [a,a₂,N.charge_nonneg x]
      nlinarith only [mul_le_mul_of_nonneg_right cap (t.range x).1]
    · simp [t.outside x hx]
  simp only [integral_const_mul] at h
  have fi := (integrable_indicator_iff measurableSet_closedBall).mp tr.fisher
  have cap : ∀ᵐ x ∂volume.restrict (closedBall c R), ‖N.charge x*‖tr.grad x‖^2‖ ≤ s.r*‖tr.grad x‖^2 := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (N.charge_nonneg x) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (s.cap x hx) (sq_nonneg _)
  have weighted : IntegrableOn (fun x => N.charge x*‖tr.grad x‖^2) (closedBall c R) :=
    (fi.const_mul s.r).mono' (reg.charge_L1.aestronglyMeasurable.restrict.mul fi.aestronglyMeasurable) cap
  have b := integral_mono_ae (fi.const_mul s.r) (weighted.const_mul 2) <| by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    have a : s.r ≤ 2*N.charge x := by linarith only [s.comparable x hx]
    nlinarith only [mul_le_mul_of_nonneg_right a (sq_nonneg ‖tr.grad x‖)]
  simp only [integral_const_mul] at b
  exact ⟨h,b⟩

/-- The five terms in the unaveraged remainder of Proposition 4.16. The geometric
length is the ball radius R. A fixed ratio between R and the tile side changes the constant. -/
def freeWindowError {c : Position} {R : ℝ} (t : SpiralTaper (closedBall c R)) (tr : FrozenTaperRegular t)
    (N : Density) (S T : MatrixGradient) (p θ ε r d : ℝ) : ℝ :=
  ε*(∫ x, t.shape x*(N.charge x+(N.charge x)^2)) + (∫ x in closedBall c R, N.charge x*‖tr.grad x‖^2) +
  (∫ x, t.shape x*kineticDensity S x)/ε + R^p*(∫ x in closedBall c R, rootPower T p x)/ε^(max p (3*θ*p-3)-1) +
  R^3*r*‖t.wavevector‖^2*(ε+d+d^2/ε)

private theorem window_final_bound {N : Density} {R p θ ε C M : ℝ} {S T : MatrixGradient} {c : Position}
    (H : FiniteEnergyInputs) (hC : 0 ≤ C) (hM : 0 ≤ M) (morrey : MatrixSobolevMorrey p M)
    (reg : DensityRegular N p θ S T) (s : SmallBallScale N R c) (t : SpiralTaper (closedBall c R))
    (tr : FrozenTaperRegular t) (hp : 3 < p) (hθ : 0 < θ) (hleθ : θ ≤ 1) (hpθ : 2 ≤ θ*p)
    (he : 0 < ε) (hle : ε ≤ 1) (hR : 0 < R) (power : Continuous (N.power θ)) (small : s.omega θ ≤ s.r^θ) :
    let V := ∫ x, t.shape x
    let J := ∫ x in closedBall c R, ‖tr.grad x‖^2
    let k := ∫ x, t.shape x*kineticDensity S x
    let d := s.omega (1/p)/s.r^(1/p)
    smallReplacementCost H C ε V J k ‖t.wavevector‖ s.r (3*s.omega 1) d p 0 ≤
      windowCoefficient H C p * (7+ballVolume 1+((6/θ)^(3/2:ℝ)+(6/θ)^2)*(4+ballVolume 1*M)) *
        freeWindowError t tr N S T p θ ε s.r d := by
  intro V J k d
  let b := 3*s.omega 1
  let r := s.r
  let Q := ‖t.wavevector‖
  let X := R^p*∫ x in closedBall c R, rootPower T p x
  let a := max p (3*θ*p-3)-1
  let G := ballVolume 1*M*X
  let U := R^3*r*Q^2*(ε+d+d^2/ε)
  let E := freeWindowError t tr N S T p θ ε r d
  have hp₀ : 0 < p := by linarith
  have hb : 0 ≤ b := mul_nonneg (by norm_num) (s.omega_nonneg 1 zero_lt_one)
  have hr := s.r_nonneg
  have hd : 0 ≤ d := div_nonneg (s.omega_nonneg _ (one_div_pos.mpr hp₀)) (Real.rpow_nonneg hr _)
  have hV : 0 ≤ V := integral_nonneg fun x => (t.range x).1
  have hJ : 0 ≤ J := integral_nonneg fun x => sq_nonneg _
  have hk : 0 ≤ k := integral_nonneg fun x => mul_nonneg (t.range x).1 (sq_nonneg _)
  have bv : 0 ≤ ballVolume 1 := (ballVolume_pos zero_lt_one).le
  have hA : 0 ≤ ∫ x in closedBall c R, rootPower T p x := integral_nonneg (rootPower_nonneg T p)
  have hX : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hR.le _) hA
  have hG : 0 ≤ G := mul_nonneg (mul_nonneg bv hM) hX
  have cap : b ≤ r := by dsimp [b,r]; linarith only [s.small,s.r_nonneg]
  have bd : b ≤ 3*p*(r*d) := by
    rcases hr.eq_or_lt with hz | pos
    · linarith only [cap,hz,mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hp₀.le) (mul_nonneg hr hd)]
    have o := s.omega_one_le _ (one_div_pos.mpr hp₀) ((div_le_one hp₀).2 (by linarith : 1 ≤ p))
    have split : r^(1-1/p) = r/r^(1/p) := by rw [Real.rpow_sub pos,Real.rpow_one]
    change s.omega 1 ≤ (1/(1/p)*r^(1-1/p))*s.omega (1/p) at o
    rw [split,one_div_div,div_one] at o
    calc
      _ ≤ 3*((p*(r/r^(1/p)))*s.omega (1/p)) := mul_le_mul_of_nonneg_left o (by norm_num)
      _ = _ := by dsimp only [d,r]; ring
  have vm := window_volume hR t tr
  change V ≤ ballVolume 1*R^3 at vm
  have mor : V*(s.omega θ)^p ≤ G := by
    obtain ⟨x,hx,y,hy,e⟩ := s.omega_max θ hθ
    have m := morrey.theta_pair hp reg power hR x hx y hy
    rw [← e] at m
    have w := mul_le_mul vm m (Real.rpow_nonneg (s.omega_nonneg θ hθ) _) (mul_nonneg bv (pow_nonneg hR.le _))
    have id : R^3*R^(p-3) = R^p := by rw [← Real.rpow_natCast, ← Real.rpow_add hR]; ring_nf
    calc
      _ ≤ _ := w
      _ = ballVolume 1*M*(R^3*R^(p-3))*(∫ z in closedBall c R, rootPower T p z) := by ring
      _ = _ := by rw [id]; dsimp only [G,X]; ring
  let m := ∫ x, t.shape x*(N.charge x+(N.charge x)^2)
  let j := ∫ x in closedBall c R, N.charge x*‖tr.grad x‖^2
  have mass0 : 0 ≤ m := integral_nonneg fun x => mul_nonneg (t.range x).1 (add_nonneg (N.charge_nonneg x) (sq_nonneg _))
  have taper0 : 0 ≤ j := integral_nonneg fun x => mul_nonneg (N.charge_nonneg x) (sq_nonneg _)
  have grad0 : 0 ≤ X/ε^a := div_nonneg hX (Real.rpow_nonneg he.le _)
  have kin0 := div_nonneg hk he.le
  have ph0 : 0 ≤ U := by dsimp only [U]; positivity
  have eq : E = ε*m+j+k/ε+X/ε^a+U := rfl
  have weights := window_weights reg s t tr
  have mass : ε*(r+r^2)*V ≤ 4*(ε*m) := by nlinarith only [mul_le_mul_of_nonneg_left weights.1 he.le]
  have Mₛ : ε*m ≤ E := by linarith only [eq,taper0,kin0,grad0,ph0]
  have Mₜ : j ≤ E := by linarith only [eq,mul_nonneg he.le mass0,kin0,grad0,ph0]
  have Mₖ : k/ε ≤ E := by linarith only [eq,mul_nonneg he.le mass0,taper0,grad0,ph0]
  have Mₓ : X/ε^a ≤ E := by linarith only [eq,mul_nonneg he.le mass0,taper0,kin0,ph0]
  have Mᵤ : U ≤ E := by linarith only [eq,mul_nonneg he.le mass0,taper0,kin0,grad0]
  have ph : (r*Q^2*V)*(ε+d+d^2/ε) ≤ ballVolume 1*E := by
    calc
      _ ≤ (r*Q^2*(ballVolume 1*R^3))*(ε+d+d^2/ε) := by gcongr
      _ = ballVolume 1*U := by dsimp [U]; ring
      _ ≤ _ := by gcongr
  let L := (6/θ)^(3/2:ℝ)+(6/θ)^2
  have zL : 0 ≤ L := by dsimp [L]; positivity
  have res := window_residual s hp hθ hleθ hpθ he hV hG small mor
  change V*(6*s.omega 1)*_ ≤ L*(ε*V*(r+r^2)+G/ε^a) at res
  have rem : (2*b*V)*(√(2*b/ε)+2*b/ε) ≤ L*((4+ballVolume 1*M)*E) := by
    have factor : 2*b = 6*s.omega 1 := by dsimp [b]; ring
    rw [factor,mul_comm (6*s.omega 1) V]
    apply res.trans (mul_le_mul_of_nonneg_left _ zL)
    have mx := mul_le_mul_of_nonneg_left Mₓ (mul_nonneg bv hM)
    calc
      _ = ε*(r+r^2)*V + (ballVolume 1*M)*(X/ε^a) := by dsimp only [G]; ring
      _ ≤ 4*E+(ballVolume 1*M)*E := add_le_add (mass.trans (mul_le_mul_of_nonneg_left Mₛ (by norm_num))) mx
      _ = _ := by ring
  have raw := window_scalar H hC (by linarith : 1 ≤ p) he hle hV hJ hk hr hb hd cap bd (Q := Q)
  apply raw.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (windowCoefficient_nonneg H hC hp₀.le)
  unfold windowControl
  have wJ : r*J ≤ 2*j := weights.2
  nlinarith only [mass,Mₛ,wJ,Mₜ,Mₖ,ph,rem]

/-- A local minority-density floor propagates to both comparison matrices. -/
theorem SmallBallMatrices.minority_on_ball {N : Density} {R : ℝ} {c : Position}
    {s : SmallBallScale N R c} (m : SmallBallMatrices s) (hR : 0 < R) {ν : ℝ}
    (hn : 0 ≤ ν) (hle : ν ≤ 1/2) (floor : ∀ x ∈ closedBall c R, (ν*N.charge x) • (1:SpinMatrix) ≤ N.matrix x) :
    (ν*s.r/8) • (1:SpinMatrix) ≤ m.low ∧ (ν*s.r/8) • (1:SpinMatrix) ≤ m.high := by
  have smul {a b : ℝ} (h : a ≤ b) : a • (1:SpinMatrix) ≤ b • (1:SpinMatrix) := by
    simpa only [inSpinFrame_const] using (inSpinFrame_mono (1 : unitary SpinMatrix)
      (a := fun _ => a) (b := fun _ => b) fun _ => h)
  have br {A lo hi} (branch : SmallAxisBranch s A lo hi) :
      (ν*s.r/8) • (1:SpinMatrix) ≤ lo ∧ (ν*s.r/8) • (1:SpinMatrix) ≤ hi := by
    cases branch with
    | shifted f =>
      have hc : c ∈ closedBall c R := mem_closedBall_self hR.le
      have comp := shifted_comparison N hc hc s.r_nonneg s.small (fun _ h _ k => s.matrix_osc h k) f
      have lt := smul (show ν*s.r/8 ≤ s.r/16 by linarith only [mul_le_mul_of_nonneg_right hle s.r_nonneg])
      exact ⟨lt.trans comp.1,lt.trans comp.2.2.2⟩
    | gapped _ _ X =>
      have hh := X.minority_at_peak c hn (show s.omega 1 ≤ s.r/4 by linarith only [s.small,s.r_nonneg])
        s.peak (fun _ h _ k => s.matrix_osc h k) floor
      have lt := smul (show ν*s.r/8 ≤ ν*s.r/2 by linarith only [mul_nonneg hn s.r_nonneg])
      exact ⟨lt.trans hh.1,lt.trans hh.2⟩
  exact br m.construction

/-- Proposition 4.16 on a regular density representative, before any integration over
centers or orientations. The matrices depend only on the density and the ball. The
same constant applies to all tapers, wavevectors and values of ε in the stated range. -/
theorem free_window_replacement {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {p θ C M : ℝ}
    (F : IslandFockInputs μ) (radii : ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → CoulombIslandRadii μ ι ε C)
    (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct) (sob : SobolevLipschitzComposition)
    (morrey : MatrixSobolevMorrey p M) (hM : 0 ≤ M) (hp : 3 < p) (hθ : 0 < θ) (hleθ : θ < 1) (hpθ : 2 ≤ θ*p)
    (hE : exteriorFormConstant F.oneBody ≤ C) (hI : F.oneBody.interiorConstant ≤ C) :
    ∃ A > 0, ∀ {N : Density} {S T : MatrixGradient} {R : ℝ} {c : Position},
      DensityRegular N p θ S T → Continuous N.matrix → (∀ z : ℝ, 0 < z → Continuous (N.power z)) →
      0 < R → SobolevCompositionOn (closedBall c R) → SmallPowerOscillation N θ (θ/64) R c →
      ∃ s : SmallBallScale N R c, ∃ m : SmallBallMatrices s, ∀ (t : SpiralTaper (closedBall c R)) (tr : FrozenTaperRegular t),
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      let E := A*freeWindowError t tr N S T p θ ε s.r (s.omega (1/p)/s.r^(1/p))
      energy (t.field N).matrix ≤ energy (cutoffSpiral t.shape m.low t.wavevector)+E ∧
      energy (cutoffSpiral t.shape m.high t.wavevector)-E ≤ energy (t.field N).matrix := by
  let V := ballVolume 1
  let L := (6/θ)^(3/2:ℝ)+(6/θ)^2
  let A := windowCoefficient F.oneBody C p * (7+V+L*(4+V*M))
  have hC := F.oneBody.interiorConstant_nonneg.trans hI
  have hV : 0 ≤ V := (ballVolume_pos zero_lt_one).le
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hp₀ : 0 ≤ p := by linarith
  have coef : 0 < windowCoefficient F.oneBody C p := by
    unfold windowCoefficient
    positivity [F.oneBody.interiorConstant_nonneg,F.oneBody.lo_nonneg]
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  intro N S T R c reg cont cp hR comp small
  obtain ⟨s,osc⟩ := smallBallScale_of_regular (N := N) Filter.EventuallyEq.rfl cont cp hR hθ hleθ.le le_rfl small
  obtain ⟨m⟩ := smallBallMatrices_nonempty s hR cont
  refine ⟨s,m,?_⟩
  intro t tr ε he heh E
  let d := s.omega (1/p)/s.r^(1/p)
  have normOsc := osc.trans (mul_le_of_le_one_left (Real.rpow_nonneg s.r_nonneg _) (by linarith : θ/64 ≤ 1))
  have err := window_final_bound F.oneBody hC hM morrey reg s t tr hp hθ hleθ.le hpθ he (by linarith) hR (cp θ hθ) normOsc
  have signs (σ : ℝ) (hs : σ=1 ∨ σ=-1) := m.free_window_raw F (radii ε he heh) leibniz chain sob comp hR
    reg cont (cp 1 zero_lt_one) t tr (by linarith) he (by linarith) hE hI σ hs
  have b : _ ≤ E := err
  have upper := signs 1 (Or.inl rfl)
  have lower := signs (-1) (Or.inr rfl)
  simp only [ite_true,one_mul] at upper
  norm_num only [neg_one_mul,reduceCtorEq,show (-1:ℝ)≠1 by norm_num, ite_false] at lower
  exact ⟨upper.trans (add_le_add le_rfl b),by linarith only [lower,b]⟩

end TSGA.ManyBody
