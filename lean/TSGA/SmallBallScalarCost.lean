import TSGA.SmallBallCostDefinitions
import TSGA.SmallBallMatrices
import TSGA.SmallBallPhase
import TSGA.ActualFrozenScale

/-! # Normalizing the island, rotation and finite-size costs on a small tile -/

noncomputable section
namespace TSGA.ManyBody
open TSGA.Localization SSW

/-- Coefficient after using common bounds for the unnormalized kinetic,
residual-charge, and wavevector errors. -/
def smallBallScalarCoefficient (H : FiniteEnergyInputs) (C a K p : ℝ) : ℝ :=
  let bg := 8*(1+2*a)+4
  let mixed := 8*(1+4*a)+4*(3*p+1)
  192*((12*C+2*C^2)*(3*(4+bg)+mixed+9) + 6*(H.interiorConstant+H.loCoeff+H.interiorConstant*bg)
    + 16*192^2 + 16*(96*p)^2 + 2) + 8*(K^2+K)*14

theorem smallBallScalarCoefficient_nonneg (H : FiniteEnergyInputs) {C a K p : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hK : 0 ≤ K) (hp : 0 ≤ p) :
    0 ≤ smallBallScalarCoefficient H C a K p := by
  unfold smallBallScalarCoefficient
  positivity [H.interiorConstant_nonneg, H.lo_nonneg]

private theorem density_power_le_one_add {ρ t : ℝ} (hr : 0 ≤ ρ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ρ^t ≤ 1+ρ := by
  rcases le_total ρ 1 with h | h
  · exact (Real.rpow_le_one hr h ht).trans (le_add_of_nonneg_right hr)
  · apply le_trans _ (le_add_of_nonneg_left (by norm_num : 0 ≤ (1:ℝ)))
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h ht'

private theorem frozen_size_bound {K ε r ρ E : ℝ} (q : Position)
    (hK : 0 ≤ K) (he : 0 ≤ ε) (hρ : 0 ≤ ρ) (cap : ρ ≤ 2*r)
    (mass : ε*(r+r^2) ≤ E) (kin : ε*r*‖q‖^2 ≤ E) :
    smallFrozenSizeCost K ε ρ q ≤ 8*(K^2+K)*14*E := by
  have hg₁ := density_power_le_one_add hρ (by norm_num : 0 ≤ (1/3:ℝ)) (by norm_num)
  have hg₂ := density_power_le_one_add hρ (by norm_num : 0 ≤ (2/3:ℝ)) (by norm_num)
  have hr : 0 ≤ r := by linarith
  have hq : 0 ≤ ‖q‖^2 := sq_nonneg _
  have hb : 2+ρ+rateGrowth ρ q ≤ 4+3*ρ+‖q‖^2 := by unfold rateGrowth; linarith only [hg₁,hg₂]
  have bound := mul_le_mul (mul_le_mul_of_nonneg_left cap he)
    (hb.trans (by linarith only [cap] : 4+3*ρ+‖q‖^2 ≤ 4+6*r+‖q‖^2))
    (by unfold rateGrowth; positivity) (mul_nonneg he (by positivity))
  have b : ε*ρ*(2+ρ+rateGrowth ρ q) ≤ 14*E := by
    nlinarith only [bound,kin,mass,mul_nonneg he hr]
  unfold smallFrozenSizeCost
  calc
    _ ≤ 8*(K^2+K)*(14*E) := mul_le_mul_of_nonneg_left b (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- One bound for the complete replacement and finite-size errors at either
taper. The coefficient is independent of the density, the tile and ε. -/
theorem smallBallScalarCost {N : Density} {c : Position} {ε : ℝ}
    (s : SmallBallScale N (3*ε⁻¹) c) (q : Position) (H : FiniteEnergyInputs)
    {C a K p v k ρ : ℝ} (hp : 1 ≤ p) (he : 0 < ε) (hle : ε ≤ 1)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hK : 0 ≤ K) (hv : 0 ≤ v) (hk : 0 ≤ k)
    (hρ : 0 ≤ ρ) (cap : ρ ≤ 2*s.r) :
    let r := s.r
    let dist := 3*s.omega 1
    let d := s.omega (1/p)/r^(1/p)
    192*ε^3*smallReplacementCost H C ε (ε⁻¹^3) (a*ε⁻¹^2) k ‖q‖ r dist d p v +
      smallFrozenSizeCost K ε ρ q ≤ smallBallScalarCoefficient H C a K p *
      (ε*(r+r^2)+smallBallPhaseCost r d ε v q+ε^3*k/ε+
        (2*dist)*(Real.sqrt (2*dist/ε)+2*dist/ε)) := by
  intro r dist d
  let Q := ‖q‖
  let V := ε⁻¹^3
  let J := a*ε⁻¹^2
  let kin := ε^3*k/ε
  let res := (2*dist)*(Real.sqrt (2*dist/ε)+2*dist/ε)
  let mass := ε*(r+r^2)
  let phase := smallBallPhaseCost r d ε v q
  let E := mass+phase+kin+res
  let bg := smallAffineCost V J k Q 1 (2*r)
  let mixed := smallAffineCost V J k Q ε⁻¹ (2*dist+ε*(2*r))
  let B := 8*(1+2*a)+4
  let M := 8*(1+4*a)+4*(3*p+1)
  have hr : 0 ≤ r := s.r_nonneg
  have hp₀ : 0 < p := by linarith
  have d₀ : 0 ≤ d := div_nonneg (s.omega_nonneg _ (one_div_pos.mpr hp₀)) (Real.rpow_nonneg hr _)
  have i₀ : 0 ≤ dist := mul_nonneg (by norm_num) (s.omega_nonneg _ zero_lt_one)
  have di : dist ≤ r := by dsimp only [dist,r]; linarith only [s.small,s.r_nonneg]
  have dr : dist ≤ 3*p*(r*d) := by
    rcases hr.eq_or_lt with hz | hpos
    · linarith only [di,hz, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hp₀.le) (mul_nonneg hr d₀)]
    have o := s.omega_one_le _ (one_div_pos.mpr hp₀) ((div_le_one hp₀).2 hp)
    have split : r^(1-1/p) = r/r^(1/p) := by rw [Real.rpow_sub hpos,Real.rpow_one]
    change s.omega 1 ≤ (1/(1/p)*r^(1-1/p))*s.omega (1/p) at o
    rw [split,one_div_div,div_one] at o
    calc
      _ ≤ 3*((p*(r/r^(1/p)))*s.omega (1/p)) := mul_le_mul_of_nonneg_left o (by norm_num)
      _ = _ := by dsimp only [d]; ring
  have k₀ : 0 ≤ kin := by dsimp only [kin]; positivity
  have x₀ : 0 ≤ mass := mul_nonneg he.le (add_nonneg hr (sq_nonneg _))
  have z₀ : 0 ≤ res := by dsimp only [res]; positivity
  have ph₀ : 0 ≤ phase := by dsimp only [phase,smallBallPhaseCost]; positivity
  have XM : mass ≤ E := by dsimp only [E]; linarith
  have XE : phase ≤ E := by dsimp only [E]; linarith
  have T : kin ≤ E := by dsimp only [E]; linarith
  have U : res ≤ E := by dsimp only [E]; linarith
  have A : ε*r ≤ E := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) he.le).trans XM
  have Qε : ε*r*Q^2 ≤ E := by
    have hq := mul_nonneg hr (sq_nonneg Q)
    dsimp only [phase,smallBallPhaseCost] at XE
    change r*Q^2*(ε+d+d^2/ε)+r*v^2/ε+(r+r^(4/3:ℝ))*v ≤ E at XE
    nlinarith only [XE,mul_nonneg hq d₀,mul_nonneg hq (div_nonneg (sq_nonneg d) he.le),
      div_nonneg (mul_nonneg hr (sq_nonneg v)) he.le, mul_nonneg (add_nonneg hr (Real.rpow_nonneg hr (4/3:ℝ))) hv]
  have Qd : r*Q^2*d ≤ E := by
    dsimp only [phase,smallBallPhaseCost] at XE
    change r*Q^2*(ε+d+d^2/ε)+r*v^2/ε+(r+r^(4/3:ℝ))*v ≤ E at XE
    nlinarith only [XE,mul_nonneg (mul_nonneg hr (sq_nonneg Q)) he.le,
      mul_nonneg (mul_nonneg hr (sq_nonneg Q)) (div_nonneg (sq_nonneg d) he.le),
      div_nonneg (mul_nonneg hr (sq_nonneg v)) he.le,mul_nonneg (add_nonneg hr (Real.rpow_nonneg hr (4/3:ℝ))) hv]
  have Qd₂ : r*Q^2*(d^2/ε) ≤ E := by
    dsimp only [phase,smallBallPhaseCost] at XE
    change r*Q^2*(ε+d+d^2/ε)+r*v^2/ε+(r+r^(4/3:ℝ))*v ≤ E at XE
    nlinarith only [XE,mul_nonneg (mul_nonneg hr (sq_nonneg Q)) he.le,
      mul_nonneg (mul_nonneg hr (sq_nonneg Q)) d₀,div_nonneg (mul_nonneg hr (sq_nonneg v)) he.le,
      mul_nonneg (add_nonneg hr (Real.rpow_nonneg hr (4/3:ℝ))) hv]
  have P : r*v^2/ε ≤ E := by
    dsimp only [phase,smallBallPhaseCost] at XE
    change r*Q^2*(ε+d+d^2/ε)+r*v^2/ε+(r+r^(4/3:ℝ))*v ≤ E at XE
    linarith only [XE,mul_nonneg (mul_nonneg hr (sq_nonneg Q))
      (add_nonneg (add_nonneg he.le d₀) (div_nonneg (sq_nonneg d) he.le)),
      mul_nonneg (add_nonneg hr (Real.rpow_nonneg hr (4/3:ℝ))) hv]
  have KT : ε^3*ε*k ≤ E := by
    have e : ε^3*ε*k=ε^2*kin := by dsimp only [kin]; field_simp
    rw [e]
    exact (mul_le_of_le_one_left k₀ (pow_le_one₀ he.le hle)).trans T
  have hm : ε*(ε*r) ≤ E := (mul_le_of_le_one_left (mul_nonneg he.le hr) hle).trans A
  have bgb : ε^3*ε*bg ≤ B*E := by
    calc
      _ = 8*(ε^3*ε*k + 2*a*(ε*(ε*r))) + 4*(ε*r*Q^2) := by
        dsimp only [bg,smallAffineCost,V,J]; field_simp; ring
      _ ≤ 8*(E+2*a*E)+4*E := by gcongr
      _ = _ := by dsimp only [B]; ring
  have idist : ε*dist ≤ E := (mul_le_mul_of_nonneg_left di he.le).trans A
  have qdist : Q^2*dist ≤ 3*p*E := by
    calc
      _ ≤ Q^2*(3*p*(r*d)) := mul_le_mul_of_nonneg_left dr (sq_nonneg _)
      _ = 3*p*(r*Q^2*d) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left Qd (by positivity)
  have mix : ε^3*mixed ≤ M*E := by
    calc
      _ = 8*(kin+2*a*(ε*dist+ε*(ε*r)))+4*(Q^2*dist+ε*r*Q^2) := by
        dsimp only [kin,mixed,smallAffineCost,V,J]; field_simp; ring
      _ ≤ 8*(E+2*a*(E+E))+4*(3*p*E+E) := by gcongr
      _ = _ := by dsimp only [M]; ring
  have sm : ε*(2*r+(2*r)^2) ≤ 4*E := by dsimp only [mass] at XM; nlinarith only [XM,mul_nonneg he.le hr]
  have hC' : 0 ≤ 12*C+2*C^2 := by positivity
  let I := H.interiorConstant
  let L := H.loCoeff
  have hI : 0 ≤ I := H.interiorConstant_nonneg
  have hL : 0 ≤ L := H.lo_nonneg
  have island : ε^3*smallAdditionCost C ε V J k Q r dist ≤ (12*C+2*C^2)*(3*(4+B)+M+9)*E := by
    calc
      _ = (12*C+2*C^2)*(3*(ε*(2*r+(2*r)^2)+ε^3*ε*bg)+ε^3*mixed+3*(2*(ε*dist)+res)) := by
        dsimp only [smallAdditionCost,bg,mixed,res,V]; field_simp; ring
      _ ≤ (12*C+2*C^2)*(3*(4*E+B*E)+M*E+3*(2*E+E)) := by gcongr
      _ = _ := by ring
  have base : 6*((I+L)*mass+I*(ε^3*ε*bg)) ≤ 6*(I+L+I*B)*E := by
    calc
      _ ≤ 6*((I+L)*E+I*(B*E)) := by gcongr
      _ = _ := by ring
  have gauge : 16*192^2*kin+16*(96*p)^2*(r*Q^2*(d^2/ε))+2*(r*v^2/ε) ≤
      (16*192^2+16*(96*p)^2+2)*E := by
    calc
      _ ≤ 16*192^2*E+16*(96*p)^2*E+2*E := by gcongr
      _ = _ := by ring
  have replacement : ε^3*smallReplacementCost H C ε V J k Q r dist d p v ≤
      ((12*C+2*C^2)*(3*(4+B)+M+9) + 6*(I+L+I*B) + 16*192^2 + 16*(96*p)^2 + 2)*E := by
    calc
      _ = ε^3*smallAdditionCost C ε V J k Q r dist + 6*((I+L)*mass+I*(ε^3*ε*bg)) +
          (16*192^2*kin+16*(96*p)^2*(r*Q^2*(d^2/ε))+2*(r*v^2/ε)) := by
            dsimp only [smallReplacementCost,bg,kin,mass,I,L,V]
            rw [show (96:ℝ)/(1/p)=96*p by field_simp]
            field_simp
            ring
      _ ≤ _ := by linarith only [island,base,gauge]
  have frozen := frozen_size_bound (E := E) q hK he.le hρ cap XM Qε
  change 192*ε^3*smallReplacementCost H C ε V J k Q r dist d p v + _ ≤ _*E
  unfold smallBallScalarCoefficient
  dsimp only
  linarith only [frozen, mul_le_mul_of_nonneg_left replacement (by norm_num : (0:ℝ) ≤ 192)]

end TSGA.ManyBody
