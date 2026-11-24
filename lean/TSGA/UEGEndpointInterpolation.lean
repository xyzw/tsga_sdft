import TSGA.ConditionalUEG
import TSGA.EndpointInterpolation
import TSGA.SmallBallGas

/-! # Minority occupation interpolation for the zero-wavevector Coulomb gas -/

noncomputable section
namespace TSGA.Localization
open Matrix
open scoped ComplexOrder

/-- Comparing normalized matrix powers at any two exponents, including
when either density has a zero eigenvalue. -/
theorem normalized_power_distance {u θ : ℝ} (hu : 0 < u) (hθ : 0 < θ) :
    ∃ C > 0, ∀ {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) {r : ℝ},
      0 < r → A.trace.re ≤ r → B.trace.re ≤ r →
      let D := fun s : ℝ => hilbertSchmidt (hA.1.cfc (fun t => t^s) - hB.1.cfc (fun t => t^s))
      D u / r^u ≤ C * (D θ / r^θ)^(min 1 (u/θ)) := by
  by_cases h : θ ≤ u
  · refine ⟨u/θ, div_pos hu hθ, ?_⟩
    intro A B hA hB r hr hrA hrB D
    rw [min_eq_left ((one_le_div hθ).2 h), Real.rpow_one]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hr _)).2
    have hx := matrix_power_oscillation hA hB hθ h hr.le hrA hrB
    change D u ≤ u/θ * (D θ / r^θ) * r^u
    apply hx.trans_eq
    rw [Real.rpow_sub hr]
    ring
  · let C := (2 : ℝ)^((1-u/θ)/2)
    refine ⟨C, Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
    intro A B hA hB r hr _ _ D
    have hut := (lt_of_not_ge h).le
    rw [min_eq_right ((div_le_one hθ).2 hut)]
    have hx := spectral_power_holder hA hB hu hut
    have hγ : θ*(u/θ) = u := by field_simp
    change D u / r^u ≤ C * (D θ / r^θ)^(u/θ)
    rw [Real.div_rpow (show 0 ≤ D θ from Real.sqrt_nonneg _) (Real.rpow_nonneg hr.le θ), ← Real.rpow_mul hr.le, hγ,
      ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hx (Real.rpow_nonneg hr.le _)

end TSGA.Localization

namespace TSGA.ManyBody
open TSGA.Localization SSW Matrix
open scoped ComplexOrder

/-- A power modulus measured in the fraction of the trace in the minority
spin channel. The linear case is the spin-flip endpoint conjecture. -/
def UEGPowerEndpointBound (η : Mollifier) (α C : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ t ∈ Set.Icc (0:ℝ) (1/2),
    uniformEnergy energy η (populations r 0) - uniformEnergy energy η (populations (r-t*r) (t*r)) ≤
      (C*(r^(4/3:ℝ)+r^(5/3:ℝ)))*t^α

private theorem minority_power_distance {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {α : ℝ} (hα : 0 ≤ α) :
    |(minorityPopulation hA)^α-(minorityPopulation hB)^α| ≤
      hilbertSchmidt (hA.1.cfc (fun x => x^α)-hB.1.cfc (fun x => x^α)) := by
  rcases spin_indices_same_order hA.1 hB.1 with ⟨h,k⟩ | ⟨h,k⟩
  · simpa only [minorityPopulation,min_eq_right h,min_eq_right k] using eigenvalue_power_distance hA hB hα 1
  · simpa only [minorityPopulation,min_eq_left h,min_eq_left k] using eigenvalue_power_distance hA hB hα 0

/-- At positive common trace r, an α endpoint law gives the matrix modulus
of order min(1,α/θ) in the θ-powers divided by r^θ. -/
theorem CoulombGasInputs.ueg_equal_trace_of_power_endpoint {η : Mollifier} {K α C θ : ℝ}
    (L : CoulombGasInputs η K) (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (endpoint : UEGPowerEndpointBound η α C) (hC : 0 ≤ C) (hα : 0 < α) (ha : α ≤ 1) (hθ : 0 < θ) :
    ∃ J > 0, ∀ {r : ℝ}, 0 < r → ∀ {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef),
      A.trace.re = r → B.trace.re = r →
      |uniformEnergy energy η A-uniformEnergy energy η B| ≤
        J*(r^(4/3:ℝ)+r^(5/3:ℝ))*
          (hilbertSchmidt (hA.1.cfc (fun x => x^θ)-hB.1.cfc (fun x => x^θ))/r^θ)^(min 1 (α/θ)) := by
  obtain ⟨Z,hZ,transfer⟩ := normalized_power_distance hα hθ
  refine ⟨(C+1)*Z/α,by positivity,?_⟩
  intro r hr A B hA hB trA trB
  let f := fun t : ℝ => uniformEnergy energy η (populations (r-t*r) (t*r))
  let w := r^(4/3:ℝ)+r^(5/3:ℝ)
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  obtain ⟨conv,symm,rep⟩ := L.population_curve H sob hr
  obtain ⟨a,ea⟩ := rep hA trA
  obtain ⟨b,eb⟩ := rep hB trB
  have epi (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (1/2)) : f 0-f t ≤ (C*w)*t^α := by
    simpa only [f,w,zero_mul,sub_zero] using endpoint r hr t ht
  have h := convex_minority_power hα ha (mul_nonneg hC hw) conv symm epi b a
  have apos : 0 ≤ minorityPopulation hA := le_min (hA.eigenvalues_nonneg _) (hA.eigenvalues_nonneg _)
  have bpos : 0 ≤ minorityPopulation hB := le_min (hB.eigenvalues_nonneg _) (hB.eigenvalues_nonneg _)
  have hd := minority_power_distance hA hB hα.le
  rw [Real.div_rpow apos hr.le,Real.div_rpow bpos hr.le,←sub_div,abs_div,abs_of_pos (Real.rpow_pos_of_pos hr α)] at h
  let D := fun u : ℝ => hilbertSchmidt (hA.1.cfc (fun x => x^u)-hB.1.cfc (fun x => x^u))
  have cost := (div_le_div_of_nonneg_right hd (Real.rpow_nonneg hr.le α)).trans
    (transfer hA hB hr trA.le trB.le)
  rw [ea,eb]
  change |f _-f _| ≤ (C+1)*Z/α*w*(D θ/r^θ)^(min 1 (α/θ))
  apply (h.trans (mul_le_mul_of_nonneg_left cost (div_nonneg (mul_nonneg hC hw) hα.le))).trans
  have pos : 0 ≤ (Z/α)*w*(D θ/r^θ)^(min 1 (α/θ)) :=
    mul_nonneg (mul_nonneg (div_nonneg hZ.le hα.le) hw)
      (Real.rpow_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hr.le _)) _)
  change C*w/α*(Z*(D θ/r^θ)^(min 1 (α/θ))) ≤ _
  calc
    _ = C*((Z/α)*w*(D θ/r^θ)^(min 1 (α/θ))) := by ring
    _ ≤ (C+1)*((Z/α)*w*(D θ/r^θ)^(min 1 (α/θ))) :=
      mul_le_mul_of_nonneg_right (by linarith) pos
    _ = _ := by ring

/-- Changing the trace along a ray gives the same normalized power modulus
for arbitrary positive semidefinite matrices of nonzero maximum trace. -/
theorem CoulombGasInputs.ueg_of_power_endpoint {η : Mollifier} {K α C θ : ℝ}
    (L : CoulombGasInputs η K) (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (endpoint : UEGPowerEndpointBound η α C) (hC : 0 ≤ C) (hα : 0 < α) (ha : α ≤ 1) (hθ : 0 < θ) :
    ∃ J > 0, ∀ {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef),
      let r := max A.trace.re B.trace.re
      0 < r → |sswEnergy energy η A 0-sswEnergy energy η B 0| ≤
        J*(r^(4/3:ℝ)+r^(5/3:ℝ))*
          (hilbertSchmidt (hA.1.cfc (fun x => x^θ)-hB.1.cfc (fun x => x^θ))/r^θ)^(min 1 (α/θ)) := by
  obtain ⟨J,hJ,pop⟩ := L.ueg_equal_trace_of_power_endpoint H sob endpoint hC hα ha hα
  let p := 1/α
  let R := 2*(H.loCoeff+2*K)+2*(2*K+1)
  have hk := L.rate.one_le
  have hp : 1 ≤ p := (one_le_div hα).2 ha
  have R₀ : 0 ≤ R := by dsimp only [R]; linarith only [hk,H.lo_nonneg]
  have exponent : 1/p = α := by simp [p]
  let e := fun A => sswEnergy energy η A (0:Position)
  have fix {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
      (hr : 0 < A.trace.re) (eq : A.trace.re = B.trace.re) := pop hr hA hB rfl eq.symm
  have fixed {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
      (hr : 0 < A.trace.re) (eq : A.trace.re = B.trace.re) :
      |e A-e B| ≤ J*(holderGrowth A.trace.re 0/A.trace.re^(1/p:ℝ))*
        hilbertSchmidt (hA.1.cfc (fun t => t^(1/p:ℝ))-hB.1.cfc (fun t => t^(1/p:ℝ))) := by
    have h := fix hA hB hr eq
    rw [div_self hα.ne',min_self,Real.rpow_one] at h
    simp only [e,sswEnergy_zero_wavevector,holderGrowth,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,exponent]
    exact h.trans_eq (by ring)
  let states := L.kinematics H sob
  let gas := coulomb_sswGas η L.localization states
  have ray {A : SpinMatrix} (hA : A.PosSemidef) {b : ℝ} (b0 : 0 ≤ b) (b1 : b ≤ 1) :
      |e (b • A)-e A| ≤ R*(1-b)*holderGrowth A.trace.re 0 := by
    have h := gas.ray_lipschitz L.rate H.lo_nonneg hA 0 b0 b1
      (ssw_scaling gas H.lo_nonneg H.indirect_lower A hA 0
        (fun n => SpiralKinematics.representable states A hA n 0) b0 b1)
    simpa only [R,e,holderGrowth] using h
  let T := J*(1+4*p)+2*p*R
  have pp : 0 < p := zero_lt_one.trans_le hp
  have hT : 0 < T := by dsimp only [T]; positivity
  obtain ⟨Z,hZ,transfer⟩ := normalized_power_distance hα hθ
  refine ⟨T*Z,mul_pos hT hZ,?_⟩
  intro A B hA hB r hr
  have h := root_lipschitz_of_equal_charge_of_one_le e (0:Position) hp hJ.le R₀
    (fun {_ _} hP hQ hpos eq => fixed hP hQ hpos eq) (fun {_} hP {_} hb h1 => ray hP hb h1) hA hB hr
  let w := r^(4/3:ℝ)+r^(5/3:ℝ)
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  change |e A-e B| ≤ T*holderGrowth r 0*(_/r^(1/p)) at h
  simp only [holderGrowth,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,exponent] at h
  have hi := transfer hA hB hr (le_max_left ..) (le_max_right ..)
  exact (h.trans (mul_le_mul_of_nonneg_left hi (mul_nonneg hT.le hw))).trans_eq (by ring)

/-- The physical comparison matrix and local density obey the interpolated
gas modulus on a small ball, including a ball of zero charge. -/
theorem CoulombGasInputs.ueg_small_ball_of_power_endpoint {η : Mollifier} {K α C θ : ℝ}
    (L : CoulombGasInputs η K) (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (endpoint : UEGPowerEndpointBound η α C) (hC : 0 ≤ C) (hα : 0 < α) (ha : α ≤ 1)
    (hθ : 0 < θ) (hθ' : θ ≤ 1) :
    ∃ J > 0, ∀ {N : Density} {R : ℝ} {c : Position} {s : SmallBallScale N R c} (m : SmallBallMatrices s)
      {F : SpinMatrix} (_hF : F.PosSemidef), F=m.low ∨ F=m.high →
      ∀ x ∈ Metric.closedBall c R, |sswEnergy energy η F 0-sswEnergy energy η (N.matrix x) 0| ≤
        J*smallGasBulk s.r (s.omega θ) θ (min 1 (α/θ)) := by
  obtain ⟨J,hJ,law⟩ := L.ueg_of_power_endpoint H sob endpoint hC hα ha hθ
  refine ⟨384*J,by positivity,?_⟩
  intro N R c s m F hF sel x hx
  let r := s.r
  let t := max F.trace.re (N.charge x)
  let a := min 1 (α/θ)
  let u := s.omega θ/r^θ
  let d := hilbertSchmidt (hF.1.cfc (fun z => z^θ)-N.power θ x)
  have hr : 0 ≤ r := s.r_nonneg
  have ht : 0 ≤ t := (N.charge_nonneg x).trans (le_max_right ..)
  have lo : r/2 ≤ t := (s.comparable x hx).trans (le_max_right ..)
  have cap : t ≤ 2*r := max_le (m.trace_range sel).2 ((s.cap x hx).trans (by linarith))
  have hu : 0 ≤ u := div_nonneg (s.omega_nonneg _ hθ) (Real.rpow_nonneg hr _)
  have a₀ : 0 < a := lt_min zero_lt_one (div_pos hα hθ)
  have d₀ : 0 ≤ d := Real.sqrt_nonneg _
  rcases hr.eq_or_lt with hz | pos
  · have tz : t = 0 := le_antisymm (by linarith only [cap,hz]) ht
    have zero {A : SpinMatrix} (P : A.PosSemidef) (ha : A.trace.re ≤ t) : A=0 :=
      P.trace_eq_zero_iff.mp (Complex.ext (le_antisymm (ha.trans_eq tz) (RCLike.nonneg_iff.mp P.trace_nonneg).1)
        (RCLike.nonneg_iff.mp P.trace_nonneg).2)
    rw [zero hF (le_max_left ..),zero (N.positive x) (le_max_right ..),sub_self,abs_zero]
    change 0 ≤ (384*J)*((r^(4/3:ℝ)+r^(5/3:ℝ))*u^a)
    positivity
  have tp : 0 < t := by linarith
  have power (b : ℝ) (b0 : 0 ≤ b) (b2 : b ≤ 2) : t^b ≤ 4*r^b := by
    have h := Real.rpow_le_rpow ht cap b0
    rw [Real.mul_rpow (by norm_num) hr] at h
    have p2 : (2:ℝ)^b ≤ 4 := (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) b2).trans_eq (by norm_num)
    exact h.trans (mul_le_mul_of_nonneg_right p2 (Real.rpow_nonneg hr _))
  have grow : t^(4/3:ℝ)+t^(5/3:ℝ) ≤ 4*(r^(4/3:ℝ)+r^(5/3:ℝ)) := by
    rw [mul_add]
    exact add_le_add (power _ (by norm_num) (by norm_num)) (power _ (by norm_num) (by norm_num))
  have double : r^θ ≤ 2*t^θ := by
    have v := Real.rpow_le_rpow hr (by linarith only [lo] : r ≤ 2*t) hθ.le
    rw [Real.mul_rpow (by norm_num) ht] at v
    exact v.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) hθ') (Real.rpow_nonneg ht _))
  have du : d/t^θ ≤ 96*u := by
    change _ ≤ 96*(s.omega θ/r^θ)
    rw [←mul_div_assoc,div_le_div_iff₀ (Real.rpow_pos_of_pos tp _) (Real.rpow_pos_of_pos pos _)]
    exact (mul_le_mul (m.power hF sel hθ hθ' x hx) double (Real.rpow_nonneg hr _) (by positivity [s.omega_nonneg θ hθ])).trans_eq (by ring)
  have dn := div_nonneg d₀ (Real.rpow_nonneg ht θ)
  have osc := Real.rpow_le_rpow dn du a₀.le
  rw [Real.mul_rpow (by norm_num) hu] at osc
  have bound := osc.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ) ≤ 96) (show a ≤ 1 from min_le_left ..)) (Real.rpow_nonneg hu _))
  have le := mul_le_mul grow bound (Real.rpow_nonneg dn _) (by positivity)
  have h := law hF (N.positive x) tp
  change _ ≤ J*(t^(4/3:ℝ)+t^(5/3:ℝ))*(d/t^θ)^a at h
  rw [mul_assoc] at h
  exact (h.trans (mul_le_mul_of_nonneg_left le hJ.le)).trans_eq (by change _ = 384*J*((r^(4/3:ℝ)+r^(5/3:ℝ))*u^a); ring)

end TSGA.ManyBody
