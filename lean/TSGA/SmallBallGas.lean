import TSGA.SmallBallGasFormula
import TSGA.SmallBallAlignment
import TSGA.SmallBallPhaseScale

/-! # Gas error for the signed frozen matrices and central wavevector -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization SSW Metric Set
open scoped ComplexOrder MatrixOrder

/-- The normalized power oscillation times the two bulk density powers. -/
def smallGasBulk (r ω b a : ℝ) : ℝ :=
  (r^(4/3:ℝ)+r^(5/3:ℝ))*(ω/r^b)^a

/-- A uniform coefficient for the gas error after replacing the local trace
by the maximum charge on the comparison ball. -/
def smallGasConstant (J K : ℝ) : ℝ := 400*J+2*(2*K+1)

private theorem normalized_power_le {b r t dist ω : ℝ} (hb : 0 < b) (hb' : b ≤ 1)
    (hr' : 0 < r) (hlo : r/2 ≤ t) (_dist₀ : 0 ≤ dist) (ω₀ : 0 ≤ ω)
    (h : dist ≤ 48*ω) :
    dist/t^b ≤ 96*(ω/r^b) := by
  have hr := hr'.le
  have ht : 0 < t := by linarith
  have hb2 : r^b ≤ 2*t^b := by
    have bound := Real.rpow_le_rpow hr (by linarith only [hlo] : r ≤ 2*t) hb.le
    rw [Real.mul_rpow (by norm_num) ht.le] at bound
    exact bound.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) hb')
      (Real.rpow_nonneg ht.le _))
  rw [← mul_div_assoc,div_le_div_iff₀ (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos hr' _)]
  calc
    _ ≤ (48*ω)*(2*t^b) := mul_le_mul h hb2 (Real.rpow_nonneg hr _) (by positivity)
    _ = _ := by ring

private theorem power_double {t r a : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (cap : t ≤ 2*r)
    (ha : 0 ≤ a) (ha' : a ≤ 2) : t^a ≤ 4*r^a := by
  have h := Real.rpow_le_rpow ht cap ha
  rw [Real.mul_rpow (by norm_num) hr] at h
  apply h.trans (mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr _))
  calc (2:ℝ)^a ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha'
       _ = 4 := by norm_num

variable {D N : Density} {η : Mollifier} {ε K p b a J : ℝ} {c : Position}
variable {s : SmallBallScale N (3*ε⁻¹) c} (m : SmallBallMatrices s)

/-- Pointwise gas modulus on the closed ball for either frozen matrix.
The maximum in the normalization of the gas modulus includes the local
trace and is therefore at least half the ball's charge scale. -/
theorem SmallBallMatrices.gas_value_le (mod : PhysicalTileModulus η)
    (law : SmallGasFormula mod p b a K J) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hp : 3 < p) (hb : 0 < b) (hb' : b ≤ 1) (ha : 0 < a) (ha' : a ≤ 1)
    (he : 0 < ε) (he' : ε ≤ 1) {φ : Phase} (hφ : φ.Regular p)
    {F : SpinMatrix} (hF : F.PosSemidef) (sel : F=m.low ∨ F=m.high)
    (x : Position) (hx : x ∈ closedBall c (3*ε⁻¹)) :
    let r := s.r
    let d := s.omega (1/p)/r^(1/p)
    let phase := smallBallPhaseCost r d ε (tilePhaseOscillation φ c ε⁻¹) (φ.grad c)
    |mod.value F (N.matrix x) hF (N.positive x) (φ.grad c) (φ.grad x)| ≤
      smallGasConstant J K * (smallGasBulk r (s.omega b) b a + phase) := by
  intro r d phase
  let q := φ.grad c
  let k := φ.grad x
  let v := tilePhaseOscillation φ c ε⁻¹
  let t := max F.trace.re (N.charge x)
  let dist := fun j : ℝ => hilbertSchmidt (hF.1.cfc (fun z => z^j)-N.power j x) / t^j
  let u := s.omega b/r^b
  have hp₀ : 0 < p := by linarith
  have hroot : 0 < 1/p := one_div_pos.mpr hp₀
  have hroot' : 1/p ≤ 1 := (div_le_one hp₀).2 (by linarith)
  have hr := s.r_nonneg
  have hρ := N.charge_nonneg x
  have ht : 0 ≤ t := hρ.trans (le_max_right ..)
  have cap : t ≤ 2*r := max_le (m.trace_range sel).2 ((s.cap x hx).trans (by dsimp [r]; linarith))
  have hfloor : r/2 ≤ t := (s.comparable x hx).trans (le_max_right ..)
  have rel (j : ℝ) (hj : 0 < j) (hj' : j ≤ 1) : dist j ≤ 96*(s.omega j/r^j) := by
    by_cases hz : r = 0
    · have hω : s.omega j = 0 := le_antisymm (by simpa [show s.r = r from rfl,hz,Real.zero_rpow hj.ne'] using s.omega_le j hj)
        (s.omega_nonneg j hj)
      have t0 : t = 0 := le_antisymm (by simpa [hz] using cap) ht
      simp [dist,t0,hz,hω,Real.zero_rpow hj.ne']
    exact normalized_power_le hj hj' (hr.lt_of_ne' hz) hfloor (Real.sqrt_nonneg _) (s.omega_nonneg j hj) (m.power hF sel hj hj' x hx)
  have dn (j : ℝ) : 0 ≤ dist j := div_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg ht _)
  have hu : 0 ≤ u := div_nonneg (s.omega_nonneg b hb) (Real.rpow_nonneg hr _)
  have hd : 0 ≤ d := div_nonneg (s.omega_nonneg _ hroot) (Real.rpow_nonneg hr _)
  obtain ⟨_,_,_,osc⟩ := tilePhaseOscillation_attained hφ c (inv_pos.mpr he)
  have hv : 0 ≤ v := (norm_nonneg _).trans (osc x hx)
  have hphase : r*‖q‖^2*d ≤ phase := by
    change _ ≤ r*‖q‖^2*(ε+d+d^2/ε)+r*v^2/ε+(r+r^(4/3:ℝ))*v
    have h := mul_le_mul_of_nonneg_left (show d ≤ ε+d+d^2/ε by linarith only [he,div_nonneg (sq_nonneg d) he.le])
      (mul_nonneg hr (sq_nonneg ‖q‖))
    exact (h.trans (le_add_of_nonneg_right (div_nonneg (mul_nonneg hr (sq_nonneg v)) he.le))).trans
      (le_add_of_nonneg_right (mul_nonneg (add_nonneg hr (Real.rpow_nonneg hr _)) hv))
  have ph₀ : 0 ≤ phase := (mul_nonneg (mul_nonneg hr (sq_nonneg ‖q‖)) hd).trans hphase
  let mass := r^(4/3:ℝ)+r^(5/3:ℝ)
  have m₀ : 0 ≤ mass := add_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)
  have dθ := Real.rpow_le_rpow (dn b) (rel b hb hb') ha.le
  rw [Real.mul_rpow (by norm_num) hu] at dθ
  have powBound : dist b^a ≤ 96*u^a := dθ.trans <| mul_le_mul_of_nonneg_right
    (Real.rpow_le_self_of_one_le (by norm_num) ha') (Real.rpow_nonneg hu _)
  have massBound : t^(4/3:ℝ)+t^(5/3:ℝ) ≤ 4*mass := by
    dsimp only [mass]
    rw [mul_add]
    exact add_le_add (power_double ht hr cap (by norm_num) (by norm_num))
      (power_double ht hr cap (by norm_num) (by norm_num))
  have hbulk := mul_le_mul massBound powBound (Real.rpow_nonneg (dn b) _) (mul_nonneg (by norm_num) m₀)
  have hkin := mul_le_mul (mul_le_mul_of_nonneg_right cap (sq_nonneg ‖q‖)) (rel _ hroot hroot') (dn _) (by positivity)
  have hw := wavevectorModulus_le_smallBallPhaseCost hρ (s.cap x hx) hd he he' (osc x hx)
  have hwc : 0 ≤ 2*K+1 := by linarith
  rw [law]
  change |J*((t^(4/3:ℝ)+t^(5/3:ℝ))*dist b^a + t*‖q‖^2*dist (1/p)) +
    (2*K+1)*(N.charge x^(7/6:ℝ)+N.charge x^(4/3:ℝ)+N.charge x*max ‖q‖ ‖k‖)*‖q-k‖| ≤ _
  have hw₀ : 0 ≤ N.charge x^(7/6:ℝ)+N.charge x^(4/3:ℝ)+N.charge x*max ‖q‖ ‖k‖ :=
    add_nonneg (add_nonneg (Real.rpow_nonneg hρ _) (Real.rpow_nonneg hρ _)) (mul_nonneg hρ (le_max_of_le_left (norm_nonneg _)))
  have hn₁ := add_nonneg (Real.rpow_nonneg ht (4/3:ℝ)) (Real.rpow_nonneg ht (5/3:ℝ))
  have hn₂ := mul_nonneg (mul_nonneg ht (sq_nonneg ‖q‖)) (dn (1/p))
  rw [abs_of_nonneg (add_nonneg (mul_nonneg hJ (add_nonneg (mul_nonneg hn₁ (Real.rpow_nonneg (dn b) a)) hn₂))
    (mul_nonneg (mul_nonneg hwc hw₀) (norm_nonneg _)))]
  change _ ≤ (400*J+2*(2*K+1))*(mass*u^a+phase)
  have hcomp : (t^(4/3:ℝ)+t^(5/3:ℝ))*dist b^a + t*‖q‖^2*dist (1/p) ≤
      384*(mass*u^a)+192*phase := by
    calc
      _ ≤ (4*mass)*(96*u^a)+(2*r*‖q‖^2)*(96*d) := add_le_add hbulk hkin
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left hphase (by norm_num : (0:ℝ)≤192)]
  have h := add_le_add (mul_le_mul_of_nonneg_left hcomp hJ) (mul_le_mul_of_nonneg_left hw hwc)
  have b₀ := mul_nonneg m₀ (Real.rpow_nonneg hu a)
  change _ ≤ 2*phase at hw
  rw [mul_assoc (2*K+1)]
  apply h.trans
  linarith only [mul_nonneg hJ b₀,mul_nonneg hJ ph₀,mul_nonneg hwc b₀]

private theorem gasValue_measurable {D : Density} {φ : Phase} (mod : PhysicalTileModulus η)
    (law : SmallGasFormula mod p b a K J) {F : SpinMatrix} (hF : F.PosSemidef) (q : Position)
    (hc : Continuous D.matrix) (hφ : Continuous φ.grad) (hb : Continuous (D.power b))
    (hg : Continuous (D.power (1/p))) :
    Measurable (fun x => mod.value F (D.matrix x) hF (D.positive x) q (φ.grad x)) := by
  let t := fun x => max F.trace.re (D.charge x)
  let dist := fun (j : ℝ) x => hilbertSchmidt (hF.1.cfc (fun z => z^j)-D.power j x)/t x^j
  have charge : Continuous D.charge := by unfold Density.charge; fun_prop
  have ht : Measurable t := (continuous_const.max charge).measurable
  have hs : Continuous hilbertSchmidt := by unfold hilbertSchmidt; fun_prop
  have mdist (j : ℝ) (hj : Continuous (D.power j)) : Measurable (dist j) :=
    (hs.comp (continuous_const.sub hj)).measurable.div (ht.pow_const j)
  have mb := mdist b hb
  have mg := mdist (1/p) hg
  have eq : (fun x => mod.value F (D.matrix x) hF (D.positive x) q (φ.grad x)) =
      (fun x => J*((t x^(4/3:ℝ)+t x^(5/3:ℝ))*(dist b x)^a+t x*‖q‖^2*dist (1/p) x) +
        (2*K+1)*(D.charge x^(7/6:ℝ)+D.charge x^(4/3:ℝ)+D.charge x*max ‖q‖ ‖φ.grad x‖)*‖q-φ.grad x‖) :=
    funext fun x => law F (D.matrix x) hF (D.positive x) q (φ.grad x)
  rw [eq]
  have hm := (ht.pow_const (4/3:ℝ)).add (ht.pow_const (5/3:ℝ))
  have hbulk := hm.mul (mb.pow_const a)
  have hkin := (ht.mul_const (‖q‖^2)).mul mg
  have hspeed := (charge.measurable.pow_const (7/6:ℝ)).add (charge.measurable.pow_const (4/3:ℝ))
  have hmax := (measurable_const (a := ‖q‖)).max hφ.norm.measurable
  have hdiff := ((continuous_const (y := q)).sub hφ).norm.measurable
  exact ((measurable_const (a := J)).mul (hbulk.add hkin)).add
    (((measurable_const (a := 2*K+1)).mul (hspeed.add (charge.measurable.mul hmax))).mul hdiff)

/-- The modulus can be integrated against either physical cutoff, using the
original input representative in the integrand. The exponent `a'` is the
one used subsequently in bulk interpolation. In the minority case it is
smaller than one and the normalized θ oscillation is small. -/
theorem SmallBallMatrices.gas_cutoff (mod : PhysicalTileModulus η)
    (law : SmallGasFormula mod p b a K J) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hp : 3 < p) (hb : 0 < b) (hb' : b ≤ 1) (ha : 0 < a) (ha' : a ≤ 1)
    (he : 0 < ε) (he' : ε ≤ 1) {φ : Phase} (hφ : φ.Regular p)
    (e : N.matrix =ᵐ[volume] D.matrix) (hc : Continuous N.matrix)
    (powers : ∀ z : ℝ, 0 < z → Continuous (N.power z))
    {F : SpinMatrix} (hF : F.PosSemidef) (sel : F=m.low ∨ F=m.high)
    (P : TileProfile) (support : ∀ x, P.cutoff (c-x) ≠ 0 → x ∈ closedBall c (3*ε⁻¹))
    {a' : ℝ} (exponent : a' = a ∨ (0 ≤ a' ∧ a' ≤ a ∧ s.omega b / s.r^b ≤ 1)) :
    let f := fun x => mod.value F (D.matrix x) hF (D.positive x) (φ.grad c) (φ.grad x)
    let r := s.r
    let d := s.omega (1/p)/r^(1/p)
    let phase := smallBallPhaseCost r d ε (tilePhaseOscillation φ c ε⁻¹) (φ.grad c)
    Integrable (fun x => f x*P.cutoff (c-x)) ∧
      cutoffAverage P.cutoff f c ≤ smallGasConstant J K*(smallGasBulk r (s.omega b) b a'+phase) := by
  intro f r d phase
  have hroot := one_div_pos.mpr (by linarith : 0 < p)
  have eq_point {A B : SpinMatrix} (ha : A.PosSemidef) (hb : B.PosSemidef) (h : A=B) (k : Position) :
      mod.value F A hF ha (φ.grad c) k = mod.value F B hF hb (φ.grad c) k := by subst B; rfl
  have eq : (fun x => mod.value F (N.matrix x) hF (N.positive x) (φ.grad c) (φ.grad x)) =ᵐ[volume] f :=
    e.mono fun x hx => eq_point _ _ hx _
  have hm := (gasValue_measurable mod law hF (φ.grad c) hc hφ.continuous_grad (powers _ hb) (powers _ hroot)).aestronglyMeasurable.congr eq
  have scale : 0 ≤ smallGasConstant J K := by unfold smallGasConstant; positivity
  have hu : 0 ≤ s.omega b/r^b := div_nonneg (s.omega_nonneg b hb) (Real.rpow_nonneg s.r_nonneg _)
  have pure : smallGasBulk r (s.omega b) b a ≤ smallGasBulk r (s.omega b) b a' := by
    rcases exponent with rfl|⟨h₁,h₂,h₃⟩
    · rfl
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge' hu h₃ h₁ h₂)
        (add_nonneg (Real.rpow_nonneg s.r_nonneg _) (Real.rpow_nonneg s.r_nonneg _))
  have estimate (x : Position) (hx : x ∈ closedBall c (3*ε⁻¹)) :=
    (m.gas_value_le mod law hJ hK hp hb hb' ha ha' he he' hφ hF sel x hx).trans
      (mul_le_mul_of_nonneg_left (add_le_add pure (le_refl phase)) scale)
  have center : c ∈ closedBall c (3*ε⁻¹) := mem_closedBall_self (by positivity)
  exact bounded_cutoff_integral P c hm ((abs_nonneg _).trans (estimate c center)) <| by
    filter_upwards [eq] with x hx
    intro hχ
    rw [← hx]
    exact estimate x (support x hχ)

/-- The common spectral floor for the actual minority modulus on the ball. -/
theorem SmallBallMatrices.minority_gas_domain (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (S : SobolevDifferenceQuotients)
    {θ ν : ℝ} (hp : 3 ≤ p) (hθ : 0 < θ) (hθ' : θ ≤ 1) (hν : 0 < ν) (hν' : ν ≤ 1/2)
    (minor : MinorityBound ν N) (e : N.matrix =ᵐ[volume] D.matrix)
    {F : SpinMatrix} (hF : F.PosSemidef) (sel : F=m.low ∨ F=m.high) :
    ∀ᵐ x, (L.minorityModulus H S hp hθ hθ' (div_pos hν (by norm_num : (0:ℝ)<16)) (by linarith)).domain F (D.matrix x) := by
  have frozen := m.minority_domain hν.le hν' minor hF sel
  filter_upwards [minor,e] with x hx he
  change (F - (((ν/16)*F.trace.re : ℝ) : ℂ) • (1:SpinMatrix)).PosSemidef ∧ _
  refine ⟨frozen, ?_⟩
  rw [← he]
  change (N.matrix x - (((ν/16)*N.charge x : ℝ) : ℂ) • (1:SpinMatrix)).PosSemidef
  rw [← Matrix.nonneg_iff_posSemidef,sub_nonneg]
  have hf := sub_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr hx)
  have hs : ν/16*N.charge x ≤ ν*N.charge x :=
    mul_le_mul_of_nonneg_right (by linarith only [hν]) (N.charge_nonneg x)
  apply le_trans _ hf
  change (ν/16*N.charge x) • (1:SpinMatrix) ≤ (ν*N.charge x) • (1:SpinMatrix)
  simpa only [inSpinFrame_const] using (inSpinFrame_mono (1 : unitary SpinMatrix)
    (a := fun _ => ν/16*N.charge x) (b := fun _ => ν*N.charge x) fun _ => hs)

end TSGA.ManyBody
