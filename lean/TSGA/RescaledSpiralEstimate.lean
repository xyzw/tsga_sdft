import TSGA.RescaledSpiralFields
import TSGA.ErrorDensity

/-! # Particle-number scaling at a fixed local spin wavevector -/

noncomputable section
namespace TSGA
open MeasureTheory TSGA.Localization PhaseLocalization

/-- The unscaled error integrals. The last argument permits the additional
global matrix-root integral in the alternative estimate. -/
def spiralProfileError (D : Density) (φ : Phase) (S T G : MatrixGradient) (p extra : ℝ) : ℝ :=
  (∫ x, massDensity D φ x) + (∫ x, kineticDensity S x) + (∫ x, rootPower T p x) +
    (∫ x, phaseDensity D φ G p x) + extra

/-- With the wavevector held fixed, the reference energy scales by exactly
the particle number. -/
def ParticleSpiralEstimate (F : GasEnergies) (D : Density) (φ : Phase)
    (S T G : MatrixGradient) (p C extra : ℝ) : Prop :=
  ∀ N : ℝ, 1 ≤ N →
    let L := N^(1/3:ℝ)
    |F.energy (fun x => rotate ((φ.spiralDilate L).value x) ((D.particleScale N).matrix x)) -
      N*(∫ x, F.ssw (D.matrix x) (φ.grad x))| ≤ C*N^(5/6:ℝ)*spiralProfileError D φ S T G p extra

private theorem particle_spiral_bound (F : GasEnergies) (D : Density) (φ : Phase)
    (S T G : MatrixGradient) {p C N extra : ℝ} (hN : 1 ≤ N) (hC : 0 ≤ C) (hx : 0 ≤ extra)
    (phase : PhaseAdmissible D p φ G) :
    let L := N^(1/3:ℝ)
    let ε := N^(-(1/6):ℝ)
    let dn := D.dilate L
    let pn := φ.spiralDilate L
    let x := F.energy (fun x => rotate (pn.value x) (dn.matrix x))
    |x - ∫ z, F.ssw (dn.matrix z) (pn.grad z)| ≤
      tsgaError dn pn (dilatedGradient S L) (dilatedGradient T L) (dilatedGradient G L) p (2*p-1) C ε +
      C/ε^(2*p-1)*(L^(3-p)*extra) →
    |x - N*(∫ z, F.ssw (D.matrix z) (φ.grad z))| ≤
      (1+2*C)*N^(5/6:ℝ)*spiralProfileError D φ S T G p extra := by
  intro L ε dn pn x bound
  have hN₀ := zero_lt_one.trans_le hN
  have hL : 0 < L := Real.rpow_pos_of_pos hN₀ _
  have he : 0 < ε := Real.rpow_pos_of_pos hN₀ _
  have he' : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  let n := N^(5/6:ℝ)
  let a := ∫ y, massDensity D φ y
  let k := ∫ y, kineticDensity S y
  let t := ∫ y, rootPower T p y
  let h := ∫ y, D.charge y*φ.hessianNorm y^p
  let u := ∫ y in φ.active, ‖φ.grad y‖^2 * matrixGradNorm G y^p
  have ha : 0 ≤ a := integral_nonneg (massDensity_nonneg D φ)
  have hk : 0 ≤ k := integral_nonneg fun _ => sq_nonneg _
  have ht : 0 ≤ t := integral_nonneg (rootPower_nonneg _ _)
  have hh : 0 ≤ h := integral_nonneg fun z => mul_nonneg (D.charge_nonneg z) (Real.rpow_nonneg (Real.sqrt_nonneg _) p)
  have hu : 0 ≤ u := integral_nonneg fun z => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) p)
  have hn : 0 ≤ n := Real.rpow_nonneg hN₀.le _
  have volume : ε*N = n := by
    dsimp only [ε,n]
    rw [← Real.rpow_add_one hN₀.ne']
    norm_num
  have power : C/ε^(2*p-1)*L^(3-p) = C*n := by
    dsimp only [ε,L,n]
    rw [← Real.rpow_mul hN₀.le,← Real.rpow_mul hN₀.le,
      div_eq_mul_inv, ← Real.rpow_neg hN₀.le, mul_assoc,← Real.rpow_add hN₀]
    congr 2
    ring
  have kinetic : C*(1+ε)/ε*L^(3-(2:ℝ)) ≤ 2*C*n := by
    have e : ε⁻¹*L^(3-(2:ℝ)) ≤ n := by
      dsimp only [ε,L,n]
      rw [← Real.rpow_neg hN₀.le,← Real.rpow_mul hN₀.le,← Real.rpow_add hN₀]
      exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    rw [div_eq_mul_inv,mul_assoc]
    exact mul_le_mul (by nlinarith only [mul_le_mul_of_nonneg_left he' hC]) e (by positivity) (by positivity)
  have href : (∫ y, F.ssw (dn.matrix y) (pn.grad y)) = N*∫ y, F.ssw (D.matrix y) (φ.grad y) :=
    integral_particleScale hN₀ (fun y => F.ssw (D.matrix y) (φ.grad y))
  have hm : (∫ y, dn.charge y + dn.charge y^2 + dn.charge y*‖pn.grad y‖^2) = N*a :=
    integral_particleScale hN₀ (massDensity D φ)
  have hk' : (∫ y, matrixGradNorm (dilatedGradient S L) y ^ 2) = L^(3-(2:ℝ))*k := by
    simpa only [k,kineticDensity,Real.rpow_two] using integral_dilatedGradient S 2 hL
  have bulk := integral_dilatedGradient T p hL
  change _ = L^(3-p)*t at bulk
  have hess := integral_spiral_curvature D φ p hL
  have active := integral_spiral_weightedRoot φ G p hL
  rw [href,tsgaError,hm,hk',bulk,hess,active] at bound
  have hphase : (∫ y, phaseDensity D φ G p y) = h+u := integral_phaseDensity phase
  have k_le := mul_le_mul_of_nonneg_right kinetic hk
  calc
    _ ≤ n*a + 2*C*n*k + C*n*(t+h+u+extra) := by
      apply bound.trans
      change ε*(N*a)+C*(1+ε)/ε*(L^(3-(2:ℝ))*k)+C/ε^(2*p-1)*(L^(3-p)*t)+
        C/ε^(2*p-1)*(L^(3-p)*h + L^(3-p)*u) + C/ε^(2*p-1)*(L^(3-p)*extra) ≤ _
      rw [← mul_add (L^(3-p)),← mul_assoc ε,volume,← mul_assoc (C/ε^(2*p-1)),power,
        ← mul_assoc (C/ε^(2*p-1)),power,← mul_assoc (C/ε^(2*p-1)),power]
      linarith only [k_le]
    _ ≤ _ := by
      dsimp only [spiralProfileError]
      rw [hphase]
      change _ ≤ (1+2*C)*n*(a+k+t+(h+u)+extra)
      nlinarith only [mul_nonneg (mul_nonneg hC hn) ha,mul_nonneg hn hk,
        mul_nonneg (mul_nonneg (show 0 ≤ 1+C by linarith) hn) (by linarith : 0 ≤ t+h+u+extra)]

/-- The order N^(5/6) error in the fixed-wavevector illustration, with one
coefficient at fixed p for the full range of θ in the global-root bound. -/
theorem MainTSGAEstimate.particle_spiral_sharp {F : GasEnergies} (H : MainTSGAEstimate F)
    {p : ℝ} (hp : 3 < p) : ∃ A > 0, ∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p*θ →
    ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular D p θ S T →
      IsMatrixGradientOn Set.univ (D.power (1/p)) G → MemLp (matrixGradNorm G) (ENNReal.ofReal p) →
      PhaseAdmissible D p φ G → ParticleSpiralEstimate F D φ S T G p A (∫ x, rootPower G p x) := by
  obtain ⟨C,hC,est⟩ := H.sharp p hp
  refine ⟨1+2*C,by positivity,?_⟩
  intro θ hθ hθ' hpθ D φ S T G reg weak lp phase N hN L
  have hN₀ := zero_lt_one.trans_le hN
  have hL : 0 < L := Real.rpow_pos_of_pos hN₀ _
  apply particle_spiral_bound F D φ S T G hN hC.le (integral_nonneg (rootPower_nonneg _ _)) phase
  have scaled := (est θ hθ hθ' hpθ (D.dilate L) (dilatedGradient S L) (dilatedGradient T L) (dilatedGradient G L)
    (reg.dilate hL) (fun i j k => (weak i j k).dilate hL) (dilatedGradient_memLp G hL lp)
    (φ.spiralDilate L) (phase.spiralDilate hL) (N^(-(1/6):ℝ)) (Real.rpow_pos_of_pos hN₀ _)).2
  rwa [integral_dilatedGradient G p hL] at scaled

/-- For θ ≤ 1/3 the same order follows from the general estimate, including
profiles for which only the phase-weighted matrix-root integral is finite. -/
theorem MainTSGAEstimate.particle_spiral_general {F : GasEnergies} (H : MainTSGAEstimate F)
    {p θ : ℝ} (hp : 3 < p) (hθ : 0 < θ) (hle : θ ≤ 1/3) (hpθ : 2 ≤ p*θ) :
    ∃ A > 0, ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular D p θ S T →
      PhaseAdmissible D p φ G → ParticleSpiralEstimate F D φ S T G p A 0 := by
  obtain ⟨C,hC,est⟩ := H.general p θ hp hθ (by linarith) hpθ
  rw [(bulkExponent_eq_two_mul_sub_one_iff (by linarith : 0<p)).2 hle] at est
  refine ⟨1+2*C,by positivity,?_⟩
  intro D φ S T G reg phase N hN L
  have hN₀ := zero_lt_one.trans_le hN
  have hL : 0 < L := Real.rpow_pos_of_pos hN₀ _
  apply particle_spiral_bound F D φ S T G hN hC.le le_rfl phase
  have scaled := (est (D.dilate L) (dilatedGradient S L) (dilatedGradient T L) trivial (reg.dilate hL)
    (φ.spiralDilate L) (dilatedGradient G L) (phase.spiralDilate hL) (N^(-(1/6):ℝ))
    (Real.rpow_pos_of_pos hN₀ _)).2
  simpa only [mul_zero,add_zero] using scaled

end TSGA
