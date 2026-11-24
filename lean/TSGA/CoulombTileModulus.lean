import TSGA.CoulombRootRegularity
import TSGA.SpectralHolder

/-! # Gas error when freezing a matrix and wavevector on a tile

Two estimates of the same energy difference allow the density powers to use
the prescribed θ-oscillation and the spiral kinetic term to use the p-th root.
The latter term vanishes identically at zero frozen wavevector.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization
open scoped ComplexOrder

private theorem split_moduli {z B Q u v : ℝ} (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hu : z ≤ (B+Q)*u) (hv : z ≤ (B+Q)*v) : z ≤ B*u+Q*v := by
  rcases le_total u v with h | h
  · linarith only [hu,mul_le_mul_of_nonneg_left h hQ]
  · linarith only [hv,mul_le_mul_of_nonneg_left h hB]

private theorem matrix_eq_zero_of_trace_le_zero {M : SpinMatrix} (h : M.PosSemidef)
    (hle : M.trace.re ≤ 0) : M = 0 :=
  h.trace_eq_zero_iff.mp (Complex.ext (le_antisymm hle (RCLike.nonneg_iff.mp h.trace_nonneg).1)
    (RCLike.nonneg_iff.mp h.trace_nonneg).2)

private theorem same_matrix_at_vacuum {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hr : max A.trace.re B.trace.re = 0) : A = B :=
  (matrix_eq_zero_of_trace_le_zero hA ((le_max_left ..).trans_eq hr)).trans
    (matrix_eq_zero_of_trace_le_zero hB ((le_max_right ..).trans_eq hr)).symm

/-- The pointwise comparison entering the general small-oscillation branch
of Theorem 3.3. The second matrix may be the original field at a point,
and k its local phase gradient. -/
theorem coulomb_small_tile_modulus {η : Mollifier} {J K cLO : ℝ}
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ)
    (rate : FiniteRateTiling energy η K) (removal : SpiralRemovalTrials η J) (hc : 0 ≤ cLO)
    (lo : ∀ D : Density, ∀ Γ, feasible D.matrix Γ →
      -cLO * (∫ x, D.charge x^(4/3:ℝ)) ≤ indirectAt D.matrix Γ)
    {p θ : ℝ} (hp : 3 ≤ p) (hθ : 0 < θ) :
    ∃ C > 0, ∀ {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) (q k : Position),
      let r := max A.trace.re B.trace.re
      let d := fun a : ℝ => hilbertSchmidt (hA.1.cfc (fun t => t^a) - hB.1.cfc (fun t => t^a))/r^a
      |sswEnergy energy η A q - sswEnergy energy η B k| ≤ C *
        ((r^(4/3:ℝ)+r^(5/3:ℝ)) * (d θ)^(min 1 (1/(3*θ))) + r*‖q‖^2 * d (1/p)) +
        (2*K+1)*(B.trace.re^(7/6:ℝ)+B.trace.re^(4/3:ℝ)+B.trace.re*max ‖q‖ ‖k‖)*‖q-k‖ := by
  obtain ⟨P, hP, hroot⟩ := coulomb_ssw_root_lipschitz loc states rate removal hc lo hp
  obtain ⟨T, hT, hcube⟩ := coulomb_ssw_root_lipschitz loc states rate removal hc lo (le_refl (3:ℝ))
  obtain ⟨S, hS, hθcube⟩ := theta_to_cube_root hθ
  let C := max (T*S) P
  let gas := coulomb_sswGas η loc states
  have hC : 0 < C := hP.trans_le (le_max_right ..)
  refine ⟨C,hC,?_⟩
  intro A B hA hB q k
  let r := max A.trace.re B.trace.re
  let mass := r^(4/3:ℝ)+r^(5/3:ℝ)
  let phase := r*‖q‖^2
  let d := fun a : ℝ => hilbertSchmidt (hA.1.cfc (fun t => t^a) - hB.1.cfc (fun t => t^a))/r^a
  let u := (d θ)^(min 1 (1/(3*θ)))
  have hr : 0 ≤ r := (RCLike.nonneg_iff.mp hA.trace_nonneg).1.trans (le_max_left ..)
  have hm : 0 ≤ mass := add_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)
  have hz : 0 ≤ phase := mul_nonneg hr (sq_nonneg _)
  have hd (a) : 0 ≤ d a := div_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hr a)
  have hu : 0 ≤ u := Real.rpow_nonneg (hd θ) _
  apply (gas.compare_matrix_wavevector rate A B hB q k).trans
  apply add_le_add_left
  change _ ≤ C*(mass*u+phase*d (1/p))
  rcases hr.eq_or_lt with hzero | hr'
  · have he : sswEnergy energy η A q = sswEnergy energy η B q :=
      congrArg (fun M => sswEnergy energy η M q) (same_matrix_at_vacuum hA hB hzero.symm)
    rw [he, sub_self, abs_zero]
    exact mul_nonneg hC.le (add_nonneg (mul_nonneg hm hu) (mul_nonneg hz (hd _)))
  have hcub := hcube hA hB q hr'
  have hpr := hroot hA hB q hr'
  change _ ≤ T*(mass+phase)*d (1/3) at hcub
  change _ ≤ P*(mass+phase)*d (1/p) at hpr
  have hac := hθcube hA hB hr' (le_max_left ..) (le_max_right ..)
  change d (1/3) ≤ S*u at hac
  have h₁ : |sswEnergy energy η A q-sswEnergy energy η B q| ≤ (C*mass+C*phase)*u := calc
    _ ≤ T*(mass+phase)*(S*u) := hcub.trans (mul_le_mul_of_nonneg_left hac (mul_nonneg hT.le (add_nonneg hm hz)))
    _ = (T*S)*((mass+phase)*u) := by ring
    _ ≤ C*((mass+phase)*u) := mul_le_mul_of_nonneg_right (le_max_left ..) (mul_nonneg (add_nonneg hm hz) hu)
    _ = _ := by ring
  have h₂ : |sswEnergy energy η A q-sswEnergy energy η B q| ≤ (C*mass+C*phase)*d (1/p) := by
    rw [← mul_add]
    exact hpr.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right ..) (add_nonneg hm hz)) (hd _))
  exact (split_moduli (mul_nonneg hC.le hm) (mul_nonneg hC.le hz) h₁ h₂).trans_eq (by ring)

/-- With a positive minority fraction the bulk oscillation enters linearly.
The constant uses only the minority Lipschitz estimate and spectral calculus. -/
theorem coulomb_minority_tile_modulus {η : Mollifier} {K cLO : ℝ}
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ)
    (rate : FiniteRateTiling energy η K) (hc : 0 ≤ cLO)
    (lo : ∀ D : Density, ∀ Γ, feasible D.matrix Γ →
      -cLO * (∫ x, D.charge x^(4/3:ℝ)) ≤ indirectAt D.matrix Γ)
    {p θ ν : ℝ} (hp : 3 ≤ p) (hθ : 0 < θ) (hθ' : θ ≤ 1) (hν : 0 < ν) (hν' : ν ≤ 1/2) :
    ∃ C > 0, ∀ {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef),
      (A - ((ν*A.trace.re : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef →
      (B - ((ν*B.trace.re : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef → ∀ q k : Position,
      let r := max A.trace.re B.trace.re
      let d := fun a : ℝ => hilbertSchmidt (hA.1.cfc (fun t => t^a) - hB.1.cfc (fun t => t^a))/r^a
      |sswEnergy energy η A q - sswEnergy energy η B k| ≤ C *
        ((r^(4/3:ℝ)+r^(5/3:ℝ)) * d θ + r*‖q‖^2 * d (1/p)) +
        (2*K+1)*(B.trace.re^(7/6:ℝ)+B.trace.re^(4/3:ℝ)+B.trace.re*max ‖q‖ ‖k‖)*‖q-k‖ := by
  let L := (4*cLO+22*K+4)/ν
  let C := L * max (1/θ) p
  have hK := rate.one_le
  have hp' : 0 < p := by linarith
  have hL : 0 < L := div_pos (by linarith) hν
  have hC : 0 < C := mul_pos hL (hp'.trans_le (le_max_right ..))
  refine ⟨C, hC, ?_⟩
  intro A B hA hB amin bmin q k
  let r := max A.trace.re B.trace.re
  let mass := r^(4/3:ℝ)+r^(5/3:ℝ)
  let phase := r*‖q‖^2
  let d := fun a : ℝ => hilbertSchmidt (hA.1.cfc (fun t => t^a) - hB.1.cfc (fun t => t^a))/r^a
  have hr : 0 ≤ r := (RCLike.nonneg_iff.mp hA.trace_nonneg).1.trans (le_max_left ..)
  have hm : 0 ≤ mass := add_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)
  have hz : 0 ≤ phase := mul_nonneg hr (sq_nonneg _)
  have hd (a) : 0 ≤ d a := div_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hr _)
  apply ((coulomb_sswGas η loc states).compare_matrix_wavevector rate A B hB q k).trans
  apply add_le_add_left
  change _ ≤ C*(mass*d θ+phase*d (1/p))
  rcases hr.eq_or_lt with hzero | hr'
  · have he := congrArg (fun M => sswEnergy energy η M q) (same_matrix_at_vacuum hA hB hzero.symm)
    rw [he, sub_self, abs_zero]
    exact mul_nonneg hC.le (add_nonneg (mul_nonneg hm (hd _)) (mul_nonneg hz (hd _)))
  have hbase := coulomb_minority_lipschitz loc states rate hc lo hν hν' q hA hB amin bmin
  change _ ≤ L * rateGrowth r q * hilbertSchmidt (A-B) at hbase
  have hscale : mass + phase = r * rateGrowth r q := holderGrowth_eq hr' q
  have hnon : 0 ≤ rateGrowth r q := by unfold rateGrowth; positivity
  have one {P : SpinMatrix} (h : P.PosSemidef) : h.1.cfc (fun t => t^(1:ℝ)) = P := by
    simp only [Real.rpow_one]
    change h.1.cfc id = _
    rw [← h.1.cfc_eq, cfc_id ℝ P h.1.isSelfAdjoint]
  have bound (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1) (hmul : 1/a ≤ max (1/θ) p) :
      |sswEnergy energy η A q - sswEnergy energy η B q| ≤ (C*mass+C*phase)*d a := by
    have h := matrix_power_oscillation hA hB ha ha' hr (le_max_left ..) (le_max_right ..)
    rw [one hA, one hB, Real.rpow_sub hr', Real.rpow_one] at h
    calc
      _ ≤ L*rateGrowth r q * ((1/a*(r/r^a)) * _) :=
        hbase.trans (mul_le_mul_of_nonneg_left h (mul_nonneg hL.le hnon))
      _ = (L*(1/a)) * (mass+phase) * d a := by rw [hscale]; dsimp [d]; ring
      _ ≤ C*(mass+phase)*d a := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmul hL.le) (add_nonneg hm hz)) (hd a)
      _ = _ := by ring
  have h₁ := bound θ hθ hθ' (le_max_left ..)
  have h₂ := bound (1/p) (one_div_pos.mpr hp') ((div_le_one hp').mpr (by linarith))
    (by simp)
  exact (split_moduli (mul_nonneg hC.le hm) (mul_nonneg hC.le hz) h₁ h₂).trans_eq (by ring)

/-- In the global-root regime the same p-th root controls both terms. -/
theorem coulomb_root_tile_modulus {η : Mollifier} {J K cLO : ℝ}
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ)
    (rate : FiniteRateTiling energy η K) (removal : SpiralRemovalTrials η J) (hc : 0 ≤ cLO)
    (lo : ∀ D : Density, ∀ Γ, feasible D.matrix Γ →
      -cLO * (∫ x, D.charge x^(4/3:ℝ)) ≤ indirectAt D.matrix Γ)
    {p : ℝ} (hp : 3 ≤ p) :
    ∃ C > 0, ∀ {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) (q k : Position),
      let r := max A.trace.re B.trace.re
      |sswEnergy energy η A q - sswEnergy energy η B k| ≤ C * holderGrowth r q *
        (hilbertSchmidt (hA.1.cfc (fun t => t^(1/p:ℝ)) - hB.1.cfc (fun t => t^(1/p:ℝ))) / r^(1/p:ℝ)) +
        (2*K+1)*(B.trace.re^(7/6:ℝ)+B.trace.re^(4/3:ℝ)+B.trace.re*max ‖q‖ ‖k‖)*‖q-k‖ := by
  obtain ⟨C,hC,hroot⟩ := coulomb_ssw_root_lipschitz loc states rate removal hc lo hp
  refine ⟨C,hC,?_⟩
  intro A B hA hB q k r
  apply ((coulomb_sswGas η loc states).compare_matrix_wavevector rate A B hB q k).trans
  apply add_le_add_left
  have hr : 0 ≤ r := (RCLike.nonneg_iff.mp hA.trace_nonneg).1.trans (le_max_left ..)
  rcases hr.eq_or_lt with hz | hr'
  · have he := congrArg (fun M => sswEnergy energy η M q) (same_matrix_at_vacuum hA hB hz.symm)
    rw [he, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg hC.le (by unfold holderGrowth; positivity))
      (div_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hr _))
  exact hroot hA hB q hr'

end TSGA.ManyBody
