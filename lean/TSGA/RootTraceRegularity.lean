import TSGA.ComparisonMatrices
import TSGA.HolderRegularity

/-! # Passing from fixed charge to arbitrary charge in the matrix-root estimate

Scale the higher-trace matrix to the smaller trace. The trace difference is
controlled by the root difference via the spectral power estimate. This also
bounds the cost of moving along the ray when the smaller matrix is vacuum.
-/

noncomputable section
namespace TSGA.SSW
open TSGA.Localization
open scoped ComplexOrder Matrix.Norms.Frobenius

private theorem frame_scale (U : unitary SpinMatrix) (v : Fin 2 → ℝ) (a : ℝ) :
    a • inSpinFrame U v = inSpinFrame U (fun i => a*v i) := by
  have h : a • Matrix.diagonal (fun i => (v i : ℂ)) = Matrix.diagonal (fun i => ((a*v i : ℝ) : ℂ)) := by
    ext i j
    by_cases hi : i = j
    · subst j
      simp [Matrix.smul_apply, Complex.real_smul]
    · simp [hi, Matrix.diagonal_apply_ne]
  change a • ((U : SpinMatrix) * _ * (star U : SpinMatrix)) = (U : SpinMatrix) * _ * (star U : SpinMatrix)
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]

theorem positive_power_smul {A : SpinMatrix} (hA : A.PosSemidef) {b : ℝ} (hb : 0 ≤ b) (a : ℝ) :
    (hA.smul hb).1.cfc (fun t => t^a) = b^a • hA.1.cfc (fun t => t^a) := by
  let U := hA.1.eigenvectorUnitary
  let v := hA.1.eigenvalues
  have hspec : A = inSpinFrame U v := hA.1.spectral_theorem
  have he : b • A = inSpinFrame U (fun i => b*v i) := by rw [hspec, frame_scale]
  have hcfc {X Y : SpinMatrix} (heq : X = Y) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
      hX.cfc (fun t => t^a) = hY.cfc (fun t => t^a) := by subst Y; rfl
  have hfr : (inSpinFrame U (fun i => b*v i)).IsHermitian :=
    (inSpinFrame_pos U fun i => mul_nonneg hb (hA.eigenvalues_nonneg i)).1
  rw [hcfc he (hA.smul hb).1 hfr, inSpinFrame_cfc]
  change _ = b^a • inSpinFrame U (fun i => v i ^ a)
  rw [frame_scale]
  exact congrArg (inSpinFrame U) (funext fun i => Real.mul_rpow hb (hA.eigenvalues_nonneg i))

private theorem root_norm {B : SpinMatrix} (hB : B.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    hilbertSchmidt (hB.1.cfc (fun t => t^a)) ≤ 2*B.trace.re^a := by
  let U := hB.1.eigenvectorUnitary
  let v := hB.1.eigenvalues
  have hb (i : Fin 2) : 0 ≤ v i := hB.eigenvalues_nonneg i
  have ht : B.trace.re = v 0 + v 1 := (inSpinFrame_trace U v) ▸ congrArg (fun P : SpinMatrix => P.trace.re) hB.1.spectral_theorem
  have hr : 0 ≤ B.trace.re := (RCLike.nonneg_iff.mp hB.trace_nonneg).1
  have h (i : Fin 2) : v i^a ≤ B.trace.re^a := Real.rpow_le_rpow (hb i)
    (by
      rw [ht]
      fin_cases i
      · exact le_add_of_nonneg_right (hb 1)
      · exact le_add_of_nonneg_left (hb 0)) ha
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (Real.rpow_nonneg hr _))).1
  change hilbertSchmidt (inSpinFrame U (fun i => v i^a)) ^ 2 ≤ _
  rw [inSpinFrame_hs]
  nlinarith only [(sq_le_sq₀ (Real.rpow_nonneg (hb 0) a) (Real.rpow_nonneg hr a)).2 (h 0),
    (sq_le_sq₀ (Real.rpow_nonneg (hb 1) a) (Real.rpow_nonneg hr a)).2 (h 1), sq_nonneg (B.trace.re^a)]

/-- A common upper bound on the traces may also be used in the normalized
matrix-root modulus. -/
theorem holderGrowth_div_rpow_mono {s r a : ℝ} (hs : 0 < s) (hsr : s ≤ r) (ha : a ≤ 1) (q : Position) :
    holderGrowth s q / s^a ≤ holderGrowth r q / r^a := by
  have he (t : ℝ) (ht : 0 < t) : holderGrowth t q / t^a =
      t^(4/3-a) + t^(5/3-a) + t^(1-a)*‖q‖^2 := by
    unfold holderGrowth
    rw [Real.rpow_sub ht, Real.rpow_sub ht, Real.rpow_sub ht, Real.rpow_one]
    ring
  rw [he s hs, he r (hs.trans_le hsr)]
  exact add_le_add (add_le_add (Real.rpow_le_rpow hs.le hsr (by linarith))
    (Real.rpow_le_rpow hs.le hsr (by linarith))) (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hs.le hsr (by linarith)) (sq_nonneg _))

/-- Change of trace in Proposition E.2(vi). The constants L and R are those
of the equal-trace root estimate and the ray estimate. -/
theorem root_lipschitz_of_equal_charge_of_one_le (e : SpinMatrix → ℝ) (q : Position) {L R p : ℝ}
    (hp : 1 ≤ p) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (fixed : ∀ {P Q : SpinMatrix} (hP : P.PosSemidef) (hQ : Q.PosSemidef), 0 < P.trace.re →
      P.trace.re = Q.trace.re → |e P-e Q| ≤ L*(holderGrowth P.trace.re q/P.trace.re^(1/p:ℝ))*
        hilbertSchmidt (hP.1.cfc (fun t => t^(1/p:ℝ)) - hQ.1.cfc (fun t => t^(1/p:ℝ))))
    (ray : ∀ {P : SpinMatrix}, P.PosSemidef → ∀ {b : ℝ}, 0 ≤ b → b ≤ 1 →
      |e (b • P) - e P| ≤ R*(1-b)*holderGrowth P.trace.re q)
    {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) (hr : 0 < max A.trace.re B.trace.re) :
    let r := max A.trace.re B.trace.re
    |e A-e B| ≤ (L*(1+4*p)+2*p*R) * holderGrowth r q *
      (hilbertSchmidt (hA.1.cfc (fun t => t^(1/p:ℝ)) - hB.1.cfc (fun t => t^(1/p:ℝ))) / r^(1/p:ℝ)) := by
  wlog hab : A.trace.re ≤ B.trace.re generalizing A B
  · simpa only [max_comm B.trace.re, abs_sub_comm (e B), hs_sub_comm (hB.1.cfc _)] using
      this hB hA (by rwa [max_comm]) (le_of_not_ge hab)
  rw [max_eq_right hab] at hr ⊢
  let r := B.trace.re
  let s := A.trace.re
  let a := 1/p
  let X := hA.1.cfc (fun t => t^a)
  let Y := hB.1.cfc (fun t => t^a)
  let d := hilbertSchmidt (X-Y)
  let b := s/r
  let G := holderGrowth r q
  have hp' : 0 < p := by linarith
  have ha : 0 < a := one_div_pos.mpr hp'
  have ha1 : a ≤ 1 := (div_le_one hp').mpr (by linarith)
  have hs : 0 ≤ s := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  have hb : 0 ≤ b := div_nonneg hs hr.le
  have hb1 : b ≤ 1 := (div_le_one hr).2 hab
  have hbr : b*r = s := div_mul_cancel₀ _ hr.ne'
  have hra : 0 < r^a := Real.rpow_pos_of_pos hr _
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hG : 0 ≤ G := by dsimp [G, holderGrowth, r]; positivity
  have tr_scaled : (b • B).trace.re = s := by simpa only
    [Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul] using hbr
  have hgap : (1-b)*r ≤ 2*(p*r^(1-a))*d := by
    have hm := matrix_power_oscillation hA hB ha ha1 hr.le hab le_rfl
    have one {P : SpinMatrix} (h : P.PosSemidef) : h.1.cfc (fun t => t^(1:ℝ)) = P := by
      simp only [Real.rpow_one]
      change h.1.cfc id = _
      rw [← h.1.cfc_eq, cfc_id ℝ P h.1.isSelfAdjoint]
    rw [one hA, one hB, show 1/a=p by dsimp [a]; simp] at hm
    have ht := abs_trace_re_le_hilbertSchmidt (A-B)
    rw [Matrix.trace_sub, Complex.sub_re, abs_of_nonpos (sub_nonpos.mpr hab)] at ht
    change hilbertSchmidt (A-B) ≤ (p*r^(1-a))*d at hm
    change -(s-r) ≤ 2*hilbertSchmidt (A-B) at ht
    linarith only [ht,hm,hbr]
  have hrem : (1-b)*r^a ≤ 2*p*d := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hr (1-a))).mp
    have hpow : r^(1-a)*r^a = r := by rw [← Real.rpow_add hr, sub_add_cancel, Real.rpow_one]
    calc
      _ = (1-b)*(r^(1-a)*r^a) := by change (1-b)*r^a*r^(1-a) = _; ring
      _ = (1-b)*r := by rw [hpow]
      _ ≤ _ := hgap
      _ = _ := by ring
  have hdist : hilbertSchmidt (X-b^a • Y) ≤ (1+4*p)*d := by
    have hba := Real.rpow_le_one hb hb1 ha.le
    have he : X-b^a • Y = (X-Y)+(1-b^a) • Y := by rw [sub_smul, one_smul]; abel
    have H : hilbertSchmidt (X-b^a • Y) ≤ d+(1-b^a)*hilbertSchmidt Y := by
      change _ ≤ hilbertSchmidt (X-Y)+_
      simp only [hs_eq_norm]
      rw [he]
      exact (norm_add_le ..).trans_eq (by rw [norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr hba)])
    have hs1 := Real.self_le_rpow_of_le_one hb hb1 ha1
    have hY : hilbertSchmidt Y ≤ 2*r^a := root_norm hB ha.le
    have hmul := mul_le_mul (sub_le_sub_left hs1 1) hY (Real.sqrt_nonneg _) (sub_nonneg.mpr hb1)
    linarith only [H,hmul,hrem]
  have hfix : |e A-e (b • B)| ≤ L*(G/r^a)*((1+4*p)*d) := by
    rcases hs.eq_or_lt with hz | hpos
    · have az : A=0 := hA.trace_eq_zero_iff.mp (Complex.ext hz.symm (RCLike.nonneg_iff.mp hA.trace_nonneg).2)
      rw [az, show b=0 by dsimp only [b]; rw [← hz, zero_div], zero_smul, sub_self, abs_zero]
      positivity
    have h := fixed hA (hB.smul hb) hpos tr_scaled.symm
    rw [positive_power_smul hB hb] at h
    exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left (holderGrowth_div_rpow_mono hpos hab ha1 q) hL)
      hdist (Real.sqrt_nonneg _) (mul_nonneg hL (div_nonneg hG hra.le)))
  have hrad := ray hB hb hb1
  change |e (b • B)-e B| ≤ R*(1-b)*G at hrad
  have hrr := mul_le_mul_of_nonneg_right ((le_div_iff₀ hra).2 hrem) (mul_nonneg hR hG)
  change |e A-e B| ≤ (L*(1+4*p)+2*p*R)*G*(d/r^a)
  apply ((abs_sub_le (e A) (e (b • B)) (e B)).trans (add_le_add hfix hrad)).trans
  simp only [div_eq_mul_inv] at hrr ⊢
  linarith only [hrr]

/-- The matrix-root specialization of the change-of-trace lemma used in
Proposition E.2. -/
theorem root_lipschitz_of_equal_charge (e : SpinMatrix → ℝ) (q : Position) {L R p : ℝ}
    (hp : 3 ≤ p) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (fixed : ∀ {P Q : SpinMatrix} (hP : P.PosSemidef) (hQ : Q.PosSemidef), 0 < P.trace.re →
      P.trace.re = Q.trace.re → |e P-e Q| ≤ L*(holderGrowth P.trace.re q/P.trace.re^(1/p:ℝ))*
        hilbertSchmidt (hP.1.cfc (fun t => t^(1/p:ℝ)) - hQ.1.cfc (fun t => t^(1/p:ℝ))))
    (ray : ∀ {P : SpinMatrix}, P.PosSemidef → ∀ {b : ℝ}, 0 ≤ b → b ≤ 1 →
      |e (b • P) - e P| ≤ R*(1-b)*holderGrowth P.trace.re q)
    {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) (hr : 0 < max A.trace.re B.trace.re) :
    let r := max A.trace.re B.trace.re
    |e A-e B| ≤ (L*(1+4*p)+2*p*R) * holderGrowth r q *
      (hilbertSchmidt (hA.1.cfc (fun t => t^(1/p:ℝ)) - hB.1.cfc (fun t => t^(1/p:ℝ))) / r^(1/p:ℝ)) :=
  root_lipschitz_of_equal_charge_of_one_le e q (by linarith : 1 ≤ p) hL hR fixed ray hA hB hr

end TSGA.SSW
