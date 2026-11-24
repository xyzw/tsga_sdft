import TSGA.PoissonIslands

/-! # The covariance of the shell between two Poisson unions

Joint Laplace functionals of the two masks give the thin-shell bound
directly. The overlap of two copies of the difference profile contributes
linearly. Two distinct hits contribute quadratically in the shell intensity.
-/

noncomputable section
namespace TSGA.Islands

/-- Covariance of `Q_b - Q_u`, where Q denotes an uncovered mask, u=b+s.
The four numbers k,p,q,d are the overlaps of bb,bs,sb,ss at two points. -/
def shellCovariance (v b k p q d : ℝ) :=
  Real.exp (-b)*Real.exp (-b)*Real.exp k - Real.exp (-b)*Real.exp (-v)*Real.exp (k+p) -
  Real.exp (-v)*Real.exp (-b)*Real.exp (k+q) + Real.exp (-v)*Real.exp (-v)*Real.exp (k+p+q+d) -
  (Real.exp (-b)-Real.exp (-v))^2

theorem shellCovariance_far (v b : ℝ) : shellCovariance v b 0 0 0 0 = 0 := by
  simp [shellCovariance]; ring

theorem shellCovariance_le {v b k p q d : ℝ} (hb : 0 ≤ b) (hbv : b ≤ v) (hv : v ≤ 1)
    (hk : k ≤ v) (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d)
    (hp' : p ≤ v-b) (hq' : q ≤ v-b) (htot : k+p+q+d ≤ 2*v) :
    shellCovariance v b k p q d ≤ d + Real.exp 1 * (v-b)^2 := by
  let a := Real.exp (-b)
  let e := Real.exp (-v)
  have hae : e ≤ a := Real.exp_le_exp.mpr (by linarith)
  have hdiff : a-e ≤ v-b := by
    have eqn : a-e = a*(1-Real.exp (-(v-b))) := by
      dsimp [a,e]
      rw [mul_sub,mul_one,← Real.exp_add]
      ring_nf
    rw [eqn]
    refine (mul_le_of_le_one_left (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb))).trans ?_
    linarith only [Real.one_sub_le_exp_neg (v-b)]
  have hde (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ v-b) :
      0 ≤ a-e*Real.exp t ∧ a-e*Real.exp t ≤ a-e := by
    have h₀ : e*Real.exp t ≤ a := by
      dsimp [a,e]; rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have h₁ := mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr ht) (Real.exp_pos (-v)).le
    exact ⟨sub_nonneg.mpr h₀,by dsimp [e] at *; linarith only [h₁]⟩
  have hprod := mul_le_mul (hde p hp hp').2 (hde q hq hq').2 (hde q hq hq').1 (sub_nonneg.mpr hae)
  have hfirst : Real.exp k *((a-e*Real.exp p)*(a-e*Real.exp q)) ≤ Real.exp 1 * (v-b)^2 := by
    refine (mul_le_mul_of_nonneg_left hprod (Real.exp_pos k).le).trans ?_
    rw [← sq]
    exact mul_le_mul (Real.exp_le_exp.mpr (hk.trans hv)) ((sq_le_sq₀ (sub_nonneg.mpr hae) (sub_nonneg.mpr hbv)).mpr hdiff)
      (sq_nonneg _) (Real.exp_pos _).le
  have hC : e*e*Real.exp (k+p+q+d) ≤ 1 := by
    dsimp [e]; rw [← Real.exp_add,← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
  have htail : e*e*Real.exp (k+p+q+d)*(1-Real.exp (-d)) ≤ d := by
    refine (mul_le_of_le_one_left (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hd))) hC).trans ?_
    linarith only [Real.one_sub_le_exp_neg d]
  have cancel : Real.exp (k+p+q+d)*Real.exp (-d) = Real.exp (k+p+q) := by
    rw [← Real.exp_add]; congr 1; ring
  have eqn : shellCovariance v b k p q d =
      Real.exp k *((a-e*Real.exp p)*(a-e*Real.exp q)) +
      e*e*Real.exp (k+p+q+d)*(1-Real.exp (-d)) - (a-e)^2 := by
    rw [mul_sub (e*e*Real.exp (k+p+q+d)),mul_one, mul_assoc (e*e) _ _,cancel]
    simp only [shellCovariance,Real.exp_add,a,e]
    ring
  rw [eqn]
  linarith only [hfirst,htail,sq_nonneg (a-e)]

/-- The covariance of two occurrences of a single covered or uncovered mask. -/
theorem oneMask_covariance_le {v a : ℝ} (ha : 0 ≤ a) (hav : a ≤ v) :
    Real.exp (-v)*Real.exp (-v)*Real.exp a - Real.exp (-v)^2 ≤ a := by
  have hv : 0 ≤ v := ha.trans hav
  have h : Real.exp (-v)*Real.exp (-v)*Real.exp a ≤ 1 := by
    rw [← Real.exp_add,← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
  have e : Real.exp (-v)*Real.exp (-v)*Real.exp a - Real.exp (-v)^2 =
      (Real.exp (-v)*Real.exp (-v)*Real.exp a)*(1-Real.exp (-a)) := by
    rw [mul_sub,mul_one,mul_assoc _ (Real.exp a) _,← Real.exp_add a (-a),add_neg_cancel,Real.exp_zero,mul_one,sq]
  rw [e]
  refine (mul_le_of_le_one_left (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha))) h).trans ?_
  linarith only [Real.one_sub_le_exp_neg a]

end TSGA.Islands
