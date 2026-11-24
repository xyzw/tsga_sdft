import TSGA.TileAlignment
import TSGA.CoulombReplacement
import TSGA.AxialKinetic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Kinetic cost of aligning the spin axes in a spiral tile -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization
open scoped InnerProductSpace

variable {K : Set Position}

/-- Weak scalar product rule with the smooth plane wave on the tile. -/
def WeakPlaneWaveProduct (K : Set Position) : Prop :=
  ∀ (q : Position) (b : ℝ) (i : Fin 3) (f g : Position → ℂ),
    WeakPartialOn K i f g →
    WeakPartialOn K i (fun x => phaseFactor (b * ⟪q,x⟫_ℝ) * f x)
      (fun x => phaseFactor (b * ⟪q,x⟫_ℝ) * (g x + Complex.I * (b : ℂ) * (q i : ℂ) * f x))

/-- Coordinate derivative of the laboratory-frame rotation. Its wavevector
term vanishes on the diagonal. -/
def laboratoryGradient (q : Position) (V : Position → unitary SpinMatrix) (Z : MatrixGradient) :
    MatrixGradient := fun x i j k =>
  phaseFactor (axialWeight j k * ⟪q,x⟫_ℝ) *
    (Z x i j k + Complex.I * (axialWeight j k : ℂ) * (q i : ℂ) * (V x : SpinMatrix) j k)

theorem SpiralTaper.alignment_gradient (t : SpiralTaper K) (product : WeakPlaneWaveProduct K)
    {V : Position → unitary SpinMatrix} {Z : MatrixGradient}
    (hZ : IsMatrixGradientOn K (fun x => (V x : SpinMatrix)) Z) :
    IsMatrixGradientOn K (fun x => (t.alignment V x : SpinMatrix))
      (laboratoryGradient t.wavevector V Z) := by
  intro i j k
  change WeakPartialOn K i (fun x => rotate ⟪t.wavevector,x⟫_ℝ (V x : SpinMatrix) j k) _
  simp only [rotate_by_entry]
  exact product _ _ _ _ _ (hZ i j k)

/-- Conjugation by the spiral costs only the displacement from the identity.
The scalar `d²` can therefore vanish on a constant-axis tile. -/
theorem laboratoryGradient_sq (q : Position) (V : Position → unitary SpinMatrix)
    (Z : MatrixGradient) (x : Position) :
    (matrixGradNorm (laboratoryGradient q V Z) x)^2 ≤ 2*(matrixGradNorm Z x)^2 +
      2*‖q‖^2 * (hilbertSchmidt ((V x : SpinMatrix)-1))^2 := by
  let B := (V x : SpinMatrix)-1
  have correction (i : Fin 3) (j k : Fin 2) :
      ‖Complex.I * (axialWeight j k : ℂ) * (q i : ℂ) * (V x : SpinMatrix) j k‖ ≤
        ‖q i‖ * ‖B j k‖ := by
    have he : |axialWeight j k| ≤ 1 := by fin_cases j <;> fin_cases k <;> norm_num [axialWeight]
    by_cases hj : j = k
    · subst k
      simp only [axialWeight,sub_self,Complex.ofReal_zero,mul_zero,zero_mul,norm_zero]
      positivity
    · simp only [B,Matrix.sub_apply,Matrix.one_apply_ne hj,sub_zero,norm_mul,Complex.norm_I,one_mul,
        Complex.norm_real]
      rw [mul_assoc]
      exact mul_le_of_le_one_left (by positivity) he
  have entry (i : Fin 3) (j k : Fin 2) : ‖laboratoryGradient q V Z x i j k‖^2 ≤
      2*‖Z x i j k‖^2 + 2*‖q i‖^2*‖B j k‖^2 := by
    have h := (norm_add_le (Z x i j k) _).trans (add_le_add le_rfl (correction i j k))
    have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
    have hn (u : ℝ) : ‖phaseFactor u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    simp only [laboratoryGradient, norm_mul, hn, one_mul]
    nlinarith only [hs,sq_nonneg (‖Z x i j k‖-‖q i‖*‖B j k‖)]
  simp only [matrixGradNorm,hilbertSchmidt,Real.sq_sqrt (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _),PiLp.norm_sq_eq_of_L2]
  apply (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    Finset.sum_le_sum fun k _ => entry i j k).trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- A unitary representative on all of space, using the identity outside
the comparison set, where the tapered density vanishes. -/
def tileAxisUnitary (K : Set Position) (D : Density) (c : Position)
    (unit : ∀ x ∈ K, alignSpin (blochAxis (D.matrix x)) (blochAxis (D.matrix c)) ∈ unitary SpinMatrix)
    (x : Position) : unitary SpinMatrix := by
  classical
  exact if h : x ∈ K then ⟨_,unit x h⟩ else 1

private theorem transferGradient {f g : Position → SpinMatrix} {Z : MatrixGradient}
    (hK : MeasurableSet K) (e : Set.EqOn f g K) (h : IsMatrixGradientOn K f Z) :
    IsMatrixGradientOn K g Z := by
  intro i j k
  have he : (fun x => f x j k) =ᵐ[volume.restrict K] (fun x => g x j k) :=
    (ae_restrict_mem hK).mono fun _ hx => congrArg (fun A : SpinMatrix => A j k) (e hx)
  obtain ⟨hh,hg,hw⟩ := h i j k
  refine ⟨hh.congr he,hg,?_⟩
  intro ψ hψ hc hs
  apply Eq.trans _ (hw ψ hψ hc hs)
  exact integral_congr_ae (he.symm.mono fun _ hx => congrArg (_ • ·) hx)

private theorem alignSpin_self {n : Fin 3 → ℝ} (h : spinDot n n = 1) : alignSpin n n = 1 := by
  unfold alignSpin
  rw [h,pauli_sq h,show (2:ℝ)*(1+1) = 2^2 by norm_num,Real.sqrt_sq (by norm_num)]
  module

/-- The same actual unitary gives the reference-density conjugation, the
weighted gradient estimate, and the displacement estimate from the original
matrix oscillation. -/
theorem gapped_alignment_unitary (D : Density) {c : Position} (hK : MeasurableSet K) (hc : c ∈ K)
    (sob : SobolevCompositionOn K) {r : ℝ} (hr : 0 < r) (cap : ∀ x ∈ K, D.charge x ≤ r)
    (peak : ∃ z ∈ K, D.charge z = r)
    (minor : ∃ y ∈ K, ∃ i : Fin 2, (D.positive y).1.eigenvalues i ≤ r/8)
    (small : ∀ x ∈ K, ∀ y ∈ K, hilbertSchmidt (D.matrix x-D.matrix y) ≤ r/64)
    {S : MatrixGradient} (weak : IsMatrixGradientOn K (D.power (1/2)) S) :
    ∃ (V : Position → unitary SpinMatrix) (Z : MatrixGradient),
      (∀ x ∉ K, V x = 1) ∧ IsMatrixGradientOn K (fun x => (V x : SpinMatrix)) Z ∧
      (∀ x ∈ K, D.matrix x = (V x : SpinMatrix)*(referenceDensity D c).matrix x*star (V x : SpinMatrix)) ∧
      (∀ x ∈ K, hilbertSchmidt ((V x : SpinMatrix)-1) ≤ (96/r)*hilbertSchmidt (D.matrix x-D.matrix c)) ∧
      (∀ᵐ x ∂volume.restrict K, r*(matrixGradNorm Z x)^2 ≤ 192^2*(matrixGradNorm S x)^2) := by
  obtain ⟨maps,Z,hZ,estimate⟩ := gapped_tile_alignment D hc sob hr cap peak minor small weak
  have conv (x) : blochAxis (D.power (1/2) x) = blochAxis (D.matrix x) := blochAxis_matrix_sqrt (D.positive x)
  simp only [conv] at maps hZ
  let V := tileAxisUnitary K D c (fun x hx => (maps x hx).1)
  have onK (x) (hx : x ∈ K) : (V x : SpinMatrix) = alignSpin (blochAxis (D.matrix x)) (blochAxis (D.matrix c)) := by
    simp [V,tileAxisUnitary,hx]
  refine ⟨V,Z,fun x hx => by simp [V,tileAxisUnitary,hx],transferGradient hK (fun x hx => (onK x hx).symm) hZ,
    fun x hx => ?_,fun x hx => ?_,estimate⟩
  · rw [onK x hx]
    exact (maps x hx).2.2.symm
  · let n := fun x => blochAxis (D.matrix x)
    have gap := gap_on_small_tile D hr peak minor small
    have un (y) (hy : y ∈ K) := blochAxis_unit ((half_pos hr).trans_le (gap y hy))
    have hclose : hilbertSchmidt (D.matrix x-D.matrix c) ≤ blochGap (D.matrix x)/2 := by
      linarith only [small x hx c hc,gap x hx,hr]
    have angle := blochAxis_dot_nonneg_of_close (D.positive x).1 (D.positive c).1 hclose
    have hh := alignSpin_lipschitz_gap (un x hx) (un c hc) (un c hc) (by linarith only [angle])
      (by rw [un c hc]; norm_num) (half_pos hr) (gap x hx) (gap c hc)
      (blochGap_smul_pauli (D.positive x).1 ((half_pos hr).trans_le (gap x hx)))
      (blochGap_smul_pauli (D.positive c).1 ((half_pos hr).trans_le (gap c hc)))
    rw [alignSpin_self (un c hc),show 48/(r/2) = 96/r by ring] at hh
    simpa only [onK x hx] using hh

/-- Displacement in terms of the oscillation of any fractional matrix
power. In particular, the exponent `1/p` gives the wavevector correction
on a strongly polarized tile. -/
theorem alignment_displacement_of_power {D : Density} {c : Position}
    {V : Position → unitary SpinMatrix} {a r ω : ℝ} (hr : 0 < r) (ha : 0 < a) (ha' : a ≤ 1)
    (hc : c ∈ K) (cap : ∀ x ∈ K, D.charge x ≤ r)
    (base : ∀ x ∈ K, hilbertSchmidt ((V x : SpinMatrix)-1) ≤ (96/r)*hilbertSchmidt (D.matrix x-D.matrix c))
    (osc : ∀ x ∈ K, hilbertSchmidt (D.power a x-D.power a c) ≤ ω) :
    ∀ x ∈ K, hilbertSchmidt ((V x : SpinMatrix)-1) ≤ (96/a)*(ω/r^a) := by
  intro x hx
  have bound := matrix_power_oscillation (D.positive x) (D.positive c) ha ha' hr.le (cap x hx) (cap c hc)
  have idm (z) : (D.positive z).1.cfc (fun u => u^(1:ℝ)) = D.matrix z := by
    simp only [Real.rpow_one]
    change (D.positive z).1.cfc id = _
    rw [← (D.positive z).1.cfc_eq,cfc_id ℝ _ (D.positive z).1.isSelfAdjoint]
  rw [idm,idm] at bound
  have nonneg : 0 ≤ (1/a)*r^(1-a) := by positivity
  calc
    _ ≤ (96/r)*(((1/a)*r^(1-a))*ω) := (base x hx).trans (mul_le_mul_of_nonneg_left
      (bound.trans (mul_le_mul_of_nonneg_left (osc x hx) nonneg)) (by positivity))
    _ = _ := by rw [Real.rpow_sub hr,Real.rpow_one]; field_simp

/-- Scalar majorant for the squared derivative in both spin frames. -/
def alignmentWeight (S : MatrixGradient) (r : ℝ) (q : Position) (d : ℝ) (x : Position) :=
  (2*192^2/r)*kineticDensity S x + 2*‖q‖^2*d^2

theorem alignment_weight_bound {q : Position} {V : Position → unitary SpinMatrix} {Z S : MatrixGradient}
    {d r : ℝ} (hr : 0 < r)
    (gradient : ∀ᵐ x ∂volume.restrict K, r*(matrixGradNorm Z x)^2 ≤ 192^2*(matrixGradNorm S x)^2)
    (near : ∀ᵐ x ∂volume.restrict K, hilbertSchmidt ((V x : SpinMatrix)-1) ≤ d) :
    ∀ᵐ x ∂volume.restrict K, (matrixGradNorm (laboratoryGradient q V Z) x)^2 ≤ alignmentWeight S r q d x := by
  filter_upwards [gradient,near] with x hg hn
  have hS : (matrixGradNorm Z x)^2 ≤ 192^2*(matrixGradNorm S x)^2/r :=
    (le_div_iff₀ hr).mpr (by linarith only [hg])
  have hN := pow_le_pow_left₀ (show 0 ≤ hilbertSchmidt ((V x : SpinMatrix)-1) from Real.sqrt_nonneg _) hn 2
  apply (laboratoryGradient_sq q V Z x).trans
  have hq := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2*‖q‖^2 by positivity)
  unfold alignmentWeight kineticDensity
  rw [show 2*192^2/r*(matrixGradNorm S x)^2 = 2*(192^2*(matrixGradNorm S x)^2/r) by ring]
  linarith only [hS,hq]

/-- The cutoff confines the weighted cost to the ball. The wavevector term
carries the square of the rotation displacement. -/
def alignmentCost (t : SpiralTaper K) (S : MatrixGradient) (r d : ℝ) :=
  2*192^2*(∫ x, t.shape x*kineticDensity S x) + (2*r*‖t.wavevector‖^2*d^2)*(∫ x, t.shape x)

theorem alignmentWeight_integral (t : SpiralTaper K) (D : Density) {r d : ℝ} (hr : 0 < r)
    (cap : ∀ x ∈ K, D.charge x ≤ r) {S : MatrixGradient}
    (charge : AEMeasurable D.charge volume) (shape : Integrable t.shape)
    (kin : Integrable fun x => t.shape x*kineticDensity S x) :
    Integrable (fun x => (t.field D).charge x*alignmentWeight S r t.wavevector d x) ∧
    (∫ x, (t.field D).charge x*alignmentWeight S r t.wavevector d x) ≤ alignmentCost t S r d := by
  let H := fun x => 2*192^2*(t.shape x*kineticDensity S x) + (2*r*‖t.wavevector‖^2*d^2)*t.shape x
  have hH : Integrable H := (kin.const_mul _).add (shape.const_mul _)
  have tr (x) : (t.field D).charge x = (t.shape x)*(D.charge x) := by
    change ((t.shape x : ℂ) • rotate _ (D.matrix x)).trace.re = _
    rw [Matrix.trace_smul,trace_rotate,smul_eq_mul,Complex.re_ofReal_mul]
    rfl
  let f := fun x => (t.field D).charge x*alignmentWeight S r t.wavevector d x
  have fn (x) : 0 ≤ f x := mul_nonneg ((t.field D).charge_nonneg x)
    (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (by positivity))
  have hb (x) : f x ≤ H x := by
    dsimp only [f,H,alignmentWeight]
    rw [tr]
    by_cases hx : x ∈ K
    · have hs := t.range x |>.1
      have hn : 0 ≤ alignmentWeight S r t.wavevector d x := by
        unfold alignmentWeight kineticDensity
        positivity
      have e := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (cap x hx) hs) hn
      unfold alignmentWeight at e
      calc
        _ ≤ _ := e
        _ = _ := by field_simp
    · simp [t.outside x hx]
  have fm : AEMeasurable f volume := by
    have eqf : f = fun x => (2*192^2/r)*((t.shape x*kineticDensity S x)*D.charge x) +
        (2*‖t.wavevector‖^2*d^2)*(t.shape x*D.charge x) := by
      funext x
      dsimp only [f,alignmentWeight]
      rw [tr]
      ring
    rw [eqf]
    exact (aemeasurable_const.mul (kin.aestronglyMeasurable.aemeasurable.mul charge)).add
      (aemeasurable_const.mul (shape.aestronglyMeasurable.aemeasurable.mul charge))
  have hi := hH.mono' fm.aestronglyMeasurable (ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (fn x)]
    exact hb x)
  refine ⟨hi,(integral_mono hi hH hb).trans_eq ?_⟩
  dsimp only [H,alignmentCost]
  rw [integral_add (kin.const_mul _) (shape.const_mul _),integral_const_mul,integral_const_mul]

open scoped ContDiff

/-- Integration by parts with complex tests on a compact tile. The real and
imaginary components are admissible tests in the definition of a weak
partial derivative. -/
private theorem weak_complex_tile {i : Fin 3} {f df : Position → ℂ} (hK : IsCompact K)
    (H : WeakPartialOn K i f df) (g : Position → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ K) :
    (∫ x in K, fderiv ℝ g x (PiLp.single 2 i 1) * f x) = -(∫ x in K, g x * df x) := by
  let dir : Position := PiLp.single 2 i (1:ℝ)
  let dg := fun x => fderiv ℝ g x dir
  have split {u v : Position → ℂ} (hu : IntegrableOn u K) (hv : Continuous v) :
      (∫ x in K, v x*u x) = (∫ x in K, (v x).re • u x) + Complex.I*(∫ x in K, (v x).im • u x) := by
    have hi (l : ℂ →L[ℝ] ℝ) : IntegrableOn (fun x => (l (v x)) • u x) K := by
      simp only [Complex.real_smul]
      exact IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp (l.continuous.comp hv)).continuousOn hu hK
    have ir : Integrable (fun x => (v x).re • u x) (volume.restrict K) := hi Complex.reCLM
    have ii : Integrable (fun x => Complex.I * ((v x).im • u x)) (volume.restrict K) :=
      (hi Complex.imCLM).const_mul _
    rw [← integral_const_mul, ← integral_add ir ii]
    apply integral_congr_ae (ae_of_all _ fun x => ?_)
    rw [Complex.real_smul, Complex.real_smul, ← mul_assoc,mul_comm Complex.I, ← add_mul, Complex.re_add_im]
  have part (l : ℂ →L[ℝ] ℝ) :
      (∫ x in K, l (dg x) • f x) = -(∫ x in K, l (g x) • df x) := by
    have ht : tsupport (l ∘ g) ⊆ tsupport g := tsupport_comp_subset (map_zero l) _
    have htst := H.2.2 (l ∘ g) (l.contDiff.comp hg) (hc.comp_left (map_zero l)) (ht.trans hs)
    have deriv (x : Position) : fderiv ℝ (l ∘ g) x dir = l (dg x) := by
      rw [(l.hasFDerivAt.comp x ((hg.differentiable (by simp) x).hasFDerivAt)).fderiv]
      rfl
    simpa only [← deriv,Function.comp_apply] using htst
  change (∫ x in K, dg x*f x) = _
  rw [split (H.1.integrableOn_isCompact hK) ((hg.continuous_fderiv (by simp)).clm_apply continuous_const),
    split (H.2.1.integrableOn_isCompact hK) hg.continuous]
  change (∫ x in K, Complex.reCLM (dg x) • f x) + Complex.I*(∫ x in K, Complex.imCLM (dg x) • f x) = _
  rw [part Complex.reCLM,part Complex.imCLM]
  simp [add_comm]

/-- The weak plane-wave multiplier rule follows directly by testing the
original weak derivative with the plane wave times the test function. -/
theorem weakPlaneWaveProduct_of_isCompact (hK : IsCompact K) : WeakPlaneWaveProduct K := by
  intro q b i f df H
  let p := fun x : Position => phaseFactor (b*⟪q,x⟫_ℝ)
  let a := Complex.I*(b:ℂ)*(q i:ℂ)
  let dir : Position := PiLp.single 2 i (1:ℝ)
  let L : Position →L[ℝ] ℝ := b • innerSL ℝ q
  have repr : p = fun x => Complex.exp ((L x : ℂ)*Complex.I) := rfl
  have hp : ContDiff ℝ ∞ p := by
    rw [repr]
    exact ((Complex.ofRealCLM.contDiff.comp L.contDiff).mul contDiff_const).cexp
  have dp (x) : fderiv ℝ p x dir = p x*a := by
    have hd := (((Complex.ofRealCLM.hasFDerivAt.comp x L.hasFDerivAt).mul_const Complex.I).cexp).fderiv
    rw [repr]
    change fderiv ℝ (fun x => Complex.exp (((Complex.ofRealCLM ∘ L) x)*Complex.I)) x dir = _
    rw [hd]
    change Complex.exp ((L x:ℂ)*Complex.I)*(Complex.I*(L dir : ℂ)) = _
    simp [L,dir,innerSL_apply_apply,EuclideanSpace.inner_single_right,a]
    ring
  have hfi := H.1.integrableOn_isCompact hK
  have hdi := H.2.1.integrableOn_isCompact hK
  have hpfi := IntegrableOn.continuousOn_mul hp.continuous.continuousOn hfi hK
  have hdfi : IntegrableOn (fun x => df x + a*f x) K := hdi.add (hfi.const_mul a)
  refine ⟨hpfi.locallyIntegrableOn,(IntegrableOn.continuousOn_mul hp.continuous.continuousOn hdfi hK).locallyIntegrableOn,?_⟩
  intro ψ hψ hc hs
  let dψ := fun x => fderiv ℝ ψ x dir
  let g := fun x => (ψ x:ℂ)*p x
  have ψs : ContDiff ℝ ∞ (fun x => (ψ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  have gs : ContDiff ℝ ∞ g := ψs.mul hp
  have gt : tsupport g ⊆ tsupport ψ :=
    (tsupport_mul_subset_left (f := fun x => (ψ x : ℂ)) (g := p)).trans (tsupport_comp_subset Complex.ofReal_zero ψ)
  have gc : HasCompactSupport g := (hc.comp_left Complex.ofReal_zero).mul_right
  have deriv (x) : fderiv ℝ g x dir = (dψ x:ℂ)*p x + g x*a := by
    have h := ((Complex.ofRealCLM.hasFDerivAt.comp x ((hψ.differentiable (by simp) x).hasFDerivAt)).mul
      ((hp.differentiable (by simp) x).hasFDerivAt)).fderiv
    change fderiv ℝ ((Complex.ofRealCLM ∘ ψ)*p) x dir = _
    rw [h]
    simp only [Function.comp_apply,add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply,dp,g,dψ]
    ring
  let A := fun x => (dψ x:ℂ)*p x*f x
  let B := fun x => (g x*a)*f x
  let C := fun x => g x*df x
  have dcont : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have ia : IntegrableOn A K :=
    IntegrableOn.continuousOn_mul ((Complex.continuous_ofReal.comp dcont).mul hp.continuous).continuousOn hfi hK
  have ib : IntegrableOn B K := IntegrableOn.continuousOn_mul (gs.continuous.mul continuous_const).continuousOn hfi hK
  have ic : IntegrableOn C K := IntegrableOn.continuousOn_mul gs.continuous.continuousOn hdi hK
  have he : (∫ x in K, A x)+(∫ x in K, B x) = -(∫ x in K,C x) := by
    rw [← integral_add ia ib]
    have hw := weak_complex_tile hK H g gs gc (gt.trans hs)
    change (∫ x in K, fderiv ℝ g x dir*f x) = _ at hw
    simpa only [A,B,C,deriv,add_mul] using hw
  have e₁ (x) : dψ x • (p x*f x) = A x := by simp [A,Complex.real_smul,mul_assoc]
  have e₂ (x) : ψ x • (p x*(df x + a*f x)) = C x+B x := by simp only [C,B,g,Complex.real_smul]; ring
  change (∫ x in K, dψ x • (p x*f x)) = -(∫ x in K, ψ x • (p x*(df x + a*f x)))
  simp_rw [e₁,e₂]
  rw [integral_add ic ib]
  linear_combination he

end TSGA.ManyBody
