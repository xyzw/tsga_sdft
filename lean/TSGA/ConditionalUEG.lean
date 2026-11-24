import TSGA.CoulombModel
import TSGA.SpinPopulationSegment

/-! # The conjectural endpoint bound and regularity of the uniform gas -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Filter TSGA.Localization SSW Matrix
open scoped ComplexOrder MatrixOrder Kronecker

/-- Flipping a minority occupation x costs at most linearly in x at full
polarization. This is the linear spin-flip endpoint conjecture. -/
def UEGEndpointBound (η : Mollifier) (C : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x : ℝ, 0 ≤ x → x ≤ r/2 →
    uniformEnergy energy η (populations r 0) - uniformEnergy energy η (populations (r-x) x) ≤
      C*(r^(1/3:ℝ)+r^(2/3:ℝ))*x

set_option maxHeartbeats 600000 in
private theorem cutoff_spin_unitary {f : Position → ℝ} {V : ℝ} (F : OrderedSpiralFrame f V 0)
    {A : SpinMatrix} (hA : A.PosSemidef) (U : unitary SpinMatrix) :
    energy (fun x => f x • Unitary.conjStarAlgAut ℂ SpinMatrix U A) =
      energy (fun x => f x • A) := by
  let B := Unitary.conjStarAlgAut ℂ SpinMatrix U A
  have hB : B.PosSemidef := by
    change ((U : SpinMatrix) * A * (U : SpinMatrix).conjTranspose).PosSemidef
    exact hA.mul_mul_conjTranspose_same (U : SpinMatrix)
  have mapState {X : SpinMatrix} (hX : X.PosSemidef) (T : unitary SpinMatrix) (s : CutoffState f X) :
      ∃ t : CutoffState f (Unitary.conjStarAlgAut ℂ SpinMatrix T X),
        t.val.kinetic+t.val.interaction = s.val.kinetic+s.val.interaction := by
    obtain ⟨t,K,W,_,_,hk,hw,ht,hv,_⟩ := F.localize X hX s T (Unitary.coe_star_mul_self T).le
    refine ⟨t,?_⟩
    rw [ht,hv,Unitary.coe_star_mul_self,Matrix.one_kronecker_one,one_mul,one_mul,hk,hw]
  have inv : Unitary.conjStarAlgAut ℂ SpinMatrix (star U) B = A := by
    rw [← Unitary.conjStarAlgAut_symm]
    exact (Unitary.conjStarAlgAut ℂ SpinMatrix U).symm_apply_apply A
  have same : levyLieb (fun x => f x • B) = levyLieb (fun x => f x • A) := by
    apply congrArg sInf
    ext z
    constructor
    · rintro ⟨s,hs,hz⟩
      obtain ⟨t,ht⟩ := mapState hB (star U) ⟨s,hs⟩
      exact ⟨t.val,by simpa only [inv] using t.property,hz.trans ht.symm⟩
    · rintro ⟨s,hs,hz⟩
      obtain ⟨t,ht⟩ := mapState hA U ⟨s,hs⟩
      exact ⟨t.val,t.property,hz.trans ht.symm⟩
  have tr : B.trace = A.trace := by
    change Matrix.trace ((U : SpinMatrix)*A*star (U : SpinMatrix)) = _
    rw [Matrix.trace_mul_cycle,Unitary.coe_star_mul_self,one_mul]
  change levyLieb _ - hartree (fun x => (f x • B).trace.re) = levyLieb _ - _
  rw [same]
  simp only [Matrix.trace_smul,tr]

/-- A global spin rotation preserves the zero-wavevector gas energy. -/
theorem uniform_spin_unitary {η : Mollifier} {K : ℝ} (L : CoulombGasInputs η K)
    {A : SpinMatrix} (hA : A.PosSemidef) (U : unitary SpinMatrix) :
    uniformEnergy energy η (Unitary.conjStarAlgAut ℂ SpinMatrix U A) = uniformEnergy energy η A := by
  apply tileLimit_congr
  filter_upwards [eventually_ge_atTop (1:ℝ)] with ℓ hℓ
  obtain ⟨F⟩ := L.frames ℓ (zero_lt_one.trans_le hℓ) 1 zero_lt_one hℓ 0
  have h := cutoff_spin_unitary F hA U
  simpa only [uniformEnergy,Complex.coe_smul] using congrArg (fun z : ℝ => z/regionVolume (tetrahedron ℓ)) h

theorem population_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (populations a b).PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  fin_cases i <;> simp [ha,hb]

private theorem uniform_swap {η : Mollifier} {K : ℝ} (L : CoulombGasInputs η K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    uniformEnergy energy η (populations a b) = uniformEnergy energy η (populations b a) := by
  let X : SpinMatrix := !![0,1;1,0]
  have hx : X ∈ unitary SpinMatrix := by
    apply Unitary.mem_iff.mpr
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [X,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply]
  let S : unitary SpinMatrix := ⟨X,hx⟩
  have swap : Unitary.conjStarAlgAut ℂ SpinMatrix S (populations a b) = populations b a := by
    change X * populations a b * star X = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X,populations,Matrix.mul_apply,Matrix.vecMul, dotProduct,Fin.sum_univ_two,Matrix.star_apply]
  rw [←swap]
  exact (uniform_spin_unitary L (population_pos ha hb) S).symm

/-- Secants on the left half of a convex symmetric interval inherit the
linear endpoint bound, including a secant starting at the endpoint. -/
private theorem endpoint_secants {g : ℝ → ℝ} {H : ℝ} (hH : 0 ≤ H) (conv : ConvexOn ℝ (Set.Icc 0 1) g)
    (eq : g 1 = g 0) (left : ∀ t ∈ Set.Icc (0:ℝ) (1/2), g 0-g t ≤ H*t)
    {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) (1/2)) (ht : t ∈ Set.Icc (0:ℝ) (1/2)) :
    |g s-g t| ≤ H*|s-t| := by
  wlog order : s ≤ t generalizing s t
  · simpa only [abs_sub_comm (g t),abs_sub_comm t] using this ht hs (le_of_not_ge order)
  rcases order.eq_or_lt with rfl | hst
  · simp
  have tpos : 0 < t := hs.1.trans_lt hst
  have sgap : 0 < 1-s := by linarith [hs.2]
  have ht1 : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1,by linarith [ht.2]⟩
  have hs1 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1,by linarith [hs.2]⟩
  have rhs : g 1-g s ≤ H*(1-s) := by
    rw [eq]
    exact (left s hs).trans (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hH)
  rw [abs_of_nonpos (sub_nonpos.mpr order),abs_le]
  constructor
  · have h := conv.secant_mono_aux1 hs1 (by norm_num : (1:ℝ) ∈ Set.Icc 0 1) hst (by linarith [ht.2])
    have m := mul_le_mul_of_nonneg_left rhs (sub_nonneg.mpr order)
    have step : (g t-g s)*(1-s) ≤ H*(t-s)*(1-s) := by nlinarith only [h,m]
    linarith only [(mul_le_mul_iff_left₀ sgap).mp step]
  · rcases hs.1.eq_or_lt with h | h
    · simpa only [← h,zero_sub,neg_neg] using left t ht
    have sec := conv.secant_mono_aux1 (by norm_num : (0:ℝ) ∈ Set.Icc 0 1) ht1 h hst
    have m := mul_le_mul_of_nonneg_left (left t ht) (sub_nonneg.mpr order)
    have step : (g s-g t)*t ≤ H*(t-s)*t := by nlinarith only [sec,m]
    linarith only [(mul_le_mul_iff_left₀ tpos).mp step]


private theorem population_line (r t : ℝ) :
    AffineMap.lineMap (populations r 0) (populations 0 r) t = populations (r-t*r) (t*r) := by
  rw [AffineMap.lineMap_apply_module]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [populations,Matrix.smul_apply,Complex.real_smul]
  ring

private theorem population_trace (a b : ℝ) : (populations a b).trace.re = a+b := by
  simp [populations]

private theorem fixed_population_lipschitz {η : Mollifier} {K C : ℝ} (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (hyp : UEGEndpointBound η C)
    (hC : 0 ≤ C) {r : ℝ} (hr : 0 < r) {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) (r/2))
    (hy : y ∈ Set.Icc (0:ℝ) (r/2)) :
    |uniformEnergy energy η (populations (r-x) x) - uniformEnergy energy η (populations (r-y) y)| ≤
      C*(r^(1/3:ℝ)+r^(2/3:ℝ))*|x-y| := by
  let path : ℝ →ᵃ[ℝ] SpinMatrix := AffineMap.lineMap (populations r 0) (populations 0 r)
  let g := uniformEnergy energy η ∘ path
  let Kc := C*(r^(1/3:ℝ)+r^(2/3:ℝ))
  have cost : 0 ≤ Kc := by dsimp only [Kc]; positivity
  have h0 : populations r 0 ∈ fixedCharge r := ⟨population_pos hr.le le_rfl,by rw [population_trace,add_zero]⟩
  have h1 : populations 0 r ∈ fixedCharge r := ⟨population_pos le_rfl hr.le,by rw [population_trace,zero_add]⟩
  have conv := coulomb_ssw_convex_fixed_charge η L.localization (L.kinematics H sob) hr (0:Position)
  simp only [sswEnergy_zero_wavevector] at conv
  have cg : ConvexOn ℝ (Set.Icc 0 1) g :=
    (conv.comp_affineMap path).subset (fun _ ht => conv.1.lineMap_mem h0 h1 ht) (convex_Icc ..)
  have eq : g 1 = g 0 := by
    simpa [g,path] using uniform_swap L (a := 0) (by norm_num : (0:ℝ) ≤ 0) hr.le
  have left (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (1/2)) : g 0-g t ≤ (Kc*r)*t := by
    have hx' := mul_le_mul_of_nonneg_right ht.2 hr.le
    have he := hyp r hr (t*r) (mul_nonneg ht.1 hr.le) (by linarith only [hx'])
    simpa only [g,Function.comp_apply,path,AffineMap.lineMap_apply_zero,population_line,Kc,mul_assoc,mul_comm r t] using he
  have divmem (z : ℝ) (hz : z ∈ Set.Icc (0:ℝ) (r/2)) : z/r ∈ Set.Icc (0:ℝ) (1/2) :=
    ⟨div_nonneg hz.1 hr.le,(div_le_iff₀ hr).2 (by linarith only [hz.2])⟩
  have h := endpoint_secants (mul_nonneg cost hr.le) cg eq left (divmem x hx) (divmem y hy)
  change |uniformEnergy energy η (path (x/r)) - uniformEnergy energy η (path (y/r))| ≤ _ at h
  simp only [path,population_line,div_mul_cancel₀ _ hr.ne',← sub_div,abs_div,abs_of_pos hr] at h
  exact h.trans_eq (by dsimp only [Kc]; field_simp [hr.ne'])

def minorityPopulation {A : SpinMatrix} (hA : A.PosSemidef) :=
  min (hA.1.eigenvalues 0) (hA.1.eigenvalues 1)

private theorem minority_mem {A : SpinMatrix} (hA : A.PosSemidef) :
    minorityPopulation hA ∈ Set.Icc 0 (A.trace.re/2) := by
  refine ⟨le_min (hA.eigenvalues_nonneg _) (hA.eigenvalues_nonneg _),?_⟩
  dsimp [minorityPopulation]
  linarith only [min_le_left (hA.1.eigenvalues 0) (hA.1.eigenvalues 1),
    min_le_right (hA.1.eigenvalues 0) (hA.1.eigenvalues 1),spin_population_sum hA]

/-- The uniform gas energy depends only on the two spin populations,
ordered here by decreasing eigenvalue. -/
theorem uniform_populations {η : Mollifier} {K : ℝ} (L : CoulombGasInputs η K)
    {A : SpinMatrix} (hA : A.PosSemidef) :
    uniformEnergy energy η A = uniformEnergy energy η (populations (A.trace.re-minorityPopulation hA) (minorityPopulation hA)) := by
  let a := hA.1.eigenvalues
  have ea : Unitary.conjStarAlgAut ℂ SpinMatrix hA.1.eigenvectorUnitary (populations (a 0) (a 1)) = A := by
    have hd : populations (a 0) (a 1) = diagonal (fun i => (a i : ℂ)) := by
      apply congrArg diagonal
      funext i
      fin_cases i <;> rfl
    rw [hd]
    exact hA.1.spectral_theorem.symm
  have hu := uniform_spin_unitary L (population_pos (hA.eigenvalues_nonneg 0) (hA.eigenvalues_nonneg 1)) hA.1.eigenvectorUnitary
  rw [ea] at hu
  have tr : a 0+a 1 = A.trace.re := spin_population_sum hA
  change _ = uniformEnergy energy η (populations (A.trace.re-min (a 0) (a 1)) (min (a 0) (a 1)))
  rcases le_total (a 0) (a 1) with h | h
  · rw [min_eq_left h,show A.trace.re-a 0 = a 1 by linarith only [tr]]
    exact hu.trans (uniform_swap L (hA.eigenvalues_nonneg _) (hA.eigenvalues_nonneg _))
  · rw [min_eq_right h,show A.trace.re-a 1 = a 0 by linarith only [tr]]
    exact hu

private theorem minority_dist {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    |minorityPopulation hA-minorityPopulation hB| ≤ hilbertSchmidt (A-B) := by
  have bound (i : Fin 2) := eigenvalue_power_distance hA hB (zero_le_one : 0 ≤ (1:ℝ)) i
  simp only [Real.rpow_one] at bound
  change ∀ i, |hA.1.eigenvalues i-hB.1.eigenvalues i| ≤ hilbertSchmidt (hA.1.cfc id-hB.1.cfc id) at bound
  rw [← hA.1.cfc_eq,cfc_id ℝ _ hA.1.isSelfAdjoint,← hB.1.cfc_eq,cfc_id ℝ _ hB.1.isSelfAdjoint] at bound
  rcases spin_indices_same_order hA.1 hB.1 with ⟨h,k⟩ | ⟨h,k⟩
  · simpa only [minorityPopulation,min_eq_right h,min_eq_right k] using bound 1
  · simpa only [minorityPopulation,min_eq_left h,min_eq_left k] using bound 0

private theorem equal_trace_lipschitz {η : Mollifier} {K C : ℝ} (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (hyp : UEGEndpointBound η C)
    (hC : 0 ≤ C) {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hr : 0 < A.trace.re) (eq : A.trace.re = B.trace.re) :
    |uniformEnergy energy η A-uniformEnergy energy η B| ≤
      C*(A.trace.re^(1/3:ℝ)+A.trace.re^(2/3:ℝ))*hilbertSchmidt (A-B) := by
  rw [uniform_populations L hA,uniform_populations L hB,←eq]
  exact (fixed_population_lipschitz L H sob hyp hC hr (minority_mem hA) (eq ▸ minority_mem hB)).trans
    (mul_le_mul_of_nonneg_left (minority_dist hA hB) (by positivity))


private theorem psd_zero_of_trace {A : SpinMatrix} (hA : A.PosSemidef) (hz : A.trace.re = 0) : A = 0 :=
  hA.trace_eq_zero_iff.mp (Complex.ext hz (RCLike.nonneg_iff.mp hA.trace_nonneg).2)

open scoped Matrix.Norms.Frobenius in
private theorem shrink_distance {A B : SpinMatrix} {b : ℝ} (hb : b ≤ 1) :
    hilbertSchmidt (A-b • B) ≤ hilbertSchmidt (A-B)+(1-b)*hilbertSchmidt B := by
  simp only [hs_eq_norm]
  have split : A-b • B = (A-B)+(1-b) • B := by rw [sub_smul,one_smul]; abel
  rw [split]
  exact (norm_add_le ..).trans_eq (by rw [norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr hb)])

private theorem unequal_trace_lipschitz {η : Mollifier} {K C : ℝ} (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (hyp : UEGEndpointBound η C)
    (hC : 0 ≤ C) (A B : SpinMatrix) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    let r := max A.trace.re B.trace.re
    let R := 2*(H.loCoeff+2*K)+2*(2*K+1)
    |uniformEnergy energy η A-uniformEnergy energy η B| ≤
      (3*C+2*R)*(r^(1/3:ℝ)+r^(2/3:ℝ))*hilbertSchmidt (A-B) := by
  wlog hab : A.trace.re ≤ B.trace.re generalizing A B
  · simpa only [max_comm B.trace.re,abs_sub_comm (uniformEnergy energy η B),hs_sub_comm B A] using
      this B A hB hA (le_of_not_ge hab)
  intro r R
  have hr : r = B.trace.re := max_eq_right hab
  have r0 : 0 ≤ r := (RCLike.nonneg_iff.mp hB.trace_nonneg).1.trans_eq hr.symm
  have s0 := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  have hK := zero_le_one.trans L.rate.one_le
  have R0 : 0 ≤ R := by dsimp only [R]; positivity [H.lo_nonneg]
  let growth := r^(1/3:ℝ)+r^(2/3:ℝ)
  let d := hilbertSchmidt (A-B)
  have g0 : 0 ≤ growth := by dsimp only [growth]; positivity
  have d0 : 0 ≤ d := Real.sqrt_nonneg _
  rcases r0.eq_or_lt with hz | pos
  · have zB := psd_zero_of_trace hB (hr.symm.trans hz.symm)
    have zA := psd_zero_of_trace hA (le_antisymm (hab.trans_eq (hr.symm.trans hz.symm)) s0)
    change _ ≤ (3*C+2*R)*growth*d
    rw [zB,zA,sub_self,abs_zero]
    positivity
  let b := A.trace.re/r
  have b0 : 0 ≤ b := div_nonneg s0 r0
  have b1 : b ≤ 1 := (div_le_one pos).2 (hab.trans_eq hr.symm)
  have br : b*r = A.trace.re := div_mul_cancel₀ _ pos.ne'
  let X := b • B
  have hX : X.PosSemidef := hB.smul b0
  have tr : X.trace.re = A.trace.re := by simpa only [X,Matrix.trace_smul,Complex.real_smul,Complex.re_ofReal_mul,←hr] using br
  have gap : (1-b)*r ≤ 2*d := by
    have diff := abs_trace_re_le_hilbertSchmidt (A-B)
    rw [Matrix.trace_sub,Complex.sub_re,abs_of_nonpos (sub_nonpos.mpr hab),←hr] at diff
    change _ ≤ 2*hilbertSchmidt (A-B)
    linarith only [diff,br]
  have dist : hilbertSchmidt (A-X) ≤ 3*d := by
    have h := shrink_distance (A := A) (B := B) b1
    have m := mul_le_mul_of_nonneg_left ((hilbertSchmidt_le_trace hB).trans_eq hr.symm) (sub_nonneg.mpr b1)
    change hilbertSchmidt (A-X) ≤ d+_ at h
    linarith only [h,m,gap]
  have span : |uniformEnergy energy η A - uniformEnergy energy η X| ≤ C*growth*(3*d) := by
    rcases s0.eq_or_lt with zero | positive
    · rw [psd_zero_of_trace hA zero.symm,psd_zero_of_trace hX (tr.trans zero.symm),sub_self,abs_zero]
      positivity
    have g := add_le_add (Real.rpow_le_rpow s0 (hab.trans_eq hr.symm) (by norm_num : 0 ≤ (1/3:ℝ)))
      (Real.rpow_le_rpow s0 (hab.trans_eq hr.symm) (by norm_num : 0 ≤ (2/3:ℝ)))
    exact (equal_trace_lipschitz L H sob hyp hC hA hX positive tr.symm).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left g hC) dist (Real.sqrt_nonneg _) (mul_nonneg hC g0))
  let states := L.kinematics H sob
  let gas := coulomb_sswGas η L.localization states
  have ray := gas.ray_lipschitz L.rate H.lo_nonneg hB 0 b0 b1
    (ssw_scaling gas H.lo_nonneg H.indirect_lower B hB 0
      (fun n => SpiralKinematics.representable states B hB n 0) b0 b1)
  have powers : r^(4/3:ℝ)+r^(5/3:ℝ) = r*growth := by
    simpa only [holderGrowth,rateGrowth,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,growth]
      using holderGrowth_eq pos (0:Position)
  have ray' : |uniformEnergy energy η X-uniformEnergy energy η B| ≤ R*(1-b)*(r*growth) := by
    simpa only [sswEnergy_zero_wavevector,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,
      ←hr,powers,X,R] using ray
  apply ((abs_sub_le _ (uniformEnergy energy η X) _).trans (add_le_add span ray')).trans
  change _ ≤ (3*C+2*R)*growth*d
  nlinarith only [mul_le_mul_of_nonneg_right gap (mul_nonneg R0 g0)]

/-- Under the endpoint conjecture the zero-wavevector matrix modulus holds
through the boundary of the PSD cone, uniformly in the minority fraction. -/
theorem CoulombGasInputs.ueg_lipschitz_of_endpoint {η : Mollifier} {K C : ℝ} (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (hyp : UEGEndpointBound η C)
    (hC : 0 ≤ C) : ∃ J > 0, ∀ A B : SpinMatrix, A.PosSemidef → B.PosSemidef →
      let r := max A.trace.re B.trace.re
      |sswEnergy energy η A 0 - sswEnergy energy η B 0| ≤
        J*(r^(1/3:ℝ)+r^(2/3:ℝ))*hilbertSchmidt (A-B) := by
  have hK := L.rate.one_le
  refine ⟨3*C+2*(2*(H.loCoeff+2*K)+2*(2*K+1)),by linarith only [hC,H.lo_nonneg,hK],?_⟩
  intro A B hA hB
  simpa only [sswEnergy_zero_wavevector] using unequal_trace_lipschitz L H sob hyp hC A B hA hB

/-- At fixed charge, the zero-wavevector gas is a symmetric convex function
of either spin fraction. The last identity selects the smaller fraction. -/
theorem CoulombGasInputs.population_curve {η : Mollifier} {K r : ℝ} (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (hr : 0 < r) :
    let f := fun t : ℝ => uniformEnergy energy η (populations (r-t*r) (t*r))
    ConvexOn ℝ (Set.Icc 0 1) f ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1, f (1-t) = f t) ∧
    ∀ {A : SpinMatrix} (hA : A.PosSemidef), A.trace.re = r →
      minorityPopulation hA/r ∈ Set.Icc (0:ℝ) (1/2) ∧
      uniformEnergy energy η A = f (minorityPopulation hA/r) := by
  intro f
  let path : ℝ →ᵃ[ℝ] SpinMatrix := AffineMap.lineMap (populations r 0) (populations 0 r)
  have h0 : populations r 0 ∈ fixedCharge r := ⟨population_pos hr.le le_rfl,by rw [population_trace,add_zero]⟩
  have h1 : populations 0 r ∈ fixedCharge r := ⟨population_pos le_rfl hr.le,by rw [population_trace,zero_add]⟩
  have conv := coulomb_ssw_convex_fixed_charge η L.localization (L.kinematics H sob) hr (0:Position)
  simp only [sswEnergy_zero_wavevector] at conv
  have eq : f = uniformEnergy energy η ∘ path := funext fun t => by simp [f,path,population_line]
  refine ⟨eq ▸ (conv.comp_affineMap path).subset (fun _ ht => conv.1.lineMap_mem h0 h1 ht) (convex_Icc ..),?_,?_⟩
  · intro t ht
    have a : 0 ≤ t*r := mul_nonneg ht.1 hr.le
    have b : 0 ≤ r-t*r := by linarith only [mul_le_mul_of_nonneg_right ht.2 hr.le]
    dsimp only [f]
    rw [show r-(1-t)*r=t*r by ring,show (1-t)*r=r-t*r by ring]
    exact uniform_swap L a b
  · intro A hA tr
    have m := minority_mem hA
    rw [tr] at m
    refine ⟨⟨div_nonneg m.1 hr.le,(div_le_iff₀ hr).2 (by linarith only [m.2])⟩,?_⟩
    simpa only [f,div_mul_cancel₀ _ hr.ne',tr] using uniform_populations L hA

end TSGA.ManyBody
