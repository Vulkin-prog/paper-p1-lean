module

public import PaperP1.Probability.DifferenceCoefficients
public import PaperP1.Probability.PoissonExponential
public import PaperP1.Probability.QuadraticPoisson

/-! # The exact perturbation masses in companion T23.1

The pointwise argument works throughout 0≤a≤2, the full positivity interval
of the quadratic reference at mean one. The source range 0≤a≤1 is included.
All factorials and perturbation coefficients are literal finite quantities.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MomentObstructionMass

open MeasureTheory PaperP1.Probability PaperP1.PoissonSequence PaperP1.DifferenceCoefficients
  PaperP1.FiniteLawEmbedding PaperP1.CharlierQuadratic Finset

def qMass (a : ℝ) : ℕ → ℝ := quadraticMass 1 a

def sourceConstant (a : ℝ) : ℝ := (1 - a / 2) * Real.exp (-1)

def epsilon (m : ℕ) (a : ℝ) : ℝ := sourceConstant a / (2 * (m.factorial : ℝ))

def pMass (m : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  qMass a k + epsilon m a * ((forwardDifference : SignedLaw ℝ) ^ m).coeff k

theorem sourceConstant_nonneg (a : ℝ) (ha : a ≤ 2) : 0 ≤ sourceConstant a :=
  mul_nonneg (by linarith) (Real.exp_pos _).le

theorem sourceConstant_pos (a : ℝ) (ha : a < 2) : 0 < sourceConstant a :=
  mul_pos (by linarith) (Real.exp_pos _)

theorem epsilon_nonneg (m : ℕ) (a : ℝ) (ha : a ≤ 2) : 0 ≤ epsilon m a :=
  div_nonneg (sourceConstant_nonneg a ha) (by positivity)

theorem epsilon_mul_factorial (m : ℕ) (a : ℝ) :
    epsilon m a * (m.factorial : ℝ) = sourceConstant a / 2 := by
  unfold epsilon
  field_simp

theorem qMass_lower (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    sourceConstant a / (k.factorial : ℝ) ≤ qMass a k := by
  have hmin := quadratic_ge_minimum 1 (by norm_num) k
  norm_num [minimumMagnitude, theta] at hmin
  have hmul := mul_le_mul_of_nonneg_left hmin (show 0 ≤ a / 2 by positivity)
  have hb : 1 - a / 2 ≤ 1 + a / 2 * (((k : ℝ) - 1) ^ 2 - k) := by
    unfold quadratic at hmul
    linarith
  have hbase : 0 ≤ mass 1 k := (mass_pos 1 (by norm_num) k).le
  have h := mul_le_mul_of_nonneg_left hb hbase
  rw [qMass, quadraticMass_formula 1 a (by norm_num)]
  convert h using 1
  · unfold sourceConstant mass
    norm_num
    ring
  · norm_num

theorem qMass_nonneg (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (k : ℕ) : 0 ≤ qMass a k :=
  (div_nonneg (sourceConstant_nonneg a ha2) (by positivity)).trans (qMass_lower a ha0 k)

theorem abs_difference_coeff_le_ratio (m k : ℕ) :
    |((forwardDifference : SignedLaw ℝ) ^ m).coeff k| ≤ (m.factorial : ℝ) / (k.factorial : ℝ) :=
  (le_div_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mpr (abs_coeff_mul_factorial_le m k)

theorem perturbation_abs_le (m : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (k : ℕ) :
    |epsilon m a * ((forwardDifference : SignedLaw ℝ) ^ m).coeff k| ≤ qMass a k / 2 := by
  rw [abs_mul, abs_of_nonneg (epsilon_nonneg m a ha2)]
  calc
    _ ≤ epsilon m a * ((m.factorial : ℝ) / (k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (abs_difference_coeff_le_ratio m k) (epsilon_nonneg m a ha2)
    _ = (sourceConstant a / (k.factorial : ℝ)) / 2 := by
      unfold epsilon
      field_simp
    _ ≤ qMass a k / 2 := div_le_div_of_nonneg_right (qMass_lower a ha0 k) (by norm_num)

theorem pMass_pointwise_bounds (m : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (k : ℕ) :
    qMass a k / 2 ≤ pMass m a k ∧ pMass m a k ≤ 3 / 2 * qMass a k := by
  have h := abs_le.mp (perturbation_abs_le m a ha0 ha2 k)
  unfold pMass
  constructor <;> linarith

theorem pMass_nonneg (m : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (k : ℕ) : 0 ≤ pMass m a k :=
  (div_nonneg (qMass_nonneg a ha0 ha2 k) (by norm_num)).trans (pMass_pointwise_bounds m a ha0 ha2 k).1

theorem hasSum_qMass (a : ℝ) : HasSum (qMass a) 1 := hasSum_quadraticMass 1 a (by norm_num)

theorem hasSum_difference (m : ℕ) (hm : 1 ≤ m) :
    HasSum (fun k ↦ ((forwardDifference : SignedLaw ℝ) ^ m).coeff k) 0 := by
  have h := (summable_coeff ((forwardDifference : SignedLaw ℝ) ^ m)).hasSum
  rwa [tsum_coeff_eq_mass, map_pow, totalMass_forwardDifference, zero_pow (by omega : m ≠ 0)] at h

theorem hasSum_pMass (m : ℕ) (hm : 1 ≤ m) (a : ℝ) : HasSum (pMass m a) 1 := by
  have h := (hasSum_qMass a).add ((hasSum_difference m hm).mul_left (epsilon m a))
  convert h using 1
  · rfl
  · ring

def qLaw (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) : ProbabilityMeasure ℕ :=
  AtomicProbability.ofMass (qMass a) (qMass_nonneg a ha0 ha2) (hasSum_qMass a)

def pLaw (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) : ProbabilityMeasure ℕ :=
  AtomicProbability.ofMass (pMass m a) (pMass_nonneg m a ha0 ha2) (hasSum_pMass m hm a)

theorem qLaw_real_singleton (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (k : ℕ) :
    (qLaw a ha0 ha2 : Measure ℕ).real {k} = qMass a k := AtomicProbability.ofMass_real_singleton _ _ _ _

theorem pLaw_real_singleton (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (k : ℕ) :
    (pLaw m hm a ha0 ha2 : Measure ℕ).real {k} = pMass m a k :=
  AtomicProbability.ofMass_real_singleton _ _ _ _

theorem qLaw_signed_identity (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    (qLaw a ha0 ha2 : Measure ℕ).toSignedMeasure = QuadraticPoisson.reference 1 a :=
  AtomicProbability.ofMass_toSignedMeasure _ _ _

theorem pLaw_signed_identity (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    (pLaw m hm a ha0 ha2 : Measure ℕ).toSignedMeasure =
      QuadraticPoisson.reference 1 a + epsilon m a • embed ((forwardDifference : SignedLaw ℝ) ^ m) := by
  apply AtomicSignedLaw.signedMeasure_ext_singleton
  intro k
  rw [Measure.toSignedMeasure_apply_measurable (measurableSet_singleton k), pLaw_real_singleton,
    _root_.add_apply, _root_.smul_apply, embed_singleton, smul_eq_mul]
  rw [QuadraticPoisson.reference,
    AtomicSignedLaw.ofSequence_singleton (hasSum_quadraticMass 1 a (by norm_num)).summable]
  rfl

end PaperP1.MomentObstructionMass
