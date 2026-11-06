module

public import PaperP1.Arithmetic.SelbergLambdaError


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimeSelbergCoefficients
open Finset Nat PaperP1
open scoped Classical

def sieve (Z : ℕ) : BoundingSieve :=
  ReciprocalDivisibilitySieve.sieve 2 0 (primorial Z) (squarefree_primorial Z)

def support (Z : ℕ) : Finset ℕ := (primorial Z).divisors

def coefficient (Z d : ℕ) : ℝ := BoundingSieve.lambdaSquared (OptimalSelbergWeights.weight (sieve Z) Z) d

def denominator (Z : ℕ) : ℝ := OptimalSelbergWeights.denominator (sieve Z) Z

theorem denominator_pos (Z : ℕ) (hZ : 1 ≤ Z) : 0 < denominator Z :=
  OptimalSelbergWeights.denominator_pos (sieve Z) Z hZ

theorem denominator_log_lower (Z : ℕ) : Real.log ((Z+1 : ℕ) : ℝ)/2 ≤ denominator Z :=
  SquarefreeHarmonicLower.denominator_log_lower 2 0 Z

theorem main_mass (Z : ℕ) (hZ : 1 ≤ Z) :
    (∑ d ∈ support Z, coefficient Z d/(d : ℝ))=1/denominator Z := by
  have hh := OptimalSelbergWeights.main_sum_exact (sieve Z) Z hZ
  change (∑ d ∈ support Z, coefficient Z d*(1/(d : ℝ)))=1/denominator Z at hh
  simpa only [mul_one_div] using hh

theorem absolute_mass (Z : ℕ) (hZ : 1 ≤ Z) :
    (∑ d ∈ support Z, |coefficient Z d|) ≤ (Z : ℝ)^4 :=
  SelbergLambdaError.reciprocal_error_bound 2 0 (primorial Z) Z (squarefree_primorial Z) hZ

theorem coefficient_support (Z d : ℕ) (hd : d ∈ support Z) (hZd : Z^2 < d) : coefficient Z d=0 := by
  have hdP : d ∣ (sieve Z).prodPrimes := Nat.dvd_of_mem_divisors hd
  unfold coefficient BoundingSieve.lambdaSquared
  apply sum_eq_zero
  intro a ha
  apply sum_eq_zero
  intro b hb
  by_cases he : d=Nat.lcm a b
  · rw [ite_eq_left he]
    have haP : a ∣ (sieve Z).prodPrimes := (Nat.dvd_of_mem_divisors ha).trans hdP
    have hbP : b ∣ (sieve Z).prodPrimes := (Nat.dvd_of_mem_divisors hb).trans hdP
    by_cases hZa : Z < a
    · rw [OptimalSelbergWeights.weight_support (sieve Z) Z a haP hZa,zero_mul]
    · by_cases hZb : Z < b
      · rw [OptimalSelbergWeights.weight_support (sieve Z) Z b hbP hZb,mul_zero]
      · have hAB : Nat.lcm a b ≤ a*b := Nat.le_of_dvd
          (Nat.mul_pos (Nat.pos_of_mem_divisors ha) (Nat.pos_of_mem_divisors hb))
          (Nat.lcm_dvd_iff.mpr ⟨⟨b,rfl⟩,⟨a,Nat.mul_comm _ _⟩⟩)
        have hle : d ≤ Z^2 := by
          rw [he,pow_two]
          exact hAB.trans (Nat.mul_le_mul (Nat.le_of_not_gt hZa) (Nat.le_of_not_gt hZb))
        omega
  · rw [ite_eq_right he]

theorem lambda_divisor_identity (P n : ℕ) (hP : P ≠ 0) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if d ∣ n then BoundingSieve.lambdaSquared w d else 0)=
      (∑ d ∈ P.divisors, if d ∣ n then w d else 0)^2 := by
  calc
    _ = ∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d=Nat.lcm a b then (if d ∣ n then w a*w b else 0) else 0 := by
      apply sum_congr rfl
      intro d hd
      by_cases hdn : d ∣ n
      · simp only [hdn,ite_true,BoundingSieve.lambdaSquared]
      · simp only [hdn,ite_false,ite_self,sum_const_zero]
    _ = ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d=Nat.lcm a b then (if d ∣ n then w a*w b else 0) else 0 :=
      SelbergLambdaError.divisor_lcm_extension P (fun a b d ↦ if d ∣ n then w a*w b else 0)
    _ = ∑ a ∈ P.divisors, ∑ b ∈ P.divisors, if Nat.lcm a b ∣ n then w a*w b else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      have hl : Nat.lcm a b ∈ P.divisors := mem_divisors.mpr
        ⟨Nat.lcm_dvd_iff.mpr ⟨Nat.dvd_of_mem_divisors ha,Nat.dvd_of_mem_divisors hb⟩,hP⟩
      exact sum_ite_eq_of_mem' P.divisors (Nat.lcm a b) _ hl
    _ = _ := by
      rw [pow_two,sum_mul_sum]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      by_cases han : a ∣ n <;> by_cases hbn : b ∣ n <;> simp [Nat.lcm_dvd_iff,han,hbn]

theorem divisor_nonneg (Z n : ℕ) : 0 ≤ ∑ d ∈ support Z, if d ∣ n then coefficient Z d else 0 := by
  change 0 ≤ ∑ d ∈ (primorial Z).divisors,
    if d ∣ n then BoundingSieve.lambdaSquared (OptimalSelbergWeights.weight (sieve Z) Z) d else 0
  rw [lambda_divisor_identity (primorial Z) n (primorial_ne_zero Z)]
  exact sq_nonneg _

theorem prime_value (Z p : ℕ) (hZ : 1 ≤ Z) (hp : p.Prime) (hZp : Z < p) :
    (∑ d ∈ support Z, if d ∣ p then coefficient Z d else 0)=1 := by
  change (∑ d ∈ (primorial Z).divisors,
    if d ∣ p then BoundingSieve.lambdaSquared (OptimalSelbergWeights.weight (sieve Z) Z) d else 0)=1
  rw [lambda_divisor_identity (primorial Z) p (primorial_ne_zero Z)]
  have hInner : (∑ d ∈ (primorial Z).divisors,
      if d ∣ p then OptimalSelbergWeights.weight (sieve Z) Z d else 0)=1 := by
    calc
      _ = (if 1 ∣ p then OptimalSelbergWeights.weight (sieve Z) Z 1 else 0) := by
        apply sum_eq_single 1
        · intro d hd hne
          by_cases hdp : d ∣ p
          · rw [ite_eq_left hdp]
            rcases (Nat.dvd_prime hp).mp hdp with he | he
            · exact (hne he).elim
            · subst d
              exact OptimalSelbergWeights.weight_support (sieve Z) Z p (Nat.dvd_of_mem_divisors hd) hZp
          · rw [ite_eq_right hdp]
        · intro hnot
          exact (hnot (Nat.one_mem_divisors.mpr (primorial_ne_zero Z))).elim
      _ = 1 := by rw [ite_eq_left (one_dvd p),OptimalSelbergWeights.weight_one (sieve Z) Z hZ]
  rw [hInner]
  norm_num
end PaperP1.PrimeSelbergCoefficients
