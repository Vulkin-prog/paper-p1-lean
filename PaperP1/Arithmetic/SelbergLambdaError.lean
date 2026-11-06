module

public import PaperP1.Arithmetic.SquarefreeHarmonicLower

/-! # Actual Selberg lambda-square error and finite interval counting bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelbergLambdaError
open Finset Nat PaperP1
open scoped Classical

theorem divisor_lcm_extension (P : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
      if d = Nat.lcm a b then f a b d else 0)=
    ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
      if d = Nat.lcm a b then f a b d else 0 := by
  congr! 1 with d hd
  rw [mem_divisors] at hd
  suffices ∀ a b, (a ∣ d ∧ b ∣ d ∧ d = Nat.lcm a b)=(d = Nat.lcm a b) by
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1,sum_filter,ite_sum_zero,← ite_and,this]
  simp +contextual [← and_assoc,Nat.dvd_lcm_left,Nat.dvd_lcm_right]

theorem lambda_abs_point (w : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared w d| ≤
      ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d=Nat.lcm a b then |w a| * |w b| else 0 := by
  unfold BoundingSieve.lambdaSquared
  calc
    _ ≤ ∑ a ∈ d.divisors, |∑ b ∈ d.divisors, if d=Nat.lcm a b then w a*w b else 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        |if d=Nat.lcm a b then w a*w b else 0| := by
      apply sum_le_sum
      intro a ha
      exact abs_sum_le_sum_abs _ _
    _ = _ := by simp only [apply_ite abs,abs_mul,abs_zero]

theorem lambda_abs_sum (P : ℕ) (hP : P ≠ 0) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d|) ≤
      (∑ d ∈ P.divisors, |w d|)^2 := by
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d=Nat.lcm a b then |w a| * |w b| else 0 := by
      exact sum_le_sum (fun d hd ↦ lambda_abs_point w d)
    _ = ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d=Nat.lcm a b then |w a| * |w b| else 0 :=
      divisor_lcm_extension P (fun a b _ ↦ |w a| * |w b|)
    _ = ∑ a ∈ P.divisors, ∑ b ∈ P.divisors, |w a| * |w b| := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      have hl : Nat.lcm a b ∈ P.divisors := mem_divisors.mpr
        ⟨Nat.lcm_dvd_iff.mpr ⟨Nat.dvd_of_mem_divisors ha,Nat.dvd_of_mem_divisors hb⟩,hP⟩
      exact sum_ite_eq_of_mem' P.divisors (Nat.lcm a b) _ hl
    _ = _ := by rw [pow_two,sum_mul]; simp only [mul_sum]

theorem reciprocal_weight_abs (x L P Z d : ℕ) (hP : Squarefree P) (hZ : 1 ≤ Z)
    (hd : d ∣ P) :
    |OptimalSelbergWeights.weight (ReciprocalDivisibilitySieve.sieve x L P hP) Z d| ≤ d := by
  have hb := OptimalSelbergWeights.weight_abs_bound
    (ReciprocalDivisibilitySieve.sieve x L P hP) Z d hZ hd
  change |OptimalSelbergWeights.weight (ReciprocalDivisibilitySieve.sieve x L P hP) Z d| ≤
    1/(1/(d : ℝ)) at hb
  simpa only [one_div,inv_inv] using hb

theorem reciprocal_weight_sum (x L P Z : ℕ) (hP : Squarefree P) (hZ : 1 ≤ Z) :
    (∑ d ∈ P.divisors,
      |OptimalSelbergWeights.weight (ReciprocalDivisibilitySieve.sieve x L P hP) Z d|) ≤
      (Z : ℝ)^2 := by
  let s := ReciprocalDivisibilitySieve.sieve x L P hP
  have he : (∑ d ∈ P.divisors, |OptimalSelbergWeights.weight s Z d|)=
      ∑ d ∈ P.divisors.filter (fun d ↦ d ≤ Z), |OptimalSelbergWeights.weight s Z d| := by
    symm
    apply sum_subset (filter_subset _ _)
    intro d hd hnot
    have hgt : Z < d := lt_of_not_ge (fun hh ↦ hnot (mem_filter.mpr ⟨hd,hh⟩))
    rw [OptimalSelbergWeights.weight_support s Z d (Nat.dvd_of_mem_divisors hd) hgt,abs_zero]
  rw [he]
  have hsub : P.divisors.filter (fun d ↦ d ≤ Z) ⊆ Icc 1 Z := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (mem_filter.mp hd).1,(mem_filter.mp hd).2⟩
  calc
    _ ≤ ∑ d ∈ P.divisors.filter (fun d ↦ d ≤ Z), (d : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact reciprocal_weight_abs x L P Z d hP hZ (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
    _ ≤ ∑ d ∈ Icc 1 Z, (d : ℝ) := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ ≤ ∑ d ∈ Icc 1 Z, (Z : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact_mod_cast (mem_Icc.mp hd).2
    _ = (Z : ℝ)^2 := by simp [pow_two,Nat.card_Icc]

theorem reciprocal_error_bound (x L P Z : ℕ) (hP : Squarefree P) (hZ : 1 ≤ Z) :
    (∑ d ∈ P.divisors,
      |BoundingSieve.lambdaSquared (OptimalSelbergWeights.weight
        (ReciprocalDivisibilitySieve.sieve x L P hP) Z) d|) ≤ (Z : ℝ)^4 := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have he := lambda_abs_sum P hP0
    (OptimalSelbergWeights.weight (ReciprocalDivisibilitySieve.sieve x L P hP) Z)
  have hw := reciprocal_weight_sum x L P Z hP hZ
  have hn : 0 ≤ ∑ d ∈ P.divisors,
      |OptimalSelbergWeights.weight (ReciprocalDivisibilitySieve.sieve x L P hP) Z d| :=
    sum_nonneg (fun _ _ ↦ abs_nonneg _)
  nlinarith [sq_nonneg ((Z : ℝ)^2 - ∑ d ∈ P.divisors,
    |OptimalSelbergWeights.weight (ReciprocalDivisibilitySieve.sieve x L P hP) Z d|)]

theorem actual_optimized_sieve (x L P Z : ℕ) (hP : Squarefree P) (hx : 2 ≤ x) (hZ : 1 ≤ Z) :
    (((NormalizedWindowSets.values x L).filter (fun n ↦ P.Coprime n)).card : ℝ) ≤
      ((L+1 : ℕ) : ℝ)/OptimalSelbergWeights.denominator
        (ReciprocalDivisibilitySieve.sieve x L P hP) Z+(Z : ℝ)^4 := by
  let s := ReciprocalDivisibilitySieve.sieve x L P hP
  let w := OptimalSelbergWeights.weight s Z
  have hs := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared w)
    (BoundingSieve.upperMoebius_lambdaSquared w (OptimalSelbergWeights.weight_one s Z hZ))
  have hm := OptimalSelbergWeights.main_sum_exact s Z hZ
  have herr : s.errSum (BoundingSieve.lambdaSquared w) ≤ (Z : ℝ)^4 :=
    (ReciprocalDivisibilitySieve.error_sum_bound x L P hP hx _).trans
      (reciprocal_error_bound x L P Z hP hZ)
  rw [hm] at hs
  calc
    _ = s.siftedSum := (ReciprocalDivisibilitySieve.siftedSum_eq_card x L P hP).symm
    _ ≤ s.totalMass*(1/OptimalSelbergWeights.denominator s Z)+s.errSum (BoundingSieve.lambdaSquared w) := hs
    _ ≤ ((L+1 : ℕ) : ℝ)/OptimalSelbergWeights.denominator s Z+(Z : ℝ)^4 := by
      change ((L+1 : ℕ) : ℝ)*(1/OptimalSelbergWeights.denominator s Z)+
        s.errSum (BoundingSieve.lambdaSquared w) ≤ _
      have he : ((L+1 : ℕ) : ℝ)*(1/OptimalSelbergWeights.denominator s Z)=
        ((L+1 : ℕ) : ℝ)/OptimalSelbergWeights.denominator s Z := by ring
      rw [he]
      exact add_le_add le_rfl herr

theorem actual_primorial_sieve (x L Z : ℕ) (hx : 2 ≤ x) (hZ : 1 ≤ Z) :
    (((NormalizedWindowSets.values x L).filter (fun n ↦ (primorial Z).Coprime n)).card : ℝ) ≤
      2*((L+1 : ℕ) : ℝ)/Real.log ((Z+1 : ℕ) : ℝ)+(Z : ℝ)^4 := by
  let s := ReciprocalDivisibilitySieve.sieve x L (primorial Z) (squarefree_primorial Z)
  have hh := actual_optimized_sieve x L (primorial Z) Z (squarefree_primorial Z) hx hZ
  have hG := SquarefreeHarmonicLower.denominator_log_lower x L Z
  have hlog : 0 < Real.log ((Z+1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z+1))
  have hden : 0 < Real.log ((Z+1 : ℕ) : ℝ)/2 := by positivity
  have hb : ((L+1 : ℕ) : ℝ)/OptimalSelbergWeights.denominator s Z ≤
      2*((L+1 : ℕ) : ℝ)/Real.log ((Z+1 : ℕ) : ℝ) := by
    calc
      _ ≤ ((L+1 : ℕ) : ℝ)/(Real.log ((Z+1 : ℕ) : ℝ)/2) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden hG
      _ = _ := by ring
  exact hh.trans (add_le_add hb le_rfl)
end PaperP1.SelbergLambdaError


