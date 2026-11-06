module

public import Mathlib.NumberTheory.SelbergSieve
public import PaperP1.Arithmetic.IntervalDivisibilityCount

/-! # Actual reciprocal divisibility data and the concrete Selberg quadratic sieve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReciprocalDivisibilitySieve
open Finset PaperP1 NormalizedWindowSets IntervalDivisibilityCount
open scoped Classical

def density : ArithmeticFunction ℝ := ⟨fun d ↦ 1/(d : ℝ),by simp⟩

theorem density_mul (m n : ℕ) : density (m*n)=density m*density n := by
  change 1/((m*n : ℕ) : ℝ)=1/(m : ℝ)*(1/(n : ℝ))
  rw [Nat.cast_mul,one_div,one_div,one_div,mul_inv_rev]
  ring

theorem density_multiplicative : density.IsMultiplicative := by
  refine ⟨?_,fun {m n} _ ↦ density_mul m n⟩
  norm_num [density]

def sieve (x L P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := values x L
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ by norm_num
  totalMass := ((L+1 : ℕ) : ℝ)
  nu := density
  nu_mult := density_multiplicative
  nu_pos_of_prime := by
    intro p hp hpd
    change 0 < (1 : ℝ)/(p : ℝ)
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := by
    intro p hp hpd
    change (1 : ℝ)/(p : ℝ) < 1
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
    apply (div_lt_iff₀ hpr).mpr
    simpa only [one_mul] using (show (1 : ℝ) < p by exact_mod_cast hp.one_lt)

theorem multSum_eq_hits (x L P : ℕ) (hP : Squarefree P) (d : ℕ) :
    (sieve x L P hP).multSum d=((hits d x L).card : ℝ) := by
  simp only [BoundingSieve.multSum,sieve,hits,sum_boole]

theorem siftedSum_eq_card (x L P : ℕ) (hP : Squarefree P) :
    (sieve x L P hP).siftedSum=((values x L).filter (fun n ↦ P.Coprime n)).card := by
  simp only [BoundingSieve.siftedSum,sieve,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]
  apply sum_congr rfl
  intro n hn
  split_ifs with hc
  · exact ite_eq_left hc
  · exact ite_eq_right hc

theorem rem_abs_le_one (x L P : ℕ) (hP : Squarefree P) (hx : 2 ≤ x) (d : ℕ) (hd : 0 < d) :
    |(sieve x L P hP).rem d| ≤ 1 := by
  have hc := count_bounds (L := L) hx hd
  rw [BoundingSieve.rem,multSum_eq_hits]
  change |((hits d x L).card : ℝ)-(1/(d : ℝ))*((L+1 : ℕ) : ℝ)| ≤ 1
  have he : (1/(d : ℝ))*((L+1 : ℕ) : ℝ)=((L+1 : ℕ) : ℝ)/(d : ℝ) := by ring
  rw [he]
  exact abs_le.mpr ⟨by linarith [hc.1],by linarith [hc.2]⟩

theorem error_sum_bound (x L P : ℕ) (hP : Squarefree P) (hx : 2 ≤ x) (μplus : ℕ → ℝ) :
    (sieve x L P hP).errSum μplus ≤ ∑ d ∈ P.divisors, |μplus d| := by
  unfold BoundingSieve.errSum
  apply sum_le_sum
  intro d hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have he := mul_le_mul_of_nonneg_left (rem_abs_le_one x L P hP hx d hdpos) (abs_nonneg (μplus d))
  simpa only [mul_one] using he

theorem actual_lambda_sieve (x L P : ℕ) (hP : Squarefree P) (hx : 2 ≤ x) (w : ℕ → ℝ) (hw : w 1=1) :
    (((values x L).filter (fun n ↦ P.Coprime n)).card : ℝ) ≤
      ((L+1 : ℕ) : ℝ)*(∑ l ∈ P.divisors, ((sieve x L P hP).selbergTerms l)⁻¹*
        (∑ d ∈ P.divisors, if l ∣ d then (1/(d : ℝ))*w d else 0)^2)+
      ∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| := by
  have hs := (sieve x L P hP).siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared w) (BoundingSieve.upperMoebius_lambdaSquared w hw)
  rw [siftedSum_eq_card,BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq] at hs
  have he := error_sum_bound x L P hP hx (BoundingSieve.lambdaSquared w)
  exact hs.trans (add_le_add le_rfl he)
end ReciprocalDivisibilitySieve
