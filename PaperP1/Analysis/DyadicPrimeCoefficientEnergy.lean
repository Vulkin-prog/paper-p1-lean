module

public import PaperP1.Arithmetic.LogarithmicPrimeCount
public import PaperP1.Analysis.DirichletPolynomialMeanValue


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DyadicPrimeCoefficientEnergy
open Finset Filter PaperP1
open scoped Classical

def constant : ℝ := 42*Real.log 2

theorem constant_pos : 0 < constant := mul_pos (by norm_num) (Real.log_pos (by norm_num))

theorem prime_card_bound (A : ℝ) (hA : 2 ≤ A) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ A ≤ p ∧ (p : ℝ) ≤ 2*A) :
    (P.card : ℝ) ≤ constant*A/Real.log A := by
  have hAP : 0 < A := by linarith only [hA]
  have hLogA : 0 < Real.log A := Real.log_pos (by linarith only [hA])
  have hLog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let M := ⌈2*A⌉₊
  have hML : 2*A ≤ (M : ℝ) := Nat.le_ceil _
  have hMA : A ≤ (M : ℝ) := by linarith only [hML,hA]
  have hM4 : 4 ≤ M := by
    have hh : (4 : ℝ) ≤ M := by linarith only [hML,hA]
    exact_mod_cast hh
  have hMU : (M : ℝ) ≤ 3*A := by
    have hh := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*A)).le
    change (M : ℝ) ≤ 2*A+1 at hh
    linarith only [hh,hA]
  have hSub : P ⊆ DefectCounting.smallPrimesUpTo M := by
    intro p hp
    have hh := hP p hp
    exact DefectCounting.mem_smallPrimesUpTo.mpr ⟨hh.1,by exact_mod_cast hh.2.2.trans hML⟩
  have hCard : (P.card : ℝ) ≤ (LogarithmicPrimeCount.primeCount M : ℝ) := by exact_mod_cast card_le_card hSub
  have hLogAM := Real.log_le_log hAP hMA
  have hLogM : 0 ≤ Real.log (M : ℝ) := hLogA.le.trans hLogAM
  apply (le_div_iff₀ hLogA).mpr
  calc
    _ ≤ (P.card : ℝ)*Real.log (M : ℝ) := mul_le_mul_of_nonneg_left hLogAM (Nat.cast_nonneg _)
    _ ≤ (LogarithmicPrimeCount.primeCount M : ℝ)*Real.log (M : ℝ) := mul_le_mul_of_nonneg_right hCard hLogM
    _ ≤ 14*Real.log 2*(M : ℝ) := LogarithmicPrimeCount.log_mul_primeCount_le hM4
    _ ≤ 14*Real.log 2*(3*A) := mul_le_mul_of_nonneg_left hMU (by positivity)
    _ = _ := by unfold constant; ring

theorem coefficient_energy (A : ℝ) (hA : 2 ≤ A) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ A ≤ p ∧ (p : ℝ) ≤ 2*A)
    (f : ℕ → ℂ) (hf : ∀ p ∈ P, ‖f p‖ ≤ 1) :
    (∑ p ∈ P, ‖f p/(p : ℂ)‖^2) ≤ constant/(A*Real.log A) := by
  have hAP : 0 < A := by linarith only [hA]
  have hLog : 0 < Real.log A := Real.log_pos (by linarith only [hA])
  have hPoint : ∀ p ∈ P, ‖f p/(p : ℂ)‖ ≤ 1/A := by
    intro p hp
    rw [norm_div,RCLike.norm_natCast]
    exact (div_le_div_of_nonneg_right (hf p hp) (Nat.cast_nonneg p)).trans
      (one_div_le_one_div_of_le hAP (hP p hp).2.1)
  calc
    _ ≤ ∑ _p ∈ P, (1/A)^2 := by
      apply sum_le_sum
      intro p hp
      exact pow_le_pow_left₀ (norm_nonneg _) (hPoint p hp) 2
    _ = (P.card : ℝ)*(1/A)^2 := by rw [sum_const,nsmul_eq_mul]
    _ ≤ (constant*A/Real.log A)*(1/A)^2 :=
      mul_le_mul_of_nonneg_right (prime_card_bound A hA P hP) (sq_nonneg _)
    _ = _ := by field_simp [hAP.ne',hLog.ne']
end PaperP1.DyadicPrimeCoefficientEnergy
