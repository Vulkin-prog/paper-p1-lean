module

public import PaperP1.Arithmetic.IntervalDivisibilityCount
public import PaperP1.Analysis.DirichletPolynomialMeanValue

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.WeightedDivisorSquare
open Finset PaperP1
open scoped Classical

def divisorSum {ι : Type*} (S : Finset ι) (d : ι → ℕ) (w : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ S, if d a ∣ n then w a else 0

def kernel {ι : Type*} (S : Finset ι) (d : ι → ℕ) (w : ι → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, w a*w b/(Nat.lcm (d a) (d b) : ℝ)

theorem divisorSum_nonneg {ι : Type*} (S : Finset ι) (d : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (n : ℕ) : 0 ≤ divisorSum S d w n := by
  apply sum_nonneg
  intro a ha
  split_ifs
  · exact hw a ha
  · exact le_rfl

theorem kernel_nonneg {ι : Type*} (S : Finset ι) (d : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) : 0 ≤ kernel S d w := by
  apply sum_nonneg
  intro a ha
  apply sum_nonneg
  intro b hb
  exact div_nonneg (mul_nonneg (hw a ha) (hw b hb)) (Nat.cast_nonneg _)

theorem square_expansion {ι : Type*} (S : Finset ι) (d : ι → ℕ) (w : ι → ℝ) (n : ℕ) :
    (divisorSum S d w n)^2=
      ∑ a ∈ S, ∑ b ∈ S, if Nat.lcm (d a) (d b) ∣ n then w a*w b else 0 := by
  unfold divisorSum
  rw [pow_two,sum_mul]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  by_cases ha' : d a ∣ n <;> by_cases hb' : d b ∣ n <;>
    simp only [Nat.lcm_dvd_iff,ha',hb',ite_true,ite_false,true_and,false_and,and_false,mul_zero,zero_mul]

theorem square_sum_identity {ι : Type*} (S : Finset ι) (d : ι → ℕ) (w : ι → ℝ) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, (divisorSum S d w n)^2)=
      ∑ a ∈ S, ∑ b ∈ S, ((X/Nat.lcm (d a) (d b) : ℕ) : ℝ)*(w a*w b) := by
  simp_rw [square_expansion]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  rw [← sum_filter,sum_const,nsmul_eq_mul,Nat.Ioc_filter_dvd_card_eq_div]

theorem square_sum_bound {ι : Type*} (S : Finset ι) (d : ι → ℕ) (w : ι → ℝ)
    (hd : ∀ a ∈ S, 0 < d a) (hw : ∀ a ∈ S, 0 ≤ w a) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, (divisorSum S d w n)^2) ≤ (X : ℝ)*kernel S d w := by
  rw [square_sum_identity,kernel,mul_sum]
  apply sum_le_sum
  intro a ha
  rw [mul_sum]
  apply sum_le_sum
  intro b hb
  have hp : (0 : ℝ) < Nat.lcm (d a) (d b) := by exact_mod_cast Nat.lcm_pos (hd a ha) (hd b hb)
  have hfloor : ((X/Nat.lcm (d a) (d b) : ℕ) : ℝ) ≤ (X : ℝ)/(Nat.lcm (d a) (d b) : ℝ) := by
    apply (le_div_iff₀ hp).mpr
    exact_mod_cast Nat.div_mul_le_self X (Nat.lcm (d a) (d b))
  have hm := mul_le_mul_of_nonneg_right hfloor (mul_nonneg (hw a ha) (hw b hb))
  exact hm.trans_eq (by ring)
end PaperP1.WeightedDivisorSquare
