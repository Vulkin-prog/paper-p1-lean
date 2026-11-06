module

public import PaperP1.Arithmetic.PrimeLogMertens
public import PaperP1.Analysis.ReciprocalSquareTail

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimeDampingBudget
open Finset PaperP1
open scoped Classical

theorem damping_bounds (x σ : ℝ) (hx : 1 ≤ x) (hσ : 0 ≤ σ) :
    0 ≤ x^(-σ) ∧ x^(-σ) ≤ 1 := by
  constructor
  · exact Real.rpow_nonneg (by linarith only [hx]) _
  · simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hx (neg_nonpos.mpr hσ)

theorem damping_defect (x σ : ℝ) (hx : 1 ≤ x) (hσ : 0 ≤ σ) :
    0 ≤ 1-x^(-σ) ∧ 1-x^(-σ) ≤ σ*Real.log x := by
  have hp : 0 < x := by linarith only [hx]
  have hExp : Real.exp (-σ*Real.log x)=x^(-σ) := by
    rw [Real.rpow_def_of_pos hp]
    congr 1
    ring
  have hh := Real.add_one_le_exp (-σ*Real.log x)
  rw [hExp] at hh
  exact ⟨sub_nonneg.mpr (damping_bounds x σ hx hσ).2,by linarith only [hh]⟩

theorem prime_log_sum_bound (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X) :
    (∑ p ∈ P, Real.log (p : ℝ)/(p : ℝ)) ≤ Real.log (X : ℝ)+(Real.log 4+4) := by
  have he : (∑ p ∈ P, Real.log (p : ℝ)/(p : ℝ))=∑ p ∈ P, PrimeLogMertens.coefficient p := by
    apply sum_congr rfl
    intro p hp
    simp only [PrimeLogMertens.coefficient,(hP p hp).1,ite_true]
  rw [he]
  apply le_trans _ (PrimeLogMertens.natural_bounds X hX).2
  unfold PrimeLogMertens.weightedPrimes
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact mem_range.mpr (by have hh := (hP p hp).2; omega)
  · intro p hp hnot
    unfold PrimeLogMertens.coefficient
    split_ifs with hh
    · positivity [Real.log_natCast_nonneg p]
    · exact le_rfl

theorem reciprocal_square_budget (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, 1/(p : ℝ)^2) ≤ 1 := by
  have hh := ReciprocalSquareTail.finite_bound 2 (by norm_num) P
    (fun p hp ↦ by exact_mod_cast (hP p hp).two_le)
  norm_num at hh
  simpa only [one_div] using hh

theorem summed_damping_defect (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X) (σ : ℝ) (hσ : 0 ≤ σ) :
    (∑ p ∈ P, (1/(p : ℝ)-(p : ℝ)^(-σ)/(p : ℝ))) ≤
      σ*(Real.log (X : ℝ)+(Real.log 4+4)) := by
  calc
    _ ≤ ∑ p ∈ P, σ*(Real.log (p : ℝ)/(p : ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).1.one_le
      have hh := div_le_div_of_nonneg_right (damping_defect p σ hp1 hσ).2 (Nat.cast_nonneg p)
      convert hh using 1 <;> ring
    _ = σ*(∑ p ∈ P, Real.log (p : ℝ)/(p : ℝ)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_log_sum_bound X hX P hP) hσ

theorem uniform_summed_defect (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hLog : σ*Real.log (X : ℝ) ≤ 1) :
    (∑ p ∈ P, (1/(p : ℝ)-(p : ℝ)^(-σ)/(p : ℝ))) ≤ Real.log 4+5 := by
  have hh := summed_damping_defect X hX P hP σ hσ0
  have hC : 0 ≤ Real.log (4 : ℝ)+4 := by positivity
  have hTerm := mul_le_mul_of_nonneg_right hσ1 hC
  nlinarith only [hh,hLog,hTerm]
end PaperP1.PrimeDampingBudget
