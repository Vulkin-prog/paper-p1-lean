module

public import PaperP1.Analysis.GaussianExponentialSums
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Exact finite Gram duality and correlation-sensitive large-value bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteGramLargeValues
open Finset PaperP1
open scoped Classical

def gram {α β : Type*} (S : Finset α) (ψ : β → α → ℂ) (r s : β) : ℂ :=
  ∑ n ∈ S, ψ r n*star (ψ s n)

def evaluate {α β : Type*} (S : Finset α) (a : α → ℂ) (ψ : β → α → ℂ) (r : β) : ℂ :=
  ∑ n ∈ S, a n*ψ r n

theorem complex_cauchy_square {α : Type*} (S : Finset α) (a b : α → ℂ) :
    ‖∑ n ∈ S, a n*b n‖^2 ≤ (∑ n ∈ S, ‖a n‖^2)*(∑ n ∈ S, ‖b n‖^2) := by
  have ht : ‖∑ n ∈ S, a n*b n‖ ≤ ∑ n ∈ S, ‖a n‖*‖b n‖ := by
    simpa only [norm_mul] using norm_sum_le S (fun n ↦ a n*b n)
  have hp := pow_le_pow_left₀ (norm_nonneg _) ht 2
  exact hp.trans (sum_mul_sq_le_sq_mul_sq S (fun n ↦ ‖a n‖) (fun n ↦ ‖b n‖))

theorem gram_star {α β : Type*} (S : Finset α) (ψ : β → α → ℂ) (r s : β) :
    star (gram S ψ r s)=gram S ψ s r := by
  simp only [gram,star_sum,star_mul,star_star]

theorem gram_norm_symm {α β : Type*} (S : Finset α) (ψ : β → α → ℂ) (r s : β) :
    ‖gram S ψ r s‖=‖gram S ψ s r‖ := by
  rw [← gram_star S ψ r s,norm_star]

theorem square_expansion {α β : Type*} (S : Finset α) (R : Finset β)
    (b : β → ℂ) (ψ : β → α → ℂ) :
    ((∑ n ∈ S, ‖∑ r ∈ R, b r*ψ r n‖^2 : ℝ) : ℂ) =
      ∑ r ∈ R, ∑ s ∈ R, b r*star (b s)*gram S ψ r s := by
  have hp (n : α) : ((‖∑ r ∈ R, b r*ψ r n‖^2 : ℝ) : ℂ) =
      ∑ r ∈ R, ∑ s ∈ R, (b r*star (b s))*(ψ r n*star (ψ s n)) := by
    rw [Complex.ofReal_pow,← Complex.mul_conj']
    rw [map_sum,sum_mul]
    apply sum_congr rfl
    intro r hr
    rw [mul_sum]
    apply sum_congr rfl
    intro s hs
    rw [map_mul]
    change b r*ψ r n*(star (b s)*star (ψ s n))=_
    ring
  rw [Complex.ofReal_sum]
  simp_rw [hp]
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  rw [gram,mul_sum]

theorem synthesis_bound {α β : Type*} (S : Finset α) (R : Finset β)
    (b : β → ℂ) (ψ : β → α → ℂ) (L : ℝ)
    (hrow : ∀ r ∈ R, (∑ s ∈ R, ‖gram S ψ r s‖) ≤ L) :
    (∑ n ∈ S, ‖∑ r ∈ R, b r*ψ r n‖^2) ≤ L*(∑ r ∈ R, ‖b r‖^2) := by
  have he := square_expansion S R b ψ
  have hn := congrArg norm he
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sum_nonneg (fun n hn ↦ sq_nonneg _))] at hn
  rw [hn]
  have hnorm : ‖∑ r ∈ R, ∑ s ∈ R, b r*star (b s)*gram S ψ r s‖ ≤
      ∑ r ∈ R, ∑ s ∈ R, ‖gram S ψ r s‖*‖b r‖*‖b s‖ := by
    calc
      _ ≤ ∑ r ∈ R, ‖∑ s ∈ R, b r*star (b s)*gram S ψ r s‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply sum_le_sum
        intro r hr
        calc
          _ ≤ ∑ s ∈ R, ‖b r*star (b s)*gram S ψ r s‖ := norm_sum_le _ _
          _ = _ := by
            apply sum_congr rfl
            intro s hs
            simp only [norm_mul,norm_star]
            ring
  exact hnorm.trans (FiniteSymmetricKernelBudget.symmetric_bound R (fun r ↦ ‖b r‖)
    (fun r s ↦ ‖gram S ψ r s‖) L (fun r hr s hs ↦ norm_nonneg _)
    (fun r hr s hs ↦ gram_norm_symm S ψ r s) hrow)

theorem dual_identity {α β : Type*} (S : Finset α) (R : Finset β)
    (a : α → ℂ) (ψ : β → α → ℂ) :
    ((∑ r ∈ R, ‖evaluate S a ψ r‖^2 : ℝ) : ℂ) =
      ∑ n ∈ S, a n*(∑ r ∈ R, star (evaluate S a ψ r)*ψ r n) := by
  rw [Complex.ofReal_sum]
  have he (r : β) : ((‖evaluate S a ψ r‖^2 : ℝ) : ℂ) =
      ∑ n ∈ S, a n*ψ r n*star (evaluate S a ψ r) := by
    rw [Complex.ofReal_pow,← Complex.mul_conj']
    change (∑ n ∈ S, a n*ψ r n)*star (evaluate S a ψ r)=_
    rw [sum_mul]
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [mul_sum]
  apply sum_congr rfl
  intro r hr
  ring

theorem analysis_bound {α β : Type*} (S : Finset α) (R : Finset β)
    (a : α → ℂ) (ψ : β → α → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ r ∈ R, (∑ s ∈ R, ‖gram S ψ r s‖) ≤ L) :
    (∑ r ∈ R, ‖evaluate S a ψ r‖^2) ≤ L*(∑ n ∈ S, ‖a n‖^2) := by
  let A : ℝ := ∑ n ∈ S, ‖a n‖^2
  let H : ℝ := ∑ r ∈ R, ‖evaluate S a ψ r‖^2
  let b : α → ℂ := fun n ↦ ∑ r ∈ R, star (evaluate S a ψ r)*ψ r n
  have hH : 0 ≤ H := sum_nonneg (fun r hr ↦ sq_nonneg _)
  have hA : 0 ≤ A := sum_nonneg (fun n hn ↦ sq_nonneg _)
  have he := dual_identity S R a ψ
  have hn := congrArg norm he
  change ‖(H : ℂ)‖=‖∑ n ∈ S, a n*b n‖ at hn
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hH] at hn
  have hc := complex_cauchy_square S a b
  rw [← hn] at hc
  have hs := synthesis_bound S R (fun r ↦ star (evaluate S a ψ r)) ψ L hrow
  simp only [norm_star] at hs
  change (∑ n ∈ S, ‖b n‖^2) ≤ L*H at hs
  have hb := hc.trans (mul_le_mul_of_nonneg_left hs hA)
  change H^2 ≤ A*(L*H) at hb
  change H ≤ L*A
  by_cases hz : H=0
  · rw [hz]
    exact mul_nonneg hL hA
  · have hHp : 0 < H := lt_of_le_of_ne hH (Ne.symm hz)
    nlinarith

theorem large_values_card {α β : Type*} (S : Finset α) (R : Finset β)
    (a : α → ℂ) (ψ : β → α → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ r ∈ R, (∑ s ∈ R, ‖gram S ψ r s‖) ≤ L)
    (V : ℝ) (hV : 0 < V) (hbig : ∀ r ∈ R, V ≤ ‖evaluate S a ψ r‖) :
    (R.card : ℝ) ≤ L*(∑ n ∈ S, ‖a n‖^2)/V^2 := by
  have hl := sum_le_sum (s := R) (fun r hr ↦ pow_le_pow_left₀ hV.le (hbig r hr) 2)
  simp only [sum_const,nsmul_eq_mul] at hl
  exact (le_div_iff₀ (sq_pos_of_pos hV)).mpr (hl.trans (analysis_bound S R a ψ L hL hrow))

theorem montgomery_analysis_bound {α β : Type*} (S : Finset α) (R : Finset β)
    (a : α → ℂ) (ψ : β → α → ℂ) (D M : ℝ) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hdiag : ∀ r ∈ R, ‖gram S ψ r r‖ ≤ D)
    (hoff : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ‖gram S ψ r s‖ ≤ M) :
    (∑ r ∈ R, ‖evaluate S a ψ r‖^2) ≤
      (D+(R.card : ℝ)*M)*(∑ n ∈ S, ‖a n‖^2) := by
  apply analysis_bound S R a ψ (D+(R.card : ℝ)*M) (by positivity)
  intro r hr
  have hh := sum_le_sum (s := R) (fun s hs ↦ show ‖gram S ψ r s‖ ≤ (if r=s then D else 0)+M from by
    by_cases he : r=s
    · subst s
      simpa only [ite_true] using (hdiag r hr).trans (le_add_of_nonneg_right hM)
    · simpa only [he,ite_false,zero_add] using hoff r hr s hs he)
  simpa [sum_add_distrib,hr] using hh

theorem montgomery_large_values_card {α β : Type*} (S : Finset α) (R : Finset β)
    (a : α → ℂ) (ψ : β → α → ℂ) (D M : ℝ) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hdiag : ∀ r ∈ R, ‖gram S ψ r r‖ ≤ D)
    (hoff : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ‖gram S ψ r s‖ ≤ M)
    (V : ℝ) (hV : 0 < V) (hbig : ∀ r ∈ R, V ≤ ‖evaluate S a ψ r‖)
    (hden : 0 < V^2-M*(∑ n ∈ S, ‖a n‖^2)) :
    (R.card : ℝ) ≤ D*(∑ n ∈ S, ‖a n‖^2)/(V^2-M*(∑ n ∈ S, ‖a n‖^2)) := by
  have hl := sum_le_sum (s := R) (fun r hr ↦ pow_le_pow_left₀ hV.le (hbig r hr) 2)
  simp only [sum_const,nsmul_eq_mul] at hl
  have hb := hl.trans (montgomery_analysis_bound S R a ψ D M hD hM hdiag hoff)
  apply (le_div_iff₀ hden).mpr
  nlinarith
end FiniteGramLargeValues
