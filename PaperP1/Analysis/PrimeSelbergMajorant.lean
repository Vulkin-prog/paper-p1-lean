module

public import PaperP1.Analysis.LognormalSieveWeight
public import PaperP1.Analysis.PositiveSelbergGram


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimeSelbergMajorant
open Finset Filter PaperP1
open scoped Classical

theorem positive_index_injective (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) :
    Set.InjOn (fun p : ℕ ↦ p-1) (↑P) := by
  intro p hp q hq he
  have hpp := hP p hp
  have hqp := hP q hq
  change p-1=q-1 at he
  omega

theorem finite_energy_bound {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ)
    (hA : 0 < A) (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) :
    (∑ p ∈ P, PositiveSelbergGram.term A Z S a τ (p-1)) ≤ PositiveSelbergGram.energy A Z S a τ := by
  have hh := (PositiveSelbergGram.summable_terms A Z S a τ hA).sum_le_tsum
    (P.image (fun p ↦ p-1)) (fun n _ ↦ PositiveSelbergGram.term_nonneg A Z S a τ n)
  rw [sum_image (positive_index_injective P hP)] at hh
  exact hh

theorem pointwise_prime_bound {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ)
    (hA : 0 < A) (hZ : 1 ≤ Z) (p : ℕ) (hp : p.Prime) (hZp : Z < p)
    (hLower : A ≤ p) (hUpper : (p : ℝ) ≤ 2*A) :
    ‖PositiveSelbergGram.polynomial S a τ p‖^2 ≤
      Real.exp 2*PositiveSelbergGram.term A Z S a τ (p-1) := by
  rw [PositiveSelbergGram.term,show p-1+1=p by have hh := hp.pos; omega,
    PositiveSelbergSeries.weight_prime Z p hZ hp hZp,one_mul]
  have hh := LognormalSieveWeight.majorant_on_dyadic A p hA hLower hUpper
  calc
    _ ≤ (Real.exp 2*LognormalSieveWeight.weight A p)*‖PositiveSelbergGram.polynomial S a τ p‖^2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (sq_nonneg ‖PositiveSelbergGram.polynomial S a τ p‖)
    _ = _ := by ring

theorem prime_synthesis_bound {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ)
    (hA : 0 < A) (hZ : 1 ≤ Z) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Z < p ∧ A ≤ p ∧ (p : ℝ) ≤ 2*A) :
    (∑ p ∈ P, ‖PositiveSelbergGram.polynomial S a τ p‖^2) ≤
      Real.exp 2*PositiveSelbergGram.energy A Z S a τ := by
  calc
    _ ≤ ∑ p ∈ P, Real.exp 2*PositiveSelbergGram.term A Z S a τ (p-1) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpp,hZp,hLower,hUpper⟩ := hP p hp
      exact pointwise_prime_bound A Z S a τ hA hZ p hpp hZp hLower hUpper
    _ = Real.exp 2*(∑ p ∈ P, PositiveSelbergGram.term A Z S a τ (p-1)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_energy_bound A Z S a τ hA P (fun p hp ↦ (hP p hp).1.pos)) (Real.exp_pos 2).le

theorem analysis_of_synthesis {α β : Type*} (S : Finset α) (R : Finset β) (a : α → ℂ)
    (ψ : β → α → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hSynthesis : ∀ b : β → ℂ, (∑ n ∈ S, ‖∑ r ∈ R, b r*ψ r n‖^2) ≤ L*(∑ r ∈ R, ‖b r‖^2)) :
    (∑ r ∈ R, ‖FiniteGramLargeValues.evaluate S a ψ r‖^2) ≤ L*(∑ n ∈ S, ‖a n‖^2) := by
  let A : ℝ := ∑ n ∈ S, ‖a n‖^2
  let H : ℝ := ∑ r ∈ R, ‖FiniteGramLargeValues.evaluate S a ψ r‖^2
  let b : α → ℂ := fun n ↦ ∑ r ∈ R, star (FiniteGramLargeValues.evaluate S a ψ r)*ψ r n
  have hH : 0 ≤ H := sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hAN : 0 ≤ A := sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hn := congrArg norm (FiniteGramLargeValues.dual_identity S R a ψ)
  change ‖(H : ℂ)‖=‖∑ n ∈ S, a n*b n‖ at hn
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hH] at hn
  have hc := FiniteGramLargeValues.complex_cauchy_square S a b
  rw [← hn] at hc
  have hs := hSynthesis (fun r ↦ star (FiniteGramLargeValues.evaluate S a ψ r))
  simp only [norm_star] at hs
  change (∑ n ∈ S, ‖b n‖^2) ≤ L*H at hs
  have hb := hc.trans (mul_le_mul_of_nonneg_left hs hAN)
  change H^2 ≤ A*(L*H) at hb
  change H ≤ L*A
  by_cases hz : H=0
  · rw [hz]
    exact mul_nonneg hL hAN
  · have hHp : 0 < H := lt_of_le_of_ne hH (Ne.symm hz)
    nlinarith
end PaperP1.PrimeSelbergMajorant
