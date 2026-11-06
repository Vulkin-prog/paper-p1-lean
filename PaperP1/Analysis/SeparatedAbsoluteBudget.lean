module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import PaperP1.Analysis.SeparatedPositiveBudget

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SeparatedAbsoluteBudget
open Finset
open scoped Classical

theorem absolute_budgets {ι : Type*} (S : Finset ι) (τ : ι → ℝ) (c A : ℝ) (hA : 1 ≤ A)
    (hδ : ∀ i ∈ S, 1 ≤ |τ i-c| ∧ |τ i-c| ≤ A)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |τ i-τ j|) :
    (S.card : ℝ) ≤ 2*A ∧ (∑ i ∈ S, 1/|τ i-c|) ≤ 2*(1+Real.log A) := by
  let P := S.filter (fun i ↦ c ≤ τ i)
  let M := S.filter (fun i ↦ ¬c ≤ τ i)
  have hpδ : ∀ i ∈ P, 1 ≤ τ i-c ∧ τ i-c ≤ A := by
    intro i hi
    have hs := hδ i (mem_filter.mp hi).1
    rw [abs_of_nonneg (sub_nonneg.mpr (mem_filter.mp hi).2)] at hs
    exact hs
  have hmδ : ∀ i ∈ M, 1 ≤ c-τ i ∧ c-τ i ≤ A := by
    intro i hi
    have hs := hδ i (mem_filter.mp hi).1
    have he : |τ i-c|=c-τ i := by
      rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge (mem_filter.mp hi).2))]
      ring
    rwa [he] at hs
  have hpsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → 1 ≤ |(τ i-c)-(τ j-c)| := by
    intro i hi j hj hne
    have hs := hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hne
    convert hs using 1
    congr 1
    ring
  have hmsep : ∀ i ∈ M, ∀ j ∈ M, i ≠ j → 1 ≤ |(c-τ i)-(c-τ j)| := by
    intro i hi j hj hne
    rw [show (c-τ i)-(c-τ j)=τ j-τ i by ring,abs_sub_comm]
    exact hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hne
  have hpC := SeparatedPositiveBudget.card_bound P (fun i ↦ τ i-c) A hA hpδ hpsep
  have hmC := SeparatedPositiveBudget.card_bound M (fun i ↦ c-τ i) A hA hmδ hmsep
  have hpR := SeparatedPositiveBudget.reciprocal_bound P (fun i ↦ τ i-c) A hA hpδ hpsep
  have hmR := SeparatedPositiveBudget.reciprocal_bound M (fun i ↦ c-τ i) A hA hmδ hmsep
  have hc : (P.card : ℝ)+(M.card : ℝ)=(S.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := S) (fun i ↦ c ≤ τ i))
  have heP : (∑ i ∈ P, 1/|τ i-c|)=∑ i ∈ P, 1/(τ i-c) := by
    apply sum_congr rfl
    intro i hi
    rw [abs_of_nonneg (sub_nonneg.mpr (mem_filter.mp hi).2)]
  have heM : (∑ i ∈ M, 1/|τ i-c|)=∑ i ∈ M, 1/(c-τ i) := by
    apply sum_congr rfl
    intro i hi
    rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge (mem_filter.mp hi).2))]
    congr 1
    ring
  have hsum : (∑ i ∈ P, 1/|τ i-c|)+(∑ i ∈ M, 1/|τ i-c|)=∑ i ∈ S, 1/|τ i-c| :=
    Finset.sum_filter_add_sum_filter_not S (fun i ↦ c ≤ τ i) (fun i ↦ 1/|τ i-c|)
  rw [heP,heM] at hsum
  constructor <;> linarith

theorem weighted_distance_bound {ι : Type*} (S : Finset ι) (τ : ι → ℝ) (c A : ℝ) (hA : 1 ≤ A)
    (hδ : ∀ i ∈ S, 1 ≤ |τ i-c| ∧ |τ i-c| ≤ A)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |τ i-τ j|)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∑ i ∈ S, (a/|τ i-c|+b*|τ i-c|)) ≤ 2*a*(1+Real.log A)+2*b*A^2 := by
  obtain ⟨hcard,hrec⟩ := absolute_budgets S τ c A hA hδ hsep
  have hApos : 0 ≤ A := by linarith
  have hsumdist : (∑ i ∈ S, |τ i-c|) ≤ 2*A^2 := by
    calc
      _ ≤ ∑ _i ∈ S, A := sum_le_sum (fun i hi ↦ (hδ i hi).2)
      _ = (S.card : ℝ)*A := by simp
      _ ≤ (2*A)*A := mul_le_mul_of_nonneg_right hcard hApos
      _ = _ := by ring
  have he : (∑ i ∈ S, (a/|τ i-c|+b*|τ i-c|))=
      a*(∑ i ∈ S, 1/|τ i-c|)+b*(∑ i ∈ S, |τ i-c|) := by
    rw [sum_add_distrib,mul_sum,mul_sum]
    congr 1
    apply sum_congr rfl
    intro i hi
    ring
  rw [he]
  have h1 := mul_le_mul_of_nonneg_left hrec ha
  have h2 := mul_le_mul_of_nonneg_left hsumdist hb
  nlinarith only [h1,h2]
end PaperP1.SeparatedAbsoluteBudget
