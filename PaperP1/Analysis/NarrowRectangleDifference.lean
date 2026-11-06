module

public import PaperP1.Analysis.RelativePrimeRamare
public import PaperP1.Analysis.NarrowRamareRectangle
public import PaperP1.Analysis.NarrowRectangleValue
public import PaperP1.Analysis.NarrowRectangleWeight

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NarrowRectangleDifference
open Finset PaperP1 PrimeDivisorWeights
open scoped Classical

def sourceWeight (X : ℕ) (P : Finset ℕ) (n : ℕ) : ℝ :=
  if n ∈ Ico X (2*X) then RamareWeights.weight P n else 0

def coefficient (X H : ℕ) (P Q : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((NarrowRectangleWeight.weight X H P n-sourceWeight X P n : ℝ) : ℂ)*
    (PrimePresence.present Q n : ℂ)*f n

theorem sourceWeight_bounds (X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    0 ≤ sourceWeight X P n ∧ sourceWeight X P n ≤ 1 := by
  unfold sourceWeight
  split_ifs
  · exact ⟨RamareWeights.weight_nonneg P n,RamareWeights.weight_le_one P hP n⟩
  · norm_num

theorem coefficient_norm_bound (X H : ℕ) (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℂ) (n : ℕ) (hf : ‖f n‖ ≤ 1) : ‖coefficient X H P Q f n‖ ≤ 1 := by
  have hW := NarrowRectangleWeight.weight_nonneg X H P n
  have hW1 := NarrowRectangleWeight.weight_le_one X H P hP n
  obtain ⟨hS,hS1⟩ := sourceWeight_bounds X P hP n
  have hd : |NarrowRectangleWeight.weight X H P n-sourceWeight X P n| ≤ 1 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  obtain ⟨hq,hq1⟩ := PrimePresence.present_bounds Q n
  rw [coefficient,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq]
  calc
    _ ≤ 1*1*1 := mul_le_mul (mul_le_mul hd hq1 hq (by norm_num)) hf (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem coefficient_zero (X H : ℕ) (hX : 0 < X) (hH : 2 ≤ H)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℂ) (n : ℕ)
    (hn : n ∈ Ico X (4*X)) (hnot : n ∉ NarrowRectangleWeight.boundary X H) :
    coefficient X H P Q f n=0 := by
  have hh := NarrowRectangleWeight.weight_outside_boundary X H hX hH P hP n hn hnot
  unfold coefficient sourceWeight
  rw [hh,sub_self]
  simp

theorem source_value_identity (X : ℕ) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
    (f : ℕ → ℂ) (hf : ∀ a b, f (a*b)=f a*f b) (t : ℝ) :
    RelativeRamareRemainder.quotient X P Q f t=
      DirichletPolynomialMeanValue.value (Ico X (4*X))
        (fun n ↦ (sourceWeight X P n : ℂ)*(PrimePresence.present Q n : ℂ)*f n) t := by
  let b := RelativePrimeRamare.presenceCoefficient Q (fun n ↦ DirichletRamareApproximation.twist f n t)
  have hi := RelativePrimeRamare.weighted_ramare_sum (Ico X (2*X)) P (2*X) hP
    (by intro n hn; have hh := mem_Ico.mp hn; omega)
    (fun n ↦ DirichletRamareApproximation.twist f n t) b
    (RelativePrimeRamare.presence_relative P Q hP hQ hPQ (fun n ↦ DirichletRamareApproximation.twist f n t)
      (DirichletRamareApproximation.twist_mul f hf t))
  have hs : (Ico X (4*X)).filter (fun n ↦ n ∈ Ico X (2*X))=Ico X (2*X) := by
    ext n
    simp only [mem_filter,mem_Ico]
    omega
  rw [RelativePrimeRamare.value_weighted_sum]
  calc
    _ = ∑ n ∈ Ico X (2*X), (RamareWeights.weight P n : ℂ)*b n := hi.symm
    _ = ∑ n ∈ Ico X (4*X), (sourceWeight X P n : ℂ)*b n := by
      rw [← hs,sum_filter]
      apply sum_congr rfl
      intro n hn
      by_cases hi : n ∈ Ico X (2*X)
      · simp only [sourceWeight,hi,ite_true]
      · simp only [sourceWeight,hi,ite_false,Complex.ofReal_zero,zero_mul]
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      dsimp only [b,RelativePrimeRamare.presenceCoefficient]
      ring

theorem difference_identity (X H : ℕ) (hX : 0 < X) (hH : 2 ≤ H)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hPQ : Disjoint P Q) (f : ℕ → ℂ) (hf : ∀ a b, f (a*b)=f a*f b) (t : ℝ) :
    NarrowRamareRectangle.rectangle X H P Q f t-RelativeRamareRemainder.quotient X P Q f t=
      DirichletPolynomialMeanValue.value (Ico X (4*X)) (coefficient X H P Q f) t := by
  rw [NarrowRectangleValue.rectangle_value_identity X H hX hH P Q hP hQ hPQ f hf,
    source_value_identity X P Q hP hQ hPQ f hf]
  unfold DirichletPolynomialMeanValue.value GaussianExponentialSums.polynomial
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  unfold coefficient NarrowRectangleValue.coefficient
  push_cast
  ring
end PaperP1.NarrowRectangleDifference
