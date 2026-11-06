module

public import PaperP1.Arithmetic.RamareWeights
public import PaperP1.Analysis.DirichletRamareApproximation
public import PaperP1.Analysis.PrimePresence

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RelativePrimeRamare
open Finset PaperP1 PrimeDivisorWeights
open scoped Classical

theorem weighted_identity (P : Finset ℕ) (n : ℕ) (a b : ℕ → ℂ)
    (hb : ∀ p ∈ P, ∀ m : ℕ, b (p*m)=a p*b m) :
    (∑ p ∈ factors P n, a p*b (n/p)/((count P (n/p)+1 : ℕ) : ℂ))=
      (RamareWeights.weight P n : ℂ)*b n := by
  rw [RamareWeights.weight,Complex.ofReal_sum,sum_mul]
  apply sum_congr rfl
  intro p hp
  rw [← hb p (mem_filter.mp hp).1 (n/p),Nat.mul_div_cancel' (mem_filter.mp hp).2]
  push_cast
  ring

theorem weighted_ramare_sum (S P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ X) (a b : ℕ → ℂ)
    (hb : ∀ p ∈ P, ∀ m : ℕ, b (p*m)=a p*b m) :
    (∑ n ∈ S, (RamareWeights.weight P n : ℂ)*b n)=
      ∑ p ∈ P, ∑ m ∈ Icc 1 (X/p), if p*m ∈ S then a p*b m/((count P m+1 : ℕ) : ℂ) else 0 := by
  calc
    _ = ∑ n ∈ S, ∑ p ∈ factors P n, a p*b (n/p)/((count P (n/p)+1 : ℕ) : ℂ) := by
      apply sum_congr rfl
      intro n hn
      exact (weighted_identity P n a b hb).symm
    _ = ∑ p ∈ P, ∑ n ∈ S.filter (p ∣ ·), a p*b (n/p)/((count P (n/p)+1 : ℕ) : ℂ) := by
      simp only [factors,sum_filter]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      rw [sum_multiples S X p (hP p hp).pos hS]
      apply sum_congr rfl
      intro m hm
      rw [Nat.mul_div_cancel_left m (hP p hp).pos]

theorem full_ramare_with_remainder (S P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ X) (a b : ℕ → ℂ)
    (hb : ∀ p ∈ P, ∀ m : ℕ, b (p*m)=a p*b m) :
    (∑ n ∈ S, b n)=
      (∑ p ∈ P, ∑ m ∈ Icc 1 (X/p), if p*m ∈ S then a p*b m/((count P m+1 : ℕ) : ℂ) else 0)+
      ∑ n ∈ S, ((1-RamareWeights.weight P n : ℝ) : ℂ)*b n := by
  rw [← weighted_ramare_sum S P X hP hS a b hb,← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  push_cast
  ring

def presenceCoefficient (Q : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  (PrimePresence.present Q n : ℂ)*f n

theorem presence_relative (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hPQ : Disjoint P Q) (f : ℕ → ℂ) (hf : ∀ a b, f (a*b)=f a*f b) :
    ∀ p ∈ P, ∀ m : ℕ, presenceCoefficient Q f (p*m)=f p*presenceCoefficient Q f m := by
  intro p hp m
  have hpQ : p ∉ Q := fun hh ↦ Finset.disjoint_left.mp hPQ hp hh
  rw [presenceCoefficient,PrimePresence.present_mul_outside Q hQ p (hP p hp) hpQ m,hf,presenceCoefficient]
  ring

theorem full_presence_ramare (S P Q : Finset ℕ) (X : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ X) (f : ℕ → ℂ) (hf : ∀ a b, f (a*b)=f a*f b) :
    (∑ n ∈ S, presenceCoefficient Q f n)=
      (∑ p ∈ P, ∑ m ∈ Icc 1 (X/p), if p*m ∈ S then f p*presenceCoefficient Q f m/((count P m+1 : ℕ) : ℂ) else 0)+
      ∑ n ∈ S, ((1-RamareWeights.weight P n : ℝ) : ℂ)*presenceCoefficient Q f n :=
  full_ramare_with_remainder S P X hP hS f (presenceCoefficient Q f) (presence_relative P Q hP hQ hPQ f hf)

theorem value_weighted_sum (S : Finset ℕ) (w f : ℕ → ℂ) (t : ℝ) :
    DirichletPolynomialMeanValue.value S (fun n ↦ w n*f n) t=
      ∑ n ∈ S, w n*DirichletRamareApproximation.twist f n t := by
  unfold DirichletPolynomialMeanValue.value GaussianExponentialSums.polynomial DirichletRamareApproximation.twist
  apply sum_congr rfl
  intro n hn
  ring

theorem twisted_presence_identity (S P Q : Finset ℕ) (X : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ X) (f : ℕ → ℂ) (hf : ∀ a b, f (a*b)=f a*f b) (t : ℝ) :
    DirichletPolynomialMeanValue.value S (fun n ↦ (PrimePresence.present Q n : ℂ)*f n) t=
      (∑ p ∈ P, ∑ m ∈ Icc 1 (X/p), if p*m ∈ S then
        DirichletRamareApproximation.twist f p t*((PrimePresence.present Q m : ℂ)*DirichletRamareApproximation.twist f m t)/
          ((count P m+1 : ℕ) : ℂ) else 0)+
      DirichletPolynomialMeanValue.value S (fun n ↦
        ((1-RamareWeights.weight P n : ℝ) : ℂ)*(PrimePresence.present Q n : ℂ)*f n) t := by
  rw [value_weighted_sum S (fun n ↦ (PrimePresence.present Q n : ℂ)) f t,
    value_weighted_sum S (fun n ↦ ((1-RamareWeights.weight P n : ℝ) : ℂ)*(PrimePresence.present Q n : ℂ)) f t]
  have hh := full_presence_ramare S P Q X hP hQ hPQ hS (fun n ↦ DirichletRamareApproximation.twist f n t)
    (DirichletRamareApproximation.twist_mul f hf t)
  simpa only [presenceCoefficient,mul_assoc] using hh
end PaperP1.RelativePrimeRamare
