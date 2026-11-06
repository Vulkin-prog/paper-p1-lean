module

public import PaperP1.Analysis.DirichletRamareApproximation
public import PaperP1.Analysis.PrimePresence
public import PaperP1.Analysis.RelativePrimeRamare

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RelativeRamareRemainder
open Finset PaperP1
open scoped Classical

def residual (P Q : Finset ℕ) (n : ℕ) : ℝ :=
  1-RamareWeights.weight P n*PrimePresence.present Q n

def coefficient (P Q : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ := (residual P Q n : ℂ)*f n

def quotient (N : ℕ) (P Q : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ P, ∑ m ∈ Icc 1 (2*N/p), if p*m ∈ Ico N (2*N) then
    DirichletRamareApproximation.twist f p t*((PrimePresence.present Q m : ℂ)*DirichletRamareApproximation.twist f m t)/
      ((PrimeDivisorWeights.count P m+1 : ℕ) : ℂ) else 0

theorem residual_bounds (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    0 ≤ residual P Q n ∧ residual P Q n ≤ 1 := by
  have hw := RamareWeights.weight_nonneg P n
  have hw1 := RamareWeights.weight_le_one P hP n
  obtain ⟨hq,hq1⟩ := PrimePresence.present_bounds Q n
  have hp := mul_nonneg hw hq
  have hp1 := mul_le_mul hw1 hq1 hq (by norm_num : (0 : ℝ) ≤ 1)
  unfold residual
  constructor <;> nlinarith

theorem coefficient_norm_bound (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℂ) (n : ℕ) (hf : ‖f n‖ ≤ 1) : ‖coefficient P Q f n‖ ≤ 1 := by
  rw [coefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (residual_bounds P Q hP n).1]
  exact (mul_le_mul (residual_bounds P Q hP n).2 hf (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem residual_eq_zero (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ)
    (hcP : 0 < PrimeDivisorWeights.count P n) (hcQ : 0 < PrimeDivisorWeights.count Q n)
    (hsq : ∀ p ∈ P, ¬p^2 ∣ n) : residual P Q n=0 := by
  rw [residual,RamareWeights.weight_eq_one P hP n hcP hsq,PrimePresence.present,ite_eq_left hcQ]
  norm_num

theorem value_relation (S P Q : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) :
    DirichletPolynomialMeanValue.value S (coefficient P Q f) t=
      DirichletPolynomialMeanValue.value S f t-
      DirichletPolynomialMeanValue.value S (fun n ↦ (PrimePresence.present Q n : ℂ)*f n) t+
      DirichletPolynomialMeanValue.value S (fun n ↦
        ((1-RamareWeights.weight P n : ℝ) : ℂ)*(PrimePresence.present Q n : ℂ)*f n) t := by
  unfold DirichletPolynomialMeanValue.value GaussianExponentialSums.polynomial coefficient residual
  rw [← sum_sub_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  dsimp only
  push_cast
  ring

theorem difference_identity (N : ℕ) (hN : 0 < N) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
    (f : ℕ → ℂ) (hf : ∀ a b, f (a*b)=f a*f b) (t : ℝ) :
    DirichletPolynomialMeanValue.value (Ico N (2*N)) f t-quotient N P Q f t=
      DirichletPolynomialMeanValue.value (Ico N (2*N)) (coefficient P Q f) t := by
  have hi := RelativePrimeRamare.twisted_presence_identity (Ico N (2*N)) P Q (2*N) hP hQ hPQ
    (fun n hn ↦ ⟨hN.trans_le (mem_Ico.mp hn).1,(mem_Ico.mp hn).2.le⟩) f hf t
  change DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun n ↦ (PrimePresence.present Q n : ℂ)*f n) t=
    quotient N P Q f t+DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun n ↦
      ((1-RamareWeights.weight P n : ℝ) : ℂ)*(PrimePresence.present Q n : ℂ)*f n) t at hi
  have hr := value_relation (Ico N (2*N)) P Q f t
  rw [hi] at hr
  calc
    _ = DirichletPolynomialMeanValue.value (Ico N (2*N)) f t-
        (quotient N P Q f t+DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun n ↦
          ((1-RamareWeights.weight P n : ℝ) : ℂ)*(PrimePresence.present Q n : ℂ)*f n) t)+
        DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun n ↦
          ((1-RamareWeights.weight P n : ℝ) : ℂ)*(PrimePresence.present Q n : ℂ)*f n) t := by abel
    _ = _ := hr.symm

theorem quotient_continuous (N : ℕ) (P Q : Finset ℕ) (f : ℕ → ℂ) : Continuous (quotient N P Q f) := by
  apply continuous_finsetSum
  intro p hp
  apply continuous_finsetSum
  intro m hm
  by_cases hmem : p*m ∈ Ico N (2*N)
  · simp only [ite_eq_left hmem]
    exact ((DirichletRamareApproximation.twist_continuous f p).mul
      (continuous_const.mul (DirichletRamareApproximation.twist_continuous f m))).div_const _
  · simpa only [ite_eq_right hmem] using (continuous_const : Continuous (fun _t : ℝ ↦ (0 : ℂ)))
end PaperP1.RelativeRamareRemainder
