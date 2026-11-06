module

public import PaperP1.Analysis.PositiveSelbergSeries
public import PaperP1.Analysis.DirichletGramLargeValues


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PositiveSelbergGram
open Finset Filter PaperP1
open scoped Classical

def polynomial {ι : Type*} (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) (x : ℝ) : ℂ :=
  ∑ i ∈ S, a i*LogarithmicExponentialSum.function (τ i) x

def term {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) (n : ℕ) : ℝ :=
  PositiveSelbergSeries.weight Z (n+1)*LognormalSieveWeight.weight A ((n+1 : ℕ) : ℝ)*
    ‖polynomial S a τ ((n+1 : ℕ) : ℝ)‖^2

def energy {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) : ℝ :=
  ∑' n : ℕ, term A Z S a τ n

theorem norm_square_expansion {ι : Type*} (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) (x : ℝ) :
    ((‖polynomial S a τ x‖^2 : ℝ) : ℂ)=
      ∑ i ∈ S, ∑ j ∈ S, a i*star (a j)*LogarithmicExponentialSum.function (τ i-τ j) x := by
  rw [Complex.ofReal_pow,← Complex.mul_conj']
  unfold polynomial
  rw [map_sum,sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [map_mul]
  change a i*LogarithmicExponentialSum.function (τ i) x*
    (star (a j)*star (LogarithmicExponentialSum.function (τ j) x))=_
  have hPhase : LogarithmicExponentialSum.function (τ i) x*star (LogarithmicExponentialSum.function (τ j) x)=
      LogarithmicExponentialSum.function (τ i-τ j) x :=
    DirichletGramLargeValues.phase_time_difference (-Real.log x) (τ i) (τ j)
  calc
    _ = (a i*star (a j))*(LogarithmicExponentialSum.function (τ i) x*star (LogarithmicExponentialSum.function (τ j) x)) := by ring
    _ = _ := by rw [hPhase]

theorem term_nonneg {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) (n : ℕ) :
    0 ≤ term A Z S a τ n :=
  mul_nonneg (mul_nonneg (PositiveSelbergSeries.weight_nonneg Z (n+1)) (LognormalSieveWeight.weight_pos A _).le) (sq_nonneg _)

theorem term_identity {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) (n : ℕ) :
    (term A Z S a τ n : ℂ)=
      ∑ i ∈ S, ∑ j ∈ S, (a i*star (a j))*
        ((PositiveSelbergSeries.weight Z (n+1) : ℂ)*LognormalPhaseVariation.function A (τ i-τ j) ((n+1 : ℕ) : ℝ)) := by
  rw [term,Complex.ofReal_mul,Complex.ofReal_mul,norm_square_expansion,mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  unfold LognormalPhaseVariation.function
  ring

theorem complex_hasSum {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) (hA : 0 < A) :
    HasSum (fun n : ℕ ↦ (term A Z S a τ n : ℂ))
      (∑ i ∈ S, ∑ j ∈ S, (a i*star (a j))*LognormalSelbergKernel.value A (τ i-τ j) Z) := by
  have hRows : ∀ i ∈ S,
      HasSum (fun n : ℕ ↦ ∑ j ∈ S, (a i*star (a j))*
        ((PositiveSelbergSeries.weight Z (n+1) : ℂ)*LognormalPhaseVariation.function A (τ i-τ j) ((n+1 : ℕ) : ℝ)))
        (∑ j ∈ S, (a i*star (a j))*LognormalSelbergKernel.value A (τ i-τ j) Z) := by
    intro i hi
    exact hasSum_sum (fun j hj ↦ (PositiveSelbergSeries.weighted_hasSum A (τ i-τ j) Z hA).mul_left (a i*star (a j)))
  exact (hasSum_sum hRows).congr_fun (fun n ↦ term_identity A Z S a τ n)

theorem real_hasSum {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) (hA : 0 < A) :
    HasSum (term A Z S a τ)
      (∑ i ∈ S, ∑ j ∈ S, (a i*star (a j))*LognormalSelbergKernel.value A (τ i-τ j) Z).re := by
  simpa only [Complex.ofReal_re] using Complex.hasSum_re (complex_hasSum A Z S a τ hA)

theorem summable_terms {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) (hA : 0 < A) :
    Summable (term A Z S a τ) := (real_hasSum A Z S a τ hA).summable

theorem gram_identity {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) (hA : 0 < A) :
    (energy A Z S a τ : ℂ)=
      ∑ i ∈ S, ∑ j ∈ S, (a i*star (a j))*LognormalSelbergKernel.value A (τ i-τ j) Z :=
  (Complex.hasSum_ofReal.mpr (summable_terms A Z S a τ hA).hasSum).unique (complex_hasSum A Z S a τ hA)

theorem energy_nonneg {ι : Type*} (A : ℝ) (Z : ℕ) (S : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) :
    0 ≤ energy A Z S a τ := tsum_nonneg (fun n ↦ term_nonneg A Z S a τ n)
end PaperP1.PositiveSelbergGram
