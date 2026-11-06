module

public import PaperP1.Analysis.LognormalSumIntegrability
public import PaperP1.Analysis.LognormalDilatedKernel
public import PaperP1.Analysis.LognormalSelbergKernel
public import PaperP1.Analysis.PrimeSelbergCoefficients


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PositiveSelbergSeries
open Finset Filter PaperP1
open scoped Classical

def weight (Z n : ℕ) : ℝ :=
  ∑ d ∈ PrimeSelbergCoefficients.support Z, if d ∣ n then PrimeSelbergCoefficients.coefficient Z d else 0

def value (A t : ℝ) (Z : ℕ) : ℂ :=
  ∑' k : ℕ, (weight Z (k+1) : ℂ)*LognormalPhaseVariation.function A t ((k+1 : ℕ) : ℝ)

theorem index_injective (D : ℕ) (hD : 1 ≤ D) :
    Function.Injective (fun k : ℕ ↦ D*(k+1)-1) := by
  intro j k he
  change D*(j+1)-1=D*(k+1)-1 at he
  have hj : 0 < D*(j+1) := Nat.mul_pos (by omega) (by omega)
  have hk : 0 < D*(k+1) := Nat.mul_pos (by omega) (by omega)
  have hm : D*(j+1)=D*(k+1) := by omega
  have hh : j+1=k+1 := mul_left_cancel₀ (by omega : D ≠ 0) hm
  omega

theorem range_iff (D k : ℕ) (hD : 1 ≤ D) :
    k ∈ Set.range (fun j : ℕ ↦ D*(j+1)-1) ↔ D ∣ k+1 := by
  constructor
  · rintro ⟨j,rfl⟩
    have hp : 0 < D*(j+1) := Nat.mul_pos (by omega) (by omega)
    have he : D*(j+1)-1+1=D*(j+1) := by omega
    rw [he]
    exact ⟨j+1,rfl⟩
  · rintro ⟨q,hq⟩
    have hqpos : 0 < q := by
      by_contra hn
      have hq0 : q=0 := by omega
      rw [hq0,mul_zero] at hq
      omega
    refine ⟨q-1,?_⟩
    change D*((q-1)+1)-1=k
    rw [show q-1+1=q by omega,← hq]
    omega

theorem multiple_hasSum (A t : ℝ) (D : ℕ) (hA : 0 < A) (hD : 1 ≤ D) :
    HasSum (fun k : ℕ ↦ if D ∣ k+1 then LognormalPhaseVariation.function A t ((k+1 : ℕ) : ℝ) else 0)
      (LognormalDilatedKernel.multipleValue A t D) := by
  let g : ℕ → ℕ := fun k ↦ D*(k+1)-1
  have hg : Function.Injective g := index_injective D hD
  have hOutside : ∀ k, k ∉ Set.range g →
      (if D ∣ k+1 then LognormalPhaseVariation.function A t ((k+1 : ℕ) : ℝ) else 0)=0 := by
    intro k hk
    exact ite_eq_right (fun hh ↦ hk ((range_iff D k hD).mpr hh))
  have hDP : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hBase : HasSum (fun k : ℕ ↦ LognormalPhaseVariation.function A t ((D : ℝ)*((k+1 : ℕ) : ℝ)))
      (LognormalDilatedKernel.multipleValue A t D) :=
    (LognormalDilatedKernel.summable_terms A t D hA hDP).hasSum
  apply (hg.hasSum_iff hOutside).mp
  apply hBase.congr_fun
  intro k
  have hp : 0 < D*(k+1) := Nat.mul_pos (by omega) (by omega)
  have he : D*(k+1)-1+1=D*(k+1) := by omega
  dsimp only [Function.comp_def,g]
  rw [he,ite_eq_left (show D ∣ D*(k+1) from ⟨k+1,rfl⟩),Nat.cast_mul]

theorem weight_nonneg (Z n : ℕ) : 0 ≤ weight Z n :=
  PrimeSelbergCoefficients.divisor_nonneg Z n

theorem weight_prime (Z p : ℕ) (hZ : 1 ≤ Z) (hp : p.Prime) (hZp : Z < p) : weight Z p=1 :=
  PrimeSelbergCoefficients.prime_value Z p hZ hp hZp

theorem term_identity (A t : ℝ) (Z k : ℕ) :
    (weight Z (k+1) : ℂ)*LognormalPhaseVariation.function A t ((k+1 : ℕ) : ℝ)=
      ∑ d ∈ PrimeSelbergCoefficients.support Z, (PrimeSelbergCoefficients.coefficient Z d : ℂ)*
        (if d ∣ k+1 then LognormalPhaseVariation.function A t ((k+1 : ℕ) : ℝ) else 0) := by
  unfold weight
  push_cast
  rw [sum_mul]
  apply sum_congr rfl
  intro d hd
  by_cases hdk : d ∣ k+1 <;> simp only [hdk,ite_true,ite_false,Complex.ofReal_zero,zero_mul,mul_zero]

theorem weighted_hasSum (A t : ℝ) (Z : ℕ) (hA : 0 < A) :
    HasSum (fun k : ℕ ↦ (weight Z (k+1) : ℂ)*LognormalPhaseVariation.function A t ((k+1 : ℕ) : ℝ))
      (LognormalSelbergKernel.value A t Z) := by
  have hD : ∀ d ∈ PrimeSelbergCoefficients.support Z,
      HasSum (fun k : ℕ ↦ (PrimeSelbergCoefficients.coefficient Z d : ℂ)*
        (if d ∣ k+1 then LognormalPhaseVariation.function A t ((k+1 : ℕ) : ℝ) else 0))
        ((PrimeSelbergCoefficients.coefficient Z d : ℂ)*LognormalDilatedKernel.multipleValue A t d) := by
    intro d hd
    exact (multiple_hasSum A t d hA (Nat.pos_of_mem_divisors hd)).mul_left _
  have hh := hasSum_sum hD
  exact hh.congr_fun (fun k ↦ term_identity A t Z k)

theorem summable_terms (A t : ℝ) (Z : ℕ) (hA : 0 < A) :
    Summable (fun k : ℕ ↦ (weight Z (k+1) : ℂ)*LognormalPhaseVariation.function A t ((k+1 : ℕ) : ℝ)) :=
  (weighted_hasSum A t Z hA).summable

theorem value_identity (A t : ℝ) (Z : ℕ) (hA : 0 < A) : value A t Z=LognormalSelbergKernel.value A t Z :=
  (weighted_hasSum A t Z hA).tsum_eq
end PaperP1.PositiveSelbergSeries
