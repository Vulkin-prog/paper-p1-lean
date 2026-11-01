module

public import PaperP1.Arithmetic.PrescribedPatternDivisors

/-! # The exposure exponent for the actual prescribed kernel divisors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.KernelExposureExponent

open Finset PaperP1.EvenPrimePatterns PaperP1.KernelExposureWeights
open PaperP1.ExposureWeights PaperP1.ExposureOrder PaperP1.OrderedExposure
open PaperP1.PrescribedPatternDivisors

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cost (q : ι → ℕ) (N : ℕ) (d : ℝ) (rank : ι → ℕ) (i : ι) : ℝ :=
  1 / 2 + Real.log (q i) / (2 * d * Real.log N) -
    Real.log (prescribed q rank i) / (d * Real.log N)

theorem cost_identity (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (N : ℕ) (d : ℝ) (rank : ι → ℕ)
    (hrank : Function.Injective rank) (last i : ι) :
    cost q N d rank i = 1 / 2 +
      (degree patterns (weight q N) i / 2 -
        prescribedWeight patterns (weight q N) (firstByRank rank last) i) / d := by
  rw [degree_identity q hq hsq N i, ← logarithmic_prescribed q rank hrank last N i]
  unfold cost
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem cost_sum_identity (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (N : ℕ) (d : ℝ) (rank : ι → ℕ)
    (hrank : Function.Injective rank) (last : ι) (hlast : ∀ i, rank i ≤ rank last) :
    (∑ i ∈ univ.erase last, cost q N d rank i) =
      ((Fintype.card ι : ℝ) - 1) / 2 + correction patterns (weight q N) last / d := by
  have hv : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨last⟩
  have hsum : (∑ i ∈ univ.erase last, cost q N d rank i) =
      ∑ i ∈ univ.erase last, (1 / 2 +
        (degree patterns (weight q N) i / 2 -
          prescribedWeight patterns (weight q N) (firstByRank rank last) i) / d) :=
    sum_congr rfl (fun i _ ↦ cost_identity q hq hsq N d rank hrank last i)
  rw [hsum, sum_add_distrib]
  rw [← sum_div (univ.erase last) (fun i ↦ degree patterns (weight q N) i / 2 -
    prescribedWeight patterns (weight q N) (firstByRank rank last) i) d]
  rw [exposure_identity patterns (weight q N) (firstByRank rank last) last
      (fun S hS ↦ firstByRank_ne_last rank hrank last hlast S (mem_filter.mp hS).2.1)]
  simp only [sum_const, card_erase_of_mem (mem_univ last), card_univ, nsmul_eq_mul,
    Nat.cast_sub hv, Nat.cast_one]
  ring

theorem exists_cost_bound [Nonempty ι] (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (N : ℕ) (hN : 2 ≤ N) (K d : ℝ) (hK : 0 < K) (hd : 0 < d)
    (hheight : ∀ i, (q i : ℝ) ≤ (K * N) ^ d) :
    ∃ (last : ι) (rank : ι → ℕ), Function.Injective rank ∧ (∀ i, rank i ≤ rank last) ∧
      (∑ i ∈ univ.erase last, cost q N d rank i) ≤
        Fintype.card ι / 2 + Real.log K / (2 * Real.log N) := by
  obtain ⟨last, rank, hrank, hmax, hbound⟩ := exists_actual_exposure q hq hsq N hN K d hK hd hheight
  refine ⟨last, rank, hrank, hmax, ?_⟩
  rw [cost_sum_identity q hq hsq N d rank hrank last hmax]
  rw [exposure_identity patterns (weight q N) (firstByRank rank last) last
    (fun S hS ↦ firstByRank_ne_last rank hrank last hmax S (mem_filter.mp hS).2.1)] at hbound
  exact hbound

end PaperP1.KernelExposureExponent
