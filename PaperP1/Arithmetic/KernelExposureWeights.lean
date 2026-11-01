module

public import PaperP1.Arithmetic.KernelTuplePatterns
public import PaperP1.Combinatorics.OrderedExposure

/-! # Actual logarithmic weights and the finite moment exposure exponent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.KernelExposureWeights

open Finset PaperP1.EvenPrimePatterns PaperP1.ExposureWeights PaperP1.ExposureOrder
open PaperP1.OrderedExposure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weight (q : ι → ℕ) (N : ℕ) (S : Finset ι) : ℝ := Real.log (part q S) / Real.log N

theorem weight_nonneg (q : ι → ℕ) (N : ℕ) (hN : 2 ≤ N) (S : Finset ι) :
    0 ≤ weight q N S := by
  apply div_nonneg
  · exact Real.log_nonneg (by exact_mod_cast part_pos q S)
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))

theorem degree_identity (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (N : ℕ) (i : ι) :
    degree patterns (weight q N) i = Real.log (q i) / Real.log N := by
  have hprod := even_reconstruction q hq hsq i
  have hlog : Real.log (q i : ℝ) =
      ∑ S ∈ patterns.filter (fun S ↦ i ∈ S), Real.log (part q S : ℝ) := by
    calc
      _ = Real.log ((∏ S ∈ patterns.filter (fun S ↦ i ∈ S), part q S : ℕ) : ℝ) :=
        congrArg (fun m : ℕ ↦ Real.log (m : ℝ)) hprod.symm
      _ = _ := by
        rw [Nat.cast_prod, Real.log_prod]
        intro S _
        exact_mod_cast (part_pos q S).ne'
  unfold degree weight
  rw [← sum_div, ← hlog]

theorem total_weight (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (N : ℕ) :
    (∑ S ∈ patterns, (S.card : ℝ) * weight q N S) = ∑ i, Real.log (q i) / Real.log N := by
  rw [← total_degree]
  apply sum_congr rfl
  intro i _
  exact degree_identity q hq hsq N i

theorem logarithmic_height_budget (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (N : ℕ) (hN : 2 ≤ N) (K d : ℝ) (hK : 0 < K)
    (hheight : ∀ i, (q i : ℝ) ≤ (K * N) ^ d) :
    (∑ S ∈ patterns, (S.card : ℝ) * weight q N S) ≤
      Fintype.card ι * d + Fintype.card ι * d * Real.log K / Real.log N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hKN : 0 < K * N := mul_pos hK hn
  have hlocal : ∀ i, Real.log (q i) / Real.log N ≤ d + d * Real.log K / Real.log N := by
    intro i
    have hp : (0 : ℝ) < q i := by exact_mod_cast Nat.pos_of_ne_zero (hq i).ne_zero
    have hlog := Real.log_le_log hp (hheight i)
    rw [Real.log_rpow hKN, Real.log_mul hK.ne' hn.ne'] at hlog
    apply (div_le_iff₀ hl).mpr
    have heq : (d + d * Real.log K / Real.log N) * Real.log N = d * (Real.log K + Real.log N) := by
      field_simp; ring
    rw [heq]
    exact hlog
  rw [total_weight q hq hsq N]
  calc
    _ ≤ ∑ _i : ι, (d + d * Real.log K / Real.log N) := sum_le_sum fun i _ ↦ hlocal i
    _ = _ := by simp; ring

theorem exists_actual_exposure [Nonempty ι] (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (N : ℕ) (hN : 2 ≤ N) (K d : ℝ) (hK : 0 < K) (hd : 0 < d)
    (hheight : ∀ i, (q i : ℝ) ≤ (K * N) ^ d) :
    ∃ (last : ι) (rank : ι → ℕ), Function.Injective rank ∧ (∀ i, rank i ≤ rank last) ∧
      ((Fintype.card ι : ℝ) - 1) / 2 +
        (∑ i ∈ univ.erase last,
          (degree patterns (weight q N) i / 2 -
            prescribedWeight patterns (weight q N) (firstByRank rank last) i)) / d ≤
        Fintype.card ι / 2 + Real.log K / (2 * Real.log N) := by
  have hbudget := logarithmic_height_budget q hq hsq N hN K d hK hheight
  obtain ⟨last, rank, hrank, hmax, hexp⟩ := exists_exposure_exponent_le
    patterns (weight q N) (fun S _ ↦ weight_nonneg q N hN S)
    (fun S hS ↦ (mem_filter.mp hS).2.1) d
    (Fintype.card ι * d * Real.log K / Real.log N) hd hbudget
  have hv : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have heq : (Fintype.card ι * d * Real.log K / Real.log N) /
      (2 * d * Fintype.card ι) = Real.log K / (2 * Real.log N) := by
    field_simp
  rw [heq] at hexp
  exact ⟨last, rank, hrank, hmax, hexp⟩

end PaperP1.KernelExposureWeights
