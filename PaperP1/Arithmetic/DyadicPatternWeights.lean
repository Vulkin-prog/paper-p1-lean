module

public import PaperP1.Asymptotics.GrowingDegreeProfiles

/-! # Fixed dyadic profile weights controlling every tuple in that profile -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicPatternWeights

open Finset PaperP1.EvenPrimePatterns PaperP1.GrowingDegreeProfiles
open PaperP1.ExposureWeights PaperP1.ExposureOrder PaperP1.OrderedExposure
open PaperP1.PrescribedPatternDivisors

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {C N d : ℕ}

def index (J : Code ι C N d) (S : Finset ι) : ℕ :=
  if hS : S ∈ patterns then (J ⟨S, hS⟩).val else 0

def weight (J : Code ι C N d) (S : Finset ι) : ℝ :=
  (index J S : ℝ) * Real.log 2 / Real.log N

def Valid (q : ι → ℕ) (J : Code ι C N d) : Prop :=
  ∀ S ∈ patterns, 2 ^ index J S ≤ part q S ∧ part q S < 2 * 2 ^ index J S

theorem index_mem (J : Code ι C N d) (S : Finset ι) (hS : S ∈ patterns) :
    index J S = (J ⟨S, hS⟩).val := by simp only [index, dite_eq_left hS]

theorem actual_profile_valid (q : ι → ℕ) (hq : ∀ i, 0 < q i) (hN : 0 < N)
    (hheight : ∀ i, q i ≤ height C N d) : Valid q (actual_profile q hq C N d hN hheight) := by
  intro S hS
  rw [index_mem _ S hS]
  exact actual_profile_window q hq C N d hN hheight ⟨S, hS⟩

theorem weight_nonneg (J : Code ι C N d) (hN : 2 ≤ N) (S : Finset ι) : 0 ≤ weight J S := by
  unfold weight
  exact div_nonneg (mul_nonneg (by positivity) (Real.log_pos (by norm_num)).le)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))

theorem weight_power (J : Code ι C N d) (hN : 2 ≤ N) (S : Finset ι) :
    (N : ℝ) ^ weight J S = (2 : ℝ) ^ index J S := by
  have heq : weight J S = PaperP1.DyadicQuadraticBudgets.exponent N (index J S) := by
    unfold weight PaperP1.DyadicQuadraticBudgets.exponent
    rw [Real.log_pow]
  rw [heq]
  exact PaperP1.DyadicQuadraticBudgets.exponent_identity N (index J S) hN

theorem lower_weight (q : ι → ℕ) (J : Code ι C N d) (hN : 2 ≤ N) (hvalid : Valid q J)
    (S : Finset ι) (hS : S ∈ patterns) : weight J S ≤ PaperP1.KernelExposureWeights.weight q N S := by
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpow : (2 : ℝ) ^ index J S ≤ part q S := by exact_mod_cast (hvalid S hS).1
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ index J S) hpow
  rw [Real.log_pow] at hlog
  exact div_le_div_of_nonneg_right hlog hl.le

theorem upper_weight (q : ι → ℕ) (J : Code ι C N d) (hN : 2 ≤ N) (hvalid : Valid q J)
    (S : Finset ι) (hS : S ∈ patterns) : PaperP1.KernelExposureWeights.weight q N S ≤
      weight J S + Real.log 2 / Real.log N := by
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpow : (part q S : ℝ) ≤ 2 * (2 : ℝ) ^ index J S := by exact_mod_cast (hvalid S hS).2.le
  have hlog := Real.log_le_log (by exact_mod_cast part_pos q S : (0 : ℝ) < part q S) hpow
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have hdiv := div_le_div_of_nonneg_right hlog hl.le
  unfold weight PaperP1.KernelExposureWeights.weight
  convert hdiv using 1; ring

theorem coordinate_upper (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (J : Code ι C N d) (hN : 2 ≤ N) (hvalid : Valid q J) (i : ι) :
    (q i : ℝ) ≤ (2 : ℝ) ^ (patterns : Finset (Finset ι)).card * (N : ℝ) ^ degree patterns (weight J) i := by
  let I := patterns.filter fun S : Finset ι ↦ i ∈ S
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprod : (q i : ℝ) = ∏ S ∈ I, (part q S : ℝ) := by
    exact_mod_cast (even_reconstruction q hq hsq i).symm
  calc
    _ = ∏ S ∈ I, (part q S : ℝ) := hprod
    _ ≤ ∏ S ∈ I, (2 * (N : ℝ) ^ weight J S) := by
      apply prod_le_prod₀ (fun _ _ ↦ by positivity)
      intro S hS
      rw [weight_power J hN S]
      exact_mod_cast (hvalid S (mem_filter.mp hS).1).2.le
    _ = (2 : ℝ) ^ I.card * (N : ℝ) ^ degree patterns (weight J) i := by
      rw [prod_mul_distrib, prod_const, ← Real.rpow_sum_of_pos hn]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (card_le_card (filter_subset _ _)))
      (Real.rpow_nonneg hn.le _)

theorem prescribed_lower (q : ι → ℕ) (J : Code ι C N d) (hN : 2 ≤ N) (hvalid : Valid q J)
    (rank : ι → ℕ) (hrank : Function.Injective rank) (fallback i : ι) :
    prescribedWeight patterns (weight J) (firstByRank rank fallback) i ≤
      Real.log (prescribed q rank i) / Real.log N := by
  have hne : ∀ S ∈ (patterns : Finset (Finset ι)), S.Nonempty := by
    intro S hS
    exact card_pos.mp (by have hc := (mem_filter.mp hS).2.1; omega)
  rw [PaperP1.PrescribedPatternDivisors.logarithmic_prescribed q rank hrank fallback N i,
    prescribedWeight_earlier patterns (weight J) rank hrank fallback hne,
    prescribedWeight_earlier patterns (PaperP1.KernelExposureWeights.weight q N) rank hrank fallback hne]
  exact sum_le_sum fun S hS ↦ lower_weight q J hN hvalid S (mem_filter.mp hS).1

theorem profile_height_budget (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (J : Code ι C N d) (hN : 2 ≤ N) (hvalid : Valid q J)
    (K D : ℝ) (hK : 0 < K) (hheight : ∀ i, (q i : ℝ) ≤ (K * N) ^ D) :
    (∑ S ∈ patterns, (S.card : ℝ) * weight J S) ≤
      Fintype.card ι * D + Fintype.card ι * D * Real.log K / Real.log N := by
  have hlower : (∑ S ∈ patterns, (S.card : ℝ) * weight J S) ≤
      ∑ S ∈ patterns, (S.card : ℝ) * PaperP1.KernelExposureWeights.weight q N S :=
    sum_le_sum fun S hS ↦ mul_le_mul_of_nonneg_left (lower_weight q J hN hvalid S hS) (by positivity)
  exact hlower.trans (PaperP1.KernelExposureWeights.logarithmic_height_budget q hq hsq N hN K D hK hheight)

end PaperP1.DyadicPatternWeights
