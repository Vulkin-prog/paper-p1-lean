module

public import PaperP1.Arithmetic.DyadicPatternWeights

/-! # A single exposure order for every tuple with one fixed size profile -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProfileExposureOrder

open Finset PaperP1.EvenPrimePatterns PaperP1.GrowingDegreeProfiles
open PaperP1.ExposureWeights PaperP1.ExposureOrder PaperP1.OrderedExposure
open PaperP1.PrescribedPatternDivisors PaperP1.DyadicPatternWeights

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {C N d : ℕ}

def delta (J : Code ι C N d) (rank : ι → ℕ) (i : ι) : ℝ :=
  ∑ S ∈ knownPatterns rank i, weight J S

def cost (J : Code ι C N d) (D : ℝ) (rank : ι → ℕ) (i : ι) : ℝ :=
  1 / 2 + degree patterns (weight J) i / (2 * D) - delta J rank i / D

theorem delta_eq_prescribedWeight (J : Code ι C N d) (rank : ι → ℕ)
    (hrank : Function.Injective rank) (fallback i : ι) :
    delta J rank i = prescribedWeight patterns (weight J) (firstByRank rank fallback) i := by
  have hne : ∀ S ∈ (patterns : Finset (Finset ι)), S.Nonempty := by
    intro S hS
    have htwo := (mem_filter.mp hS).2.1
    exact card_pos.mp (by omega)
  exact (prescribedWeight_earlier patterns (weight J) rank hrank fallback hne i).symm

theorem delta_lower (q : ι → ℕ) (J : Code ι C N d) (hN : 2 ≤ N) (hvalid : Valid q J)
    (rank : ι → ℕ) (hrank : Function.Injective rank) (i : ι) :
    delta J rank i ≤ Real.log (prescribed q rank i) / Real.log N := by
  rw [delta_eq_prescribedWeight J rank hrank i i]
  exact prescribed_lower q J hN hvalid rank hrank i i

theorem cost_identity (J : Code ι C N d) (D : ℝ) (rank : ι → ℕ)
    (hrank : Function.Injective rank) (last i : ι) :
    cost J D rank i = 1 / 2 +
      (degree patterns (weight J) i / 2 -
        prescribedWeight patterns (weight J) (firstByRank rank last) i) / D := by
  unfold cost
  rw [delta_eq_prescribedWeight J rank hrank last i]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem cost_sum_identity (J : Code ι C N d) (D : ℝ) (rank : ι → ℕ)
    (hrank : Function.Injective rank) (last : ι) (hlast : ∀ i, rank i ≤ rank last) :
    (∑ i ∈ univ.erase last, cost J D rank i) =
      ((Fintype.card ι : ℝ) - 1) / 2 + correction patterns (weight J) last / D := by
  have hrewrite : (∑ i ∈ univ.erase last, cost J D rank i) =
      ∑ i ∈ univ.erase last, (1 / 2 + (degree patterns (weight J) i / 2 -
        prescribedWeight patterns (weight J) (firstByRank rank last) i) / D) :=
    sum_congr rfl fun i _ ↦ cost_identity J D rank hrank last i
  rw [hrewrite, sum_add_distrib,
    ← sum_div (univ.erase last) (fun i ↦ degree patterns (weight J) i / 2 -
      prescribedWeight patterns (weight J) (firstByRank rank last) i) D,
    exposure_identity patterns (weight J) (firstByRank rank last) last
      (fun S hS ↦ firstByRank_ne_last rank hrank last hlast S (mem_filter.mp hS).2.1)]
  have hvNat : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨last⟩
  simp only [sum_const, card_erase_of_mem (mem_univ last), card_univ, nsmul_eq_mul,
    Nat.cast_sub hvNat, Nat.cast_one]
  ring

theorem exists_profile_order [Nonempty ι] (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (J : Code ι C N d) (hN : 2 ≤ N) (hvalid : Valid q J)
    (K D : ℝ) (hK : 0 < K) (hD : 0 < D) (hheight : ∀ i, (q i : ℝ) ≤ (K * N) ^ D) :
    ∃ (last : ι) (rank : ι → ℕ), Function.Injective rank ∧ (∀ i, rank i ≤ rank last) ∧
      (∑ i ∈ univ.erase last, cost J D rank i) ≤
        Fintype.card ι / 2 + Real.log K / (2 * Real.log N) := by
  have hbudget := profile_height_budget q hq hsq J hN hvalid K D hK hheight
  obtain ⟨last, rank, hrank, hlast, hbound⟩ := exists_exposure_exponent_le
    patterns (weight J) (fun S _ ↦ weight_nonneg J hN S)
    (fun S hS ↦ (mem_filter.mp hS).2.1) D
    (Fintype.card ι * D * Real.log K / Real.log N) hD hbudget
  have hv : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have heq : (Fintype.card ι * D * Real.log K / Real.log N) /
      (2 * D * Fintype.card ι) = Real.log K / (2 * Real.log N) := by field_simp
  rw [heq] at hbound
  have hsum : (∑ i ∈ univ.erase last, cost J D rank i) =
      ((Fintype.card ι : ℝ) - 1) / 2 +
        (∑ i ∈ univ.erase last, (degree patterns (weight J) i / 2 -
          prescribedWeight patterns (weight J) (firstByRank rank last) i)) / D := by
    have hrewrite : (∑ i ∈ univ.erase last, cost J D rank i) =
        ∑ i ∈ univ.erase last, (1 / 2 + (degree patterns (weight J) i / 2 -
          prescribedWeight patterns (weight J) (firstByRank rank last) i) / D) :=
      sum_congr rfl fun i _ ↦ cost_identity J D rank hrank last i
    rw [hrewrite, sum_add_distrib,
      ← sum_div (univ.erase last) (fun i ↦ degree patterns (weight J) i / 2 -
        prescribedWeight patterns (weight J) (firstByRank rank last) i) D]
    have hvNat : 1 ≤ Fintype.card ι := by exact_mod_cast hv
    simp only [sum_const, card_erase_of_mem (mem_univ last), card_univ, nsmul_eq_mul,
      Nat.cast_sub hvNat, Nat.cast_one]
    ring
  exact ⟨last, rank, hrank, hlast, hsum.trans_le hbound⟩

theorem exists_profile_equiv [Nonempty ι] (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (J : Code ι C N d) (hN : 2 ≤ N) (hvalid : Valid q J)
    (K D : ℝ) (hK : 0 < K) (hD : 0 < D) (hheight : ∀ i, (q i : ℝ) ≤ (K * N) ^ D) :
    ∃ (last : ι) (e : ι ≃ Fin (Fintype.card ι)), (e last).val = Fintype.card ι - 1 ∧
      (∑ i ∈ univ.erase last, cost J D (fun j ↦ (e j).val) i) ≤
        Fintype.card ι / 2 + Real.log K / (2 * Real.log N) := by
  obtain ⟨last, rank, hrank, hmax, hcost⟩ := exists_profile_order q hq hsq J hN hvalid K D hK hD hheight
  obtain ⟨e, helast⟩ := exists_equiv_last last
  have heinj : Function.Injective (fun j ↦ (e j).val) := fun i j hij ↦ e.injective (Fin.ext hij)
  have hemax : ∀ i, (e i).val ≤ (e last).val := by
    intro i
    rw [helast]
    have hi := (e i).isLt
    omega
  rw [cost_sum_identity J D rank hrank last hmax] at hcost
  refine ⟨last, e, helast, ?_⟩
  rw [cost_sum_identity J D _ heinj last hemax]
  exact hcost

end PaperP1.ProfileExposureOrder
