module

public import PaperP1.Arithmetic.GroupedPrescribedDivisors
public import PaperP1.Combinatorics.FinitePairPartition
public import Mathlib.Data.Finset.Max

/-! # An actual selected quadratic block and its finite logarithmic budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedQuadraticBudget

open Finset PaperP1.SplitOffsetProducts PaperP1.GroupedKernelResultants
open PaperP1.GroupedPrescribedDivisors PaperP1.SquarefreeOutsideDivisor

def weight (e n : ℕ) (B : Finset ℤ) : ℝ := Real.log (kernel B n) - 2 * Real.log (assigned e n B)

theorem exists_le_average {ι : Type*} (P : Finset ι) (hP : P.Nonempty) (w : ι → ℝ) (T : ℝ)
    (hbudget : (∑ i ∈ P, w i) ≤ T) : ∃ i ∈ P, w i ≤ T / P.card := by
  classical
  obtain ⟨i, hi, hmin⟩ := P.exists_min_image w hP
  have hc : (0 : ℝ) < P.card := by exact_mod_cast card_pos.mpr hP
  refine ⟨i, hi, (le_div_iff₀ hc).mpr ?_⟩
  calc
    w i * P.card = ∑ _j ∈ P, w i := by simp [mul_comm]
    _ ≤ ∑ j ∈ P, w j := sum_le_sum (fun j hj ↦ hmin j hj)
    _ ≤ T := hbudget

theorem total_weight_budget (P : Finset (Finset ℤ)) (e n : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id)
    (hvalues : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0)
    (he : e ∣ kernel (P.biUnion id) n) :
    (∑ B ∈ P, weight (outside e (resultant (P.biUnion id))) n B) ≤
      Real.log (kernel (P.biUnion id) n) - 2 * Real.log e + 4 * Real.log (resultant (P.biUnion id)) := by
  let A := P.biUnion id
  let e' := outside e (resultant A)
  have heSF : Squarefree e := (kernel_squarefree A n).squarefree_of_dvd he
  have halloc := (outside_source_allocation P e n hdis hvalues he).1
  have hlogM : Real.log (grouped P n : ℝ) = ∑ B ∈ P, Real.log (kernel B n) := by
    unfold grouped
    rw [Nat.cast_prod]
    exact Real.log_prod (fun B _ ↦ by exact_mod_cast (kernel_pos B n).ne')
  have hlogE : Real.log (e' : ℝ) = ∑ B ∈ P, Real.log (assigned e' n B) := by
    have heq : (∏ B ∈ P, assigned e' n B) = e' := halloc
    calc
      _ = Real.log ((∏ B ∈ P, assigned e' n B : ℕ) : ℝ) :=
        congrArg (fun m : ℕ ↦ Real.log (m : ℝ)) heq.symm
      _ = _ := by
        rw [Nat.cast_prod]
        exact Real.log_prod (fun B _ ↦ by exact_mod_cast (assigned_pos e' n B).ne')
  obtain ⟨R, hRD, hR⟩ := grouped_overlap_decomposition P n hdis hvalues
  have hRpos : 0 < R := Nat.pos_of_dvd_of_pos hRD (resultant_pos A)
  have hRle : R ≤ resultant A := Nat.le_of_dvd (resultant_pos A) hRD
  have hlogR := Real.log_le_log (by exact_mod_cast hRpos : (0 : ℝ) < R)
    (by exact_mod_cast hRle : (R : ℝ) ≤ resultant A)
  have hRreal : (grouped P n : ℝ) = (kernel A n : ℝ) * (R : ℝ) ^ 2 := by exact_mod_cast hR
  have hlogRmul : Real.log (grouped P n : ℝ) = Real.log (kernel A n) + 2 * Real.log R := by
    rw [hRreal, Real.log_mul (by exact_mod_cast (kernel_pos A n).ne') (by positivity), Real.log_pow]
    norm_num
  have hloss := log_loss e (resultant A) heSF (resultant_pos A)
  have hsum : (∑ B ∈ P, weight e' n B) = Real.log (grouped P n) - 2 * Real.log e' := by
    unfold weight
    rw [sum_sub_distrib, ← mul_sum, ← hlogM, ← hlogE]
  change (∑ B ∈ P, weight e' n B) ≤ _
  rw [hsum, hlogRmul]
  change Real.log (kernel A n) + 2 * Real.log R - 2 * Real.log e' ≤
    Real.log (kernel A n) - 2 * Real.log e + 4 * Real.log (resultant A)
  nlinarith only [hlogR, hloss]

theorem selected_source_block (P : Finset (Finset ℤ)) (hP : P.Nonempty) (e n : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id)
    (hvalues : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0)
    (he : e ∣ kernel (P.biUnion id) n) :
    ∃ B ∈ P, weight (outside e (resultant (P.biUnion id))) n B ≤
      (Real.log (kernel (P.biUnion id) n) - 2 * Real.log e +
        4 * Real.log (resultant (P.biUnion id))) / P.card :=
  exists_le_average P hP _ _ (total_weight_budget P e n hdis hvalues he)

theorem exists_selected_pair (A : Finset ℤ) (heven : Even A.card) (hcard : 2 ≤ A.card) (e n : ℕ)
    (hvalues : ∀ a ∈ A, (n : ℤ) + a ≠ 0) (he : e ∣ kernel A n) :
    ∃ P : Finset (Finset ℤ), Set.PairwiseDisjoint (P : Set (Finset ℤ)) id ∧
      P.biUnion id = A ∧ (∀ B ∈ P, B.card = 2) ∧
      ∃ B ∈ P, weight (outside e (resultant A)) n B ≤
        (Real.log (kernel A n) - 2 * Real.log e + 4 * Real.log (resultant A)) / ((A.card : ℝ) / 2) := by
  obtain ⟨P, hdis, hunion, hpairs⟩ := PaperP1.FinitePairPartition.exists_pair_partition A heven
  have hcardP := PaperP1.FinitePairPartition.partition_cardinality A P hdis hunion hpairs
  have hP : P.Nonempty := card_pos.mp (by omega)
  have hvalues' : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0 := by rwa [hunion]
  have he' : e ∣ kernel (P.biUnion id) n := by rwa [hunion]
  obtain ⟨B, hB, hbudget⟩ := selected_source_block P hP e n hdis hvalues' he'
  rw [hunion] at hbudget
  have hc : (P.card : ℝ) = (A.card : ℝ) / 2 := by
    have hr : (A.card : ℝ) = 2 * (P.card : ℝ) := by exact_mod_cast hcardP
    linarith
  rw [hc] at hbudget
  exact ⟨P, hdis, hunion, hpairs, B, hB, hbudget⟩

end PaperP1.SelectedQuadraticBudget
