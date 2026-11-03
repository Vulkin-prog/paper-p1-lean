module

public import PaperP1.Asymptotics.OrdinaryIndependentDeficitBound
public import PaperP1.Asymptotics.RetainedGoodPairMass
public import PaperP1.Asymptotics.UniformIndependentDeficit

/-! # The two literal independent retained-reference deficits have unconditional powers one and seven-sixths -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedIndependentDeficitRates

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.RetainedReferenceTheorem PaperP1.RetainedIndependentDeficitComparison
  PaperP1.RetainedCardinalityDeficits

theorem first_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → firstMass N L ≤ (N : ℝ) ^ (-1 + ε) := by
  let M := 4 * (2 : ℝ) ^ C
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨NT, _hNT, ht⟩ := OrdinaryIndependentDeficitBound.uniform_bound C M ε hM hε
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  refine ⟨10 + NT + NM, by omega, ?_⟩
  intro N hN L hband
  rw [first_eq]
  apply ht N (by omega) L hband (fun x ↦ 2 * infiniteMarginal x L)
    (fun x ↦ mul_nonneg (by norm_num) (MissingBlockProbabilities.infiniteMarginal_nonneg x L))
  · intro x hx
    calc
      _ ≤ 2 * (2 * (2 : ℝ) ^ C / N) :=
        mul_le_mul_of_nonneg_left (hm N (by omega) L hband x hx) (by norm_num)
      _ = _ := by dsimp [M]; ring
  · exact filter_subset _ _

theorem second_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
        secondMass H N L ≤ (N : ℝ) ^ (-7 / 6 + ε) := by
  obtain ⟨NI, _hNI, hi⟩ := UniformIndependentDeficit.uniform_bound 2 2 C (ε / 4) (by norm_num) (by positivity)
  obtain ⟨NB, _hNB, hb⟩ := RetainedGoodPairMass.uniform_bound C (ε / 4) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-7 / 6 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NI + NB + NF, by omega, ?_⟩
  intro N hN L hband H
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hE (e : Finset ℕ) (he : e ∈ GoodEdgeCompression.goodEdges H N L) :
      IndependentExtensionDeficit.deficit (RegularStarts.regularStarts N L) e
        (SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e) L 2 ≤ (N : ℝ) ^ (-1 / 2 + ε / 4) := by
    have hecard := RetainedGoodEdges.good_pair_card H N L e he
    have hereg := RetainedGoodEdges.good_pair_regular (by omega : 2 ≤ N) e he
    have heN : e ⊆ dyadicBlock N := hereg.trans (filter_subset _ _)
    exact hi N (by omega) L hband (RegularStarts.regularStarts N L) (filter_subset _ _) e heN hecard.le
      (SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e)
      (IntersectionExceptional.span_le_raw e L (fun x hx ↦ by
        have h := (mem_Ico.mp (heN hx)).1
        omega))
  calc
    _ = 4 * ∑ e ∈ GoodEdgeCompression.goodEdges H N L, infiniteJointMoment L e *
        IndependentExtensionDeficit.deficit (RegularStarts.regularStarts N L) e
          (SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e) L 2 := second_eq H N L
    _ ≤ 4 * ∑ e ∈ GoodEdgeCompression.goodEdges H N L,
        infiniteJointMoment L e * (N : ℝ) ^ (-1 / 2 + ε / 4) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun e he ↦ mul_le_mul_of_nonneg_left
        (hE e he) (infiniteJointMoment_nonneg L e))) (by norm_num)
    _ = 4 * (beta H N L * (N : ℝ) ^ (-1 / 2 + ε / 4)) := by rw [← sum_mul]; rfl
    _ ≤ 4 * ((N : ℝ) ^ (-2 / 3 + ε / 4) * (N : ℝ) ^ (-1 / 2 + ε / 4)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hb N (by omega) L hband H)
        (Real.rpow_nonneg hn.le _)) (by norm_num)
    _ = 4 * (N : ℝ) ^ (-7 / 6 + ε / 2) := by
      rw [← Real.rpow_add hn]
      congr 2
      ring
    _ ≤ (N : ℝ) ^ ((-7 / 6 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_strong (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      firstMass N L ≤ (N : ℝ) ^ (-1 + ε) ∧ secondMass H N L ≤ (N : ℝ) ^ (-7 / 6 + ε) := by
  obtain ⟨NF, _hNF, hf⟩ := first_bound C ε hε
  obtain ⟨NG, _hNG, hg⟩ := second_bound C ε hε
  refine ⟨10 + NF + NG, by omega, ?_⟩
  intro N hN L hband H
  exact ⟨hf N (by omega) L hband, hg N (by omega) L hband H⟩

theorem companion_T17_1 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      (∑ r ∈ range ((RegularStarts.regularStarts N L).card + 1), (2 : ℝ) ^ r * firstCoefficient N L r) ≤
        (N : ℝ) ^ (-4 / 5 + ε) + ((L + 1 : ℕ) : ℝ) / N ∧
      (∑ r ∈ range ((RegularStarts.regularStarts N L).card + 1), (2 : ℝ) ^ r * secondCoefficient H N L r) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NR, _hNR, hr⟩ := uniform_strong C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨10 + NR + NG, by omega, ?_⟩
  intro N hN L hband H
  have hNtwo : 2 ≤ N := by omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  obtain ⟨hf, hs⟩ := hr N (by omega) L hband H
  rw [← RetainedDeficitGrouping.firstMass_grouped hNtwo hL,
    ← RetainedDeficitGrouping.secondMass_grouped hNtwo hL H]
  refine ⟨?_, hs.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))⟩
  exact hf.trans ((Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)).trans
    (le_add_of_nonneg_right (by positivity)))

end PaperP1.RetainedIndependentDeficitRates
