module

public import PaperP1.Arithmetic.ProjectedWindowLists
public import PaperP1.Asymptotics.ShortOldSpaceProjection
public import PaperP1.Asymptotics.ComparableSplitProductCount

/-! # Actual constant-size witnesses are covered by the complete short-list count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortWitnessListsCount

open Finset Filter PaperP1.ProjectedWindowLists

theorem uniform_short_count (r s m : ℕ) (a b E ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ old : Fin s → ℕ, ∀ G : Finset ℕ,
      0 < W → (W : ℝ) ≤ E * Real.log N → (∀ n ∈ G, a * N ≤ n ∧ (n : ℝ) ≤ b * N) →
      ((shortLists (r := r) G W old m).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε) := by
  classical
  let Eold := (s : ℝ) * (2 * E + 1)
  obtain ⟨c, hc, hcount⟩ := PaperP1.ShortOldSpaceProjection.uniform_projected_lists (ι := Fin r) Eold ε hε
  obtain ⟨Nc, hNc⟩ := hcount a b ha E 1
  obtain ⟨K, _hK, hcompare⟩ := PaperP1.ComparableLogBounds.exists_nat_comparison a b ha
  obtain ⟨Nv, hNv⟩ := PaperP1.ComparableSplitProductCount.width_lt_centre K E 1
  obtain ⟨Nm, hNm⟩ := eventually_atTop.mp
    (PaperP1.ModerateOrder.loglog_tendsto_atTop.eventually (eventually_ge_atTop ((m : ℝ) / c)))
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 1))
  refine ⟨max Nc (max Nv (max Nm Nl)), ?_⟩
  intro N hN W old G hW hwidth hG
  have hlog : 1 ≤ Real.log N := hNl N (by omega)
  have hwidth' : (W : ℝ) ≤ E * (Real.log N) ^ (1 : ℝ) := by simpa only [Real.rpow_one] using hwidth
  have hWn : ∀ n ∈ G, W < n := fun n hn ↦ hNv N (by omega) n W
    (hcompare N n (hG n hn).1 (hG n hn).2).1 hwidth'
  have hm : (m : ℝ) ≤ c * Real.log (Real.log N) := by
    have h := (div_le_iff₀ hc).mp (hNm N (by omega))
    nlinarith only [h]
  have hO : ((oldValues W old).card : ℝ) ≤ Eold * Real.log N := by
    have hcard : ((oldValues W old).card : ℝ) ≤ (s : ℝ) * (2 * W + 1 : ℝ) := by
      exact_mod_cast oldValues_card W old
    have hB : (2 * W + 1 : ℝ) ≤ (2 * E + 1) * Real.log N := by nlinarith only [hwidth, hlog]
    exact hcard.trans (by simpa only [Eold, mul_assoc] using
      mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg s))
  have hsub : shortLists (r := r) G W old m ⊆ PaperP1.ShortProjectedLists.lists (oldValues W old) G N W c := by
    intro n hn
    obtain ⟨hnbase, A, hA, hsize⟩ := mem_filter.mp hn
    have hnG := ((mem_lists G W old n).mp hnbase).1
    apply PaperP1.ShortProjectedLists.mem_lists_of_even_nonempty (oldValues W old) G N W c n hnG A
    · intro i
      have hd := hA.1 i
      refine ⟨hd.1, admissible_nonempty W (n i) (A i) hd, ?_, (PaperP1.BoundedIntegerMotifs.subset_offsets W (A i)).mp hd.2.1⟩
      exact (show ((A i).card : ℝ) ≤ m by exact_mod_cast hsize i).trans hm
    · have hproj := hA.2
      have heq : (∑ i, vector (n i) (A i)) = ∑ i, PaperP1.Arithmetic.parityVec
          (PaperP1.SplitOffsetProducts.product (A i) (n i)) := by
        apply sum_congr rfl
        intro i _
        exact vector_eq_product W (n i) (A i) (hWn (n i) (hnG i)) (hA.1 i).2.1
      rwa [heq] at hproj
  have hcard := card_le_card hsub
  exact (show ((shortLists (r := r) G W old m).card : ℝ) ≤
    ((PaperP1.ShortProjectedLists.lists (ι := Fin r) (oldValues W old) G N W c).card : ℝ) by exact_mod_cast hcard).trans
      (by simpa only [Fintype.card_fin] using hNc N (by omega) W (oldValues W old) G hW hwidth' hO hG)

end PaperP1.ShortWitnessListsCount
