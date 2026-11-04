module

public import PaperP1.Arithmetic.RawEvenProfileComparison
public import PaperP1.Asymptotics.RawTwoWindowHostCount

/-! # The profile correction counts the actual unrestricted raw relation hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawEvenProfileHosts

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.RawPairRelationRank
  PaperP1.RawEvenProfileComparison PaperP1.LargePrimeOccurrences

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem full_rank_ne_zero_iff_related {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) :
    fullRank x y L ≠ 0 ↔ PaperP1.RawTwoWindowHosts.Related x y (L + 1) := by
  constructor
  · intro hh
    obtain ⟨w, hw⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := F₂)
      (M := LinearMap.ker (pairVertexParityMap x y L))).mp (Nat.pos_of_ne_zero hh)
    have hwval : w.val ≠ 0 := fun hz ↦ hw (Subtype.ext hz)
    have hrel := LinearMap.mem_ker.mp w.property
    change pairVertexParityMap x y L w.val = 0 at hrel
    change (∑ i, w.val i • parityVec (twoStartCompleteVertexLabel x y L i)) = 0 at hrel
    refine ⟨(fun i ↦ w.val (Sum.inl i)), (fun i ↦ w.val (Sum.inr i)), ?_, ?_⟩
    · by_contra hn
      push Not at hn
      apply hwval
      funext i
      cases i with
      | inl i => exact congrFun hn.1 i
      | inr i => exact congrFun hn.2 i
    · simpa only [Fintype.sum_sum_type, twoStartCompleteVertexLabel,
        startCompleteVertexLabel_eq_offset hx, startCompleteVertexLabel_eq_offset hy] using hrel
  · rintro ⟨w, v, hwv, hrel⟩
    let u : LinearMap.ker (pairVertexParityMap x y L) := ⟨Sum.elim w v, by
      rw [LinearMap.mem_ker, pairVertexParityMap, Fintype.linearCombination_apply]
      simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, twoStartCompleteVertexLabel,
        startCompleteVertexLabel_eq_offset hx, startCompleteVertexLabel_eq_offset hy] using hrel⟩
    have hu : u ≠ 0 := by
      intro hh
      have hz := congrArg Subtype.val hh
      rcases hwv with hw | hv
      · apply hw
        funext i
        exact congrFun hz (Sum.inl i)
      · apply hv
        funext i
        exact congrFun hz (Sum.inr i)
    exact Nat.ne_of_gt ((Module.finrank_pos_iff_exists_ne_zero (R := F₂)
      (M := LinearMap.ker (pairVertexParityMap x y L))).mpr ⟨u, hu⟩)

theorem rawHosts_subset {N L : ℕ} (hN : 2 ≤ N) (F : Finset (ℕ × ℕ))
    (hF : F ⊆ (PaperP1.Model.dyadicBlock N) ×ˢ (PaperP1.Model.dyadicBlock N)) :
    rawHosts F L ⊆ PaperP1.RawTwoWindowHosts.hosts N (L + 1) := by
  classical
  intro xy hxy
  obtain ⟨hf, hr⟩ := mem_filter.mp hxy
  have hblock := hF hf
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  have hxpos : 0 < xy.1 := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < xy.2 := by have := (mem_Ico.mp hy).1; omega
  exact mem_filter.mpr ⟨hblock, (full_rank_ne_zero_iff_related hxpos hypos).mp hr⟩

theorem uniform_host_bound (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ, ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ∀ F : Finset (ℕ × ℕ), F ⊆ (PaperP1.Model.dyadicBlock N) ×ˢ (PaperP1.Model.dyadicBlock N) →
        ((rawHosts F L).card : ℝ) ≤ (N : ℝ) ^ (3 / 2 + ε : ℝ) := by
  obtain ⟨N₀, h⟩ := PaperP1.RawTwoWindowHostCount.uniform_bound D hD ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hwidth F hF
  have hc : ((rawHosts F L).card : ℝ) ≤ (PaperP1.RawTwoWindowHosts.hosts N (L + 1)).card := by
    exact_mod_cast card_le_card (rawHosts_subset (by omega : 2 ≤ N) F hF)
  exact hc.trans (h N (by omega) (L + 1) (by omega) hwidth)

end PaperP1.RawEvenProfileHosts
