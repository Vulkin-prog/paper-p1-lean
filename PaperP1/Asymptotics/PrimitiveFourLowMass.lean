module

public import PaperP1.Asymptotics.PrimitiveGeneralMass
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # The low-nullity primitive four-block mass has unconditional rate three halves -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveFourLowMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrimitiveWindowMass PaperP1.FamilyIndependentMass PaperP1.ConnectedWindowFamilies

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 4 ∧ Primitive L I ∧
        (runRelativeNullity L I : ℝ) < (1 / 2 : ℝ) * L) →
      mass F L ≤ (N : ℝ) ^ (-(3 : ℝ) / 2 + ε) := by
  classical
  let K := (2 : ℝ) ^ ((C + 1) / 2)
  obtain ⟨NI, hi⟩ := OriginalWindowFamilyMass.article_10_2 4 (by norm_num) C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K (-(3 : ℝ) / 2 + ε / 2)
    (ε / 2) (by positivity)
  refine ⟨3 + NI + NF, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsub : F ⊆ primitiveFamilies (dyadicBlock N) L 4 := by
    intro I hI
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨(hF I hI).1, (hF I hI).2.1⟩,
      (hF I hI).2.2.1⟩
  have hindep : independentMass F L ≤ (N : ℝ) ^ (-2 + ε / 2) := by
    have hs : independentMass F L ≤ independentMass (primitiveFamilies (dyadicBlock N) L 4) L :=
      sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ prod_nonneg fun x _ ↦
        MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    exact hs.trans (by simpa only [Nat.cast_ofNat, show -(4 : ℝ) / 2 = -2 by norm_num] using
      (hi N (by omega) L (dyadicBlock N) hband Subset.rfl).2.2.2)
  have hpoint (I : Finset ℕ) (hI : I ∈ F) : weight L I ≤
      (K * (N : ℝ) ^ (1 / 2 : ℝ)) * ∏ x ∈ I, infiniteMarginal x L := by
    have hpow : (2 ^ runRelativeNullity L I : ℝ) ≤ K * (N : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        _ = (2 : ℝ) ^ (runRelativeNullity L I : ℝ) := (Real.rpow_natCast _ _).symm
        _ ≤ (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            have h := (hF I hI).2.2.2
            push_cast
            linarith)
        _ ≤ _ := CriticalChannelPowers.window_root_upper (b := 2) (by omega) (by norm_num) hband
    exact (mul_le_mul_of_nonneg_left hpow (prod_nonneg fun x _ ↦
      MissingBlockProbabilities.infiniteMarginal_nonneg x L)).trans_eq (mul_comm _ _)
  calc
    _ ≤ ∑ I ∈ F, (K * (N : ℝ) ^ (1 / 2 : ℝ)) * ∏ x ∈ I, infiniteMarginal x L := sum_le_sum hpoint
    _ = (K * (N : ℝ) ^ (1 / 2 : ℝ)) * independentMass F L := by rw [← mul_sum]; rfl
    _ ≤ (K * (N : ℝ) ^ (1 / 2 : ℝ)) * (N : ℝ) ^ (-2 + ε / 2) :=
      mul_le_mul_of_nonneg_left hindep (by dsimp [K]; positivity)
    _ = K * (N : ℝ) ^ (-(3 : ℝ) / 2 + ε / 2) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    _ ≤ (N : ℝ) ^ ((-(3 : ℝ) / 2 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PrimitiveFourLowMass
