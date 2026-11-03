module

public import PaperP1.Asymptotics.PrimitiveGeneralMass
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # Primitive triples below a reciprocal fixed nullity threshold

This low-nullity estimate is unconditional. The integer denominator is chosen
before the critical scale and can be arbitrarily large.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LowPrimitiveTripleRankMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrimitiveWindowMass PaperP1.FamilyIndependentMass PaperP1.ConnectedWindowFamilies

theorem uniform_bound (b : ℕ) (hb : 0 < b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ Primitive L I ∧
        (runRelativeNullity L I : ℝ) < (L : ℝ) / b) →
      mass F L ≤ (N : ℝ) ^ (-(3 : ℝ) / 2 + 1 / (b : ℝ) + ε) := by
  classical
  let K := (2 : ℝ) ^ ((C + 1) / b)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨NI, hi⟩ := OriginalWindowFamilyMass.article_10_2 3 (by omega) C (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption K
    (-(3 : ℝ) / 2 + 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NI + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsub : F ⊆ primitiveFamilies (dyadicBlock N) L 3 := by
    intro I hI
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨(hF I hI).1, (hF I hI).2.1⟩,
      (hF I hI).2.2.1⟩
  have hindep : independentMass F L ≤ (N : ℝ) ^ (-(3 : ℝ) / 2 + ε / 2) := by
    have hs : independentMass F L ≤ independentMass (primitiveFamilies (dyadicBlock N) L 3) L :=
      sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ prod_nonneg fun x _ ↦
        MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    exact hs.trans (by simpa only [Nat.cast_ofNat] using
      (hi N (by omega) L (dyadicBlock N) hband Subset.rfl).2.2.2)
  have hpoint (I : Finset ℕ) (hI : I ∈ F) : weight L I ≤
      (K * (N : ℝ) ^ (1 / (b : ℝ))) * ∏ x ∈ I, infiniteMarginal x L := by
    have hpow : (2 ^ runRelativeNullity L I : ℝ) ≤ K * (N : ℝ) ^ (1 / (b : ℝ)) := by
      calc
        _ = (2 : ℝ) ^ (runRelativeNullity L I : ℝ) := (Real.rpow_natCast _ _).symm
        _ ≤ (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) ((hF I hI).2.2.2.le.trans
            (div_le_div_of_nonneg_right (by push_cast; linarith) hbR.le))
        _ ≤ _ := CriticalChannelPowers.window_root_upper (by omega) hb hband
    exact (mul_le_mul_of_nonneg_left hpow (prod_nonneg fun x _ ↦
      MissingBlockProbabilities.infiniteMarginal_nonneg x L)).trans_eq (mul_comm _ _)
  calc
    _ ≤ ∑ I ∈ F, (K * (N : ℝ) ^ (1 / (b : ℝ))) * ∏ x ∈ I, infiniteMarginal x L := sum_le_sum hpoint
    _ = (K * (N : ℝ) ^ (1 / (b : ℝ))) * independentMass F L := by rw [← mul_sum]; rfl
    _ ≤ (K * (N : ℝ) ^ (1 / (b : ℝ))) * (N : ℝ) ^ (-(3 : ℝ) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left hindep (mul_nonneg hK (Real.rpow_nonneg hn.le _))
    _ = K * (N : ℝ) ^ (-(3 : ℝ) / 2 + 1 / (b : ℝ) + ε / 2) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 1
      ring
    _ ≤ (N : ℝ) ^ ((-(3 : ℝ) / 2 + 1 / (b : ℝ) + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.LowPrimitiveTripleRankMass
