module

public import PaperP1.Asymptotics.DensePrimitiveTripleMassUnderInputs
public import PaperP1.Asymptotics.PrimitiveGeneralMass
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # Every fixed primitive order at least three has rank-weight mass at most N^(-1+epsilon) under the recorded geometry -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedPrimitiveMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrimitiveWindowMass PaperP1.FamilyIndependentMass PaperP1.ConnectedWindowFamilies
  PaperP1.DensePrimitiveTripleMassUnderInputs

theorem uniform_triples (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p → ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ Primitive L I) →
      mass F L ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let K := (2 : ℝ) ^ ((C + 1) / 4)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨p, hp⟩ := DensePrimitiveTripleMassUnderInputs.uniform_bound C δ hδ
  obtain ⟨NI, hi⟩ := OriginalWindowFamilyMass.article_10_2 3 (by decide) C δ hδ
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (K + 1) (-1 + δ) (3 * ε / 4) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨ND, _hND, hd⟩ := hp hgeo
  refine ⟨3 + NI + NF + ND, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := fun I : Finset ℕ ↦ (1 / 4 : ℝ) * L ≤ (runRelativeNullity L I : ℝ)
  let FD := F.filter P
  let FL := F.filter (fun I ↦ ¬ P I)
  have hdense : mass FD L ≤ (N : ℝ) ^ (-1 + δ) := hd N (by omega) L hband FD (by
    intro I hI
    obtain ⟨hIF, hdim⟩ := mem_filter.mp hI
    obtain ⟨hIG, hcard, hprim⟩ := hF I hIF
    exact ⟨hIG, hcard, hprim, hdim⟩)
  have hsub : FL ⊆ primitiveFamilies (dyadicBlock N) L 3 := by
    intro I hI
    obtain ⟨hIG, hcard, hprim⟩ := hF I (mem_filter.mp hI).1
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hIG, hcard⟩, hprim⟩
  have hindep : independentMass FL L ≤ (N : ℝ) ^ (-3 / 2 + δ) := by
    have hs : independentMass FL L ≤ independentMass (primitiveFamilies (dyadicBlock N) L 3) L :=
      sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ prod_nonneg fun x _ ↦
        MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    exact hs.trans (by simpa only [Nat.cast_ofNat] using
      (hi N (by omega) L (dyadicBlock N) hband Subset.rfl).2.2.2)
  have hpoint (I : Finset ℕ) (hI : I ∈ FL) : weight L I ≤
      (K * (N : ℝ) ^ (1 / 4 : ℝ)) * ∏ x ∈ I, infiniteMarginal x L := by
    have hdim : ¬ (1 / 4 : ℝ) * L ≤ (runRelativeNullity L I : ℝ) := (mem_filter.mp hI).2
    have hpow : (2 ^ runRelativeNullity L I : ℝ) ≤ K * (N : ℝ) ^ (1 / 4 : ℝ) := by
      calc
        _ = (2 : ℝ) ^ (runRelativeNullity L I : ℝ) := (Real.rpow_natCast _ _).symm
        _ ≤ (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          have hlt := lt_of_not_ge hdim
          push_cast
          linarith only [hlt])
        _ ≤ _ := CriticalChannelPowers.window_root_upper (b := 4) (by omega) (by decide) hband
    exact (mul_le_mul_of_nonneg_left hpow (prod_nonneg fun x _ ↦
      MissingBlockProbabilities.infiniteMarginal_nonneg x L)).trans_eq (mul_comm _ _)
  have hlow : mass FL L ≤ K * (N : ℝ) ^ (-1 + δ) := by
    calc
      _ ≤ ∑ I ∈ FL, (K * (N : ℝ) ^ (1 / 4 : ℝ)) * ∏ x ∈ I, infiniteMarginal x L := sum_le_sum hpoint
      _ = (K * (N : ℝ) ^ (1 / 4 : ℝ)) * independentMass FL L := by rw [← mul_sum]; rfl
      _ ≤ (K * (N : ℝ) ^ (1 / 4 : ℝ)) * (N : ℝ) ^ (-3 / 2 + δ) :=
        mul_le_mul_of_nonneg_left hindep (mul_nonneg hK (Real.rpow_nonneg hn.le _))
      _ = K * (N : ℝ) ^ ((1 / 4 : ℝ) + (-3 / 2 + δ)) := by rw [mul_assoc, ← Real.rpow_add hn]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hK
  calc
    _ = mass FD L + mass FL L := (sum_filter_add_sum_filter_not F P (weight L)).symm
    _ ≤ (K + 1) * (N : ℝ) ^ (-1 + δ) := by linarith only [hdense, hlow]
    _ ≤ (N : ℝ) ^ ((-1 + δ) + 3 * ε / 4) := hf N (by omega)
    _ = _ := by congr 1; dsimp [δ]; ring

theorem uniform_fixed (r : ℕ) (hr : 3 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p → ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧ Primitive L I) →
      mass F L ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨p, hp⟩ := uniform_triples C ε hε
  refine ⟨p, ?_⟩
  intro hgeo
  by_cases hthree : r = 3
  · subst r
    exact hp hgeo
  · obtain ⟨NM, hm⟩ := PrimitiveGeneralMass.uniform_submass r (by omega) C ε hε
    refine ⟨3 + NM, by omega, ?_⟩
    intro N hN L hband F hF
    have hsub : F ⊆ primitiveFamilies (dyadicBlock N) L r := by
      intro I hI
      obtain ⟨hIG, hcard, hprim⟩ := hF I hI
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hIG, hcard⟩, hprim⟩
    apply (hm N (by omega) L (dyadicBlock N) F hband Subset.rfl hsub).trans
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
    have hrR : (4 : ℝ) ≤ r := by exact_mod_cast (show 4 ≤ r by omega)
    linarith only [hrR]

end PaperP1.FixedPrimitiveMassUnderInputs
