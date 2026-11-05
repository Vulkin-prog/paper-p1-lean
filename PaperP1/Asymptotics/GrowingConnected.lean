module

public import PaperP1.Asymptotics.HighNullityClosure
public import PaperP1.Asymptotics.AllCardinalityConnected
public import PaperP1.Asymptotics.SublogCardinalityCap

/-! # Companion T16.3 on its literal linear size range, with exponent1 and an actual sublogarithmic corollary -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GrowingConnected

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

theorem uniform_linear_range (t : ℕ) (η u C ε : ℝ) (htEven : Even t) (ht : 2 ≤ t)
    (hη : 0 ≤ η) (htη : η + 2 ≤ t) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ K : ℕ, 2 * (t - 2) * K ≤ L →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ I.card ≤ K ∧ Connected L I ∧
          (runCompatibleNullity L I : ℝ) ≤ η * L) →
        (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨NL, _hNL, hl⟩ := AllCardinalityConnected.uniform_bound
    1 u C (ε / 2) (by norm_num) hu (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := HighNullityClosure.uniform_bound
    t η u C (ε / 2) htEven ht hη htη hu (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NL + NC + NF, by omega, ?_⟩
  intro N hN L hband K hK G hG F hF
  let P := fun I : Finset ℕ ↦ (runCompatibleNullity L I : ℝ) ≤ L
  let FL := F.filter P
  let FH := F.filter fun I ↦ ¬ P I
  have hlow : (∑ I ∈ FL, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    have h := hl N (by omega) L hband G hG FL (by
      intro I hI
      obtain ⟨hIF, hrank⟩ := mem_filter.mp hI
      obtain ⟨hIG, hthree, _hsize, hconn, _hcap⟩ := hF I hIF
      exact ⟨hIG, hthree, hconn, by simpa only [one_mul] using hrank⟩)
    norm_num only [sub_self, min_self] at h
    exact h
  have hhigh : (∑ I ∈ FH, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply hc N (by omega) L hband K hK G hG FH
    intro I hI
    obtain ⟨hIF, hrank⟩ := mem_filter.mp hI
    obtain ⟨hIG, _hthree, hsize, _hconn, hcap⟩ := hF I hIF
    exact ⟨hIG, hsize, lt_of_not_ge hrank, hcap⟩
  have hsplit := sum_filter_add_sum_filter_not F P (fun I ↦ u ^ I.card * |infiniteCenteredCoefficient L I|)
  change (∑ I ∈ FL, u ^ I.card * |infiniteCenteredCoefficient L I|) +
    (∑ I ∈ FH, u ^ I.card * |infiniteCenteredCoefficient L I|) = _ at hsplit
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hlow, hhigh, hsplit, hfactor]

theorem uniform_sublog_range (K : ℕ → ℕ)
    (hK : Tendsto (fun N : ℕ ↦ (K N : ℝ) / Real.log N) atTop (nhds 0))
    (t : ℕ) (η u C ε : ℝ) (htEven : Even t) (ht : 2 ≤ t)
    (hη : 0 ≤ η) (htη : η + 2 ≤ t) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ I.card ≤ K N ∧ Connected L I ∧
          (runCompatibleNullity L I : ℝ) ≤ η * L) →
        (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := uniform_linear_range t η u C ε htEven ht hη htη hu hε
  let B : ℕ := 2 * (t - 2) + 1
  have hB : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by dsimp [B]; omega)
  obtain ⟨NK, _hNK, hk⟩ := SublogCardinalityCap.uniform_cap K hK C (1 / (B : ℝ)) (by positivity)
  refine ⟨10 + NK + NC, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hcap := hk N (by omega) L hband
  have hcap' : (K N : ℝ) ≤ (L : ℝ) / B := by simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hcap
  have hprod : K N * B ≤ L := by exact_mod_cast (le_div_iff₀ hB).mp hcap'
  have hlinear : 2 * (t - 2) * K N ≤ L := by
    have hmul := Nat.mul_le_mul_right (K N) (show 2 * (t - 2) ≤ B by dsimp [B]; omega)
    exact hmul.trans (by simpa only [Nat.mul_comm] using hprod)
  exact hc N (by omega) L hband (K N) hlinear G hG F hF

theorem companion_T16_3 (K : ℕ → ℕ)
    (hK : Tendsto (fun N : ℕ ↦ (K N : ℝ) / Real.log N) atTop (nhds 0))
    (η u C ε : ℝ) (hη : 0 ≤ η) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ I.card ≤ K N ∧ Connected L I ∧
          (runCompatibleNullity L I : ℝ) ≤ η * L) →
        (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 2 (η + 2))
  let t := 2 * (n + 1)
  have htEven : Even t := ⟨n + 1, by dsimp [t]; omega⟩
  have ht : 2 ≤ t := by dsimp [t]; omega
  have htη : η + 2 ≤ t := by
    have h := (le_max_right 2 (η + 2)).trans_lt hn
    dsimp only [t]
    push_cast
    linarith only [h, Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨N₀, hN₀, h⟩ := uniform_sublog_range
    K hK t η u C ε htEven ht hη htη hu hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG F hF
  exact (h N hN L hband G hG F hF).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only []))

end PaperP1.GrowingConnected
