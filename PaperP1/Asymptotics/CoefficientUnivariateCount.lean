module

public import PaperP1.Asymptotics.CriticalCoefficientPatterns
public import PaperP1.Asymptotics.DisjointSquareEquations
public import PaperP1.Combinatorics.FiniteCoverCount
public import PaperP1.Arithmetic.SplitRadicalPointHeight
public import PaperP1.Model.FiniteRademacher

/-! # Two disjoint one-variable equations with a common subpower coefficient list have subpower many hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoefficientUnivariateCount

open Finset PaperP1.CoefficientSplitRadicalPatterns PaperP1.CriticalCoefficientPatterns
  PaperP1.SplitRadicalPointHeight PaperP1.CriticalBandScale PaperP1.Model

def Valid (q : Pattern 2) : Prop :=
  Disjoint (q.1.1 0) (q.1.1 1) ∧ (q.1.1 0).Nonempty ∧ (q.1.1 1).Nonempty

def HasSystem (L K : ℕ) (Q : Finset ℕ) (n : ℕ) : Prop :=
  ∃ q ∈ pool 2 L K Q, Valid q ∧ ∀ i : Fin 2,
    IsSquare (coefficient q i * integerProduct (q.1.1 i) (n : ℤ))

theorem uniform_count (C ε : ℝ) (K : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ Q : Finset ℕ, (Q.card : ℝ) ≤ (N : ℝ) ^ coefficientMargin (ε / 2) 2 →
        (∀ d ∈ Q, 0 < d) → ∀ S : Finset ℕ,
          (∀ n ∈ S, n ∈ dyadicBlock N ∧ HasSystem L K Q n) → (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NF, hF⟩ := DisjointSquareEquations.two_equations 1 2 (by norm_num) K upperScale 1 (ε / 2) (by positivity)
  obtain ⟨NG, hG⟩ := critical_band_scale C
  obtain ⟨NP, _hNP, hP⟩ := CriticalCoefficientPatterns.uniform_pool C (ε / 2) 2 K (by positivity)
  refine ⟨max 1 (max NF (max NG NP)), by omega, ?_⟩
  intro N hN L hband Q hQcard hQ S hS
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let patterns := (pool 2 L K Q).filter Valid
  let hosts := fun q : Pattern 2 ↦ S.filter fun n : ℕ ↦ ∀ i : Fin 2,
    IsSquare (coefficient q i * integerProduct (q.1.1 i) (n : ℤ))
  have hcover : ∀ n ∈ S, ∃ q ∈ patterns, n ∈ hosts q := by
    intro n hn
    obtain ⟨q, hq, hvalid, hroots⟩ := (hS n hn).2
    exact ⟨q, mem_filter.mpr ⟨hq, hvalid⟩, mem_filter.mpr ⟨hn, hroots⟩⟩
  have hbound : ∀ q ∈ patterns, ((hosts q).card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    intro q hq
    obtain ⟨hqpool, hdisj, hne0, hne1⟩ := mem_filter.mp hq
    have hqdata := (mem_pool 2 L K Q q).mp hqpool
    apply hF N (by omega) (L + 1) (q.1.1 0) (q.1.1 1) (coefficient q 0) (coefficient q 1)
      (by omega) hne0 hne1 hdisj (hqdata.1 0).2 (hqdata.1 1).2
    · simpa only [Real.rpow_one] using (hG N (by omega) L hband).2
    · intro z hz
      rcases mem_union.mp hz with hz | hz
      · exact left_bound hqpool 0 z hz
      · exact left_bound hqpool 1 z hz
    · exact (coefficient_pos hQ hqpool 0).ne'
    · exact (coefficient_pos hQ hqpool 1).ne'
    · intro n hn
      obtain ⟨hnS, hnroots⟩ := mem_filter.mp hn
      obtain ⟨hnlo, hnhi⟩ := mem_Ico.mp (hS n hnS).1
      exact ⟨by simpa only [one_mul] using (show (N : ℝ) ≤ n by exact_mod_cast hnlo),
        by exact_mod_cast hnhi.le, hnroots 0, hnroots 1⟩
  have hfinite := FiniteCoverCount.cardinal_le S patterns hosts ((N : ℝ) ^ (ε / 2)) hcover hbound
  have hpatterns : (patterns.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    (show (patterns.card : ℝ) ≤ (pool 2 L K Q).card by exact_mod_cast card_filter_le _ _).trans
      (hP N (by omega) L hband Q hQcard)
  calc
    _ ≤ (patterns.card : ℝ) * (N : ℝ) ^ (ε / 2) := hfinite
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hpatterns (Real.rpow_nonneg hNr.le _)
    _ = _ := by rw [← Real.rpow_add hNr]; congr 1; ring

theorem uniform_pairs (C ε : ℝ) (K : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ Q : Finset ℕ, (Q.card : ℝ) ≤ (N : ℝ) ^ coefficientMargin (ε / 4) 2 →
        (∀ d ∈ Q, 0 < d) → ∀ F : Finset (ℕ × ℕ),
          (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
          (∀ p ∈ F, HasSystem L K Q p.1 ∧ HasSystem L K Q p.2) →
          (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, hc⟩ := uniform_count C (ε / 2) K (by positivity)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband Q hQcard hQ F hdyadic hsystems
  classical
  have hQcard' : (Q.card : ℝ) ≤ (N : ℝ) ^ coefficientMargin ((ε / 2) / 2) 2 := by
    simpa only [show (ε / 2) / 2 = ε / 4 by ring] using hQcard
  have hleft := hc N hN L hband Q hQcard' hQ (F.image Prod.fst) (by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    exact ⟨(hdyadic p hp).1, (hsystems p hp).1⟩)
  have hright := hc N hN L hband Q hQcard' hQ (F.image Prod.snd) (by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    exact ⟨(hdyadic p hp).2, (hsystems p hp).2⟩)
  have hsub : F ⊆ (F.image Prod.fst) ×ˢ (F.image Prod.snd) := by
    intro p hp
    exact mem_product.mpr ⟨mem_image.mpr ⟨p, hp, rfl⟩, mem_image.mpr ⟨p, hp, rfl⟩⟩
  have hfinite : (F.card : ℝ) ≤ ((F.image Prod.fst).card : ℝ) * (F.image Prod.snd).card := by
    have h := card_le_card hsub
    rw [card_product] at h
    exact_mod_cast h
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ _ := hfinite
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul hleft hright (Nat.cast_nonneg _) (Real.rpow_nonneg hNr.le _)
    _ = _ := by rw [← Real.rpow_add hNr]; congr 1; ring

end PaperP1.CoefficientUnivariateCount
