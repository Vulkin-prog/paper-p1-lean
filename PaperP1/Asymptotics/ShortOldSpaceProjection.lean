module

public import PaperP1.Arithmetic.ShortProjectedLists
public import PaperP1.Asymptotics.FixedProjectedMotifs
public import PaperP1.Asymptotics.CriticalBandScale

/-! # Uniform counts of all short projected lists, including motif enumeration -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortOldSpaceProjection

open Finset PaperP1.Arithmetic PaperP1.ShortProjectedLists PaperP1.ShortMotifBudget
open PaperP1.FiniteCoverCount PaperP1.SplitOffsetProducts

theorem uniform_projected_lists {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ a b : ℝ, 0 < a → ∀ D A₀ : ℝ,
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ O G : Finset ℕ,
        0 < W → (W : ℝ) ≤ D * (Real.log N) ^ A₀ → (O.card : ℝ) ≤ E * Real.log N →
        (∀ n ∈ G, a * N ≤ n ∧ (n : ℝ) ≤ b * N) →
        ((lists (ι := ι) O G N W c).card : ℝ) ≤ (N : ℝ) ^ (Fintype.card ι / 2 + ε) := by
  classical
  let r := Fintype.card ι
  obtain ⟨c, hc, hfixed⟩ := PaperP1.FixedProjectedMotifs.fixed_motif_count (ι := ι) E (ε / 2) (by positivity)
  let η := ε / (2 * (r + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨c, hc, ?_⟩
  intro a b ha D A₀
  obtain ⟨Nf, hNf⟩ := hfixed a b ha D A₀
  obtain ⟨Nm, hNm⟩ := card_budget c D A₀ η hc.le hη
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.mp
    (PaperP1.ModerateOrder.loglog_tendsto_atTop.eventually (Filter.eventually_ge_atTop 0))
  refine ⟨max 2 (max Nf (max Nm Nl)), ?_⟩
  intro N hN W O G hW hwidth hO hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have harg : 0 ≤ c * Real.log (Real.log N) := mul_nonneg hc.le (hNl N (by omega))
  have hηeq : η * (2 * (r + 1)) = ε := by dsimp [η]; field_simp
  have hηr : η * r ≤ ε / 2 := by nlinarith only [hηeq, hη]
  have hcodes : ((codes (ι := ι) N W c).card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    have hm := hNm N (by omega) W hW hwidth
    calc
      _ ≤ ((motifs N W c).card : ℝ) ^ r := by exact_mod_cast codes_card_le (ι := ι) N W c
      _ ≤ ((N : ℝ) ^ η) ^ r := pow_le_pow_left₀ (by positivity) hm r
      _ = (N : ℝ) ^ (η * r) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hηr
  have hfibres : ∀ A ∈ codes (ι := ι) N W c, ((fibre O G A).card : ℝ) ≤ (N : ℝ) ^ (r / 2 + ε / 2) := by
    intro A hA
    rw [fibre_card_eq]
    exact hNf N (by omega) W O A (fun _ ↦ G) hW hwidth hO (code_data N W c harg A hA) (fun _ ↦ hG)
  have hcount := cardinal_le (lists (ι := ι) O G N W c) (codes N W c) (fibre O G)
    ((N : ℝ) ^ (r / 2 + ε / 2)) (lists_cover O G N W c) hfibres
  calc
    _ ≤ ((codes (ι := ι) N W c).card : ℝ) * (N : ℝ) ^ (r / 2 + ε / 2) := hcount
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (r / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right hcodes (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; dsimp [r]; ring

theorem block_union_card {κ : Type*} [Fintype κ] (B : ℕ) (D : ℝ)
    (blocks : κ → Finset ℕ) (hblocks : ∀ i, ((blocks i).card : ℝ) ≤ D * B) :
    (((univ : Finset κ).biUnion blocks).card : ℝ) ≤ Fintype.card κ * D * B := by
  classical
  calc
    _ ≤ ((∑ i : κ, (blocks i).card : ℕ) : ℝ) := by exact_mod_cast (card_biUnion_le : ((univ : Finset κ).biUnion blocks).card ≤ _)
    _ = ∑ i : κ, ((blocks i).card : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ _i : κ, D * B := sum_le_sum fun i _ ↦ hblocks i
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring

theorem article_9_2 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (Dold ε : ℝ) (hDold : 0 ≤ Dold) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ a b : ℝ, 0 < a → ∀ D C : ℝ, 0 ≤ D →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W : ℕ, ∀ blocks : κ → Finset ℕ, ∀ G : Finset ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 0 < W → (W : ℝ) ≤ D * (L + 1 : ℕ) →
        (∀ i, ((blocks i).card : ℝ) ≤ Dold * (L + 1 : ℕ)) →
        (∀ n ∈ G, a * N ≤ n ∧ (n : ℝ) ≤ b * N) →
        ∀ T : Finset (ι → ℕ),
        (∀ n ∈ T, (∀ i, n i ∈ G) ∧ ∃ A : ι → Finset ℤ,
          (∀ i, Even (A i).card ∧ (A i).Nonempty ∧
            ((A i).card : ℝ) ≤ c * Real.log (Real.log N) ∧ ∀ x ∈ A i, x.natAbs ≤ W) ∧
          (∑ i, parityVec (product (A i) (n i))) ∈ PaperP1.OldSpaceProjection.oldSpace ((univ : Finset κ).biUnion blocks)) →
        (∀ n ∈ G, ∀ A : Finset ℤ, (∀ x ∈ A, x.natAbs ≤ W) →
          0 < product A n ∧ (product A n : ℤ) = ∏ x ∈ A, ((n : ℤ) + x) ∧ 0 < ∏ x ∈ A, ((n : ℤ) + x)) ∧
        (T.card : ℝ) ≤
          (N : ℝ) ^ (Fintype.card ι / 2 + ε) := by
  classical
  let E := (Fintype.card κ : ℝ) * Dold * PaperP1.CriticalBandScale.upperScale
  obtain ⟨c, hc, hcount⟩ := uniform_projected_lists (ι := ι) E ε hε
  refine ⟨c, hc, ?_⟩
  intro a b ha D C hD
  obtain ⟨Nc, hNc⟩ := hcount a b ha (D * PaperP1.CriticalBandScale.upperScale) 1
  obtain ⟨Nb, hNb⟩ := PaperP1.CriticalBandScale.critical_band_scale C
  obtain ⟨K, hK, hcomp⟩ := PaperP1.ComparableLogBounds.exists_nat_comparison a b ha
  obtain ⟨Nv, hNv⟩ := PaperP1.ComparableSplitProductCount.source_product_values K
    (D * PaperP1.CriticalBandScale.upperScale) 1
  refine ⟨max Nc (max Nb Nv), ?_⟩
  intro N hN L W blocks G hband hW hwidth hblocks hG T hT
  have hB := (hNb N (by omega) L hband).2
  have hwidthlog : (W : ℝ) ≤ (D * PaperP1.CriticalBandScale.upperScale) * (Real.log N) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    exact hwidth.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hB hD)
  have hO : (((univ : Finset κ).biUnion blocks).card : ℝ) ≤ E * Real.log N := by
    have hcard := block_union_card (L + 1) Dold blocks hblocks
    have hmul := mul_le_mul_of_nonneg_left hB (mul_nonneg (Nat.cast_nonneg (Fintype.card κ)) hDold)
    exact hcard.trans (by simpa only [E, mul_assoc] using hmul)
  have hsub : T ⊆ lists ((univ : Finset κ).biUnion blocks) G N W c := by
    intro n hnT
    obtain ⟨hnG, A, hA, hproj⟩ := hT n hnT
    exact mem_lists_of_even_nonempty _ G N W c n hnG A hA hproj
  have hcardT : (T.card : ℝ) ≤ ((lists (ι := ι) ((univ : Finset κ).biUnion blocks) G N W c).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  refine ⟨?_, hcardT.trans (hNc N (by omega) W _ G hW hwidthlog hO hG)⟩
  intro n hnG A hA
  exact hNv N (by omega) n W A (hcomp N n (hG n hnG).1 (hG n hnG).2).1 hwidthlog hA

end PaperP1.ShortOldSpaceProjection
