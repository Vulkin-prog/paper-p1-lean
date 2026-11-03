module

public import PaperP1.Model.GoodApartPairProducts
public import PaperP1.Asymptotics.CompressedPairIntersectionCount
public import PaperP1.Asymptotics.GoodPairSeedTail

/-! # The actual good-good apart product cost has the stronger rate seven thirds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GoodApartPairProductMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteAlignedChannelCover PaperP1.GoodApartPairProducts

theorem uniform_count (Q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℕ,
      ((families Q N H L).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  classical
  let U := (channels Q) ×ˢ (channels Q)
  have hper (t : U) : ∃ NT : ℕ, 2 ≤ NT ∧ ∀ N ≥ NT, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((CompressedPairIntersectionHosts.allPairs N t.val.1.1 t.val.1.2 t.val.2.1 t.val.2.2 L).card : ℝ) ≤
        (N : ℝ) ^ (1 + ε / 2) := by
    obtain ⟨hab, hcd⟩ := mem_product.mp t.property
    have habd := channel_data hab
    have hcdd := channel_data hcd
    exact CompressedPairIntersectionCount.uniform_count _ _ _ _ habd.1 habd.2.1.le
      hcdd.1 hcdd.2.1.le C (ε / 2) (by positivity)
  choose T hT₀ hT using hper
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (U.card : ℝ) (1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max (univ.sup T) NF), by omega, ?_⟩
  intro N hN L hband H
  have hbound (t : U) := hT t N ((le_sup (f := T) (mem_univ t)).trans (by omega)) L hband
  calc
    _ ≤ ∑ t ∈ U, ((CompressedPairIntersectionHosts.allPairs N t.1.1 t.1.2 t.2.1 t.2.2 L).card : ℝ) := by
      exact_mod_cast finite_count Q N H L
    _ ≤ ∑ _t ∈ U, (N : ℝ) ^ (1 + ε / 2) :=
      sum_le_sum fun t ht ↦ hbound ⟨t, ht⟩
    _ = (U.card : ℝ) * (N : ℝ) ^ (1 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ ((1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_coefficient (Q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e ∈ FiniteGoodChannelPartition.good Q N (2 * Q * (L + 1)) L,
      |infiniteCenteredCoefficient L e| ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let K : ℝ := (2 : ℝ) ^ ((C + 1) / 3) * M ^ 2
  obtain ⟨NR, _hNR, hr⟩ := GoodPairSeedTail.uniform_ratio Q C 1 (by norm_num)
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K (-5 / 3) ε hε
  refine ⟨max 2 (max NR (max NM NF)), by omega, ?_⟩
  intro N hN L hband e he
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hE := (mem_filter.mp (FiniteGoodChannelPartition.good_subset Q N (2 * Q * (L + 1)) L he)).1
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hE
  have hprod : (∏ x ∈ e, infiniteMarginal x L) ≤ (M / N) ^ 2 := by
    have h := prod_le_prod₀ (fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      (fun x hx ↦ hm N (by omega) L hband x (hsub hx))
    simpa only [prod_const, hcard] using h
  have hratio := hr N (by omega) L hband e he
  simp only [one_pow, div_one, one_mul] at hratio
  calc
    _ ≤ ((2 : ℝ) ^ ((C + 1) / 3) * (N : ℝ) ^ (1 / 3 : ℝ)) *
        ∏ x ∈ e, infiniteMarginal x L := hratio
    _ ≤ ((2 : ℝ) ^ ((C + 1) / 3) * (N : ℝ) ^ (1 / 3 : ℝ)) * (M / N) ^ 2 :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = K * (N : ℝ) ^ (-5 / 3 : ℝ) := by
      rw [show (-5 / 3 : ℝ) = (1 / 3 : ℝ) - 2 by norm_num, Real.rpow_sub hn,
        Real.rpow_ofNat, div_pow]
      dsimp [K]
      ring
    _ ≤ _ := hf N (by omega)

theorem uniform_mass (Q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass Q N (2 * Q * (L + 1)) L ≤ (N : ℝ) ^ (-7 / 3 + ε) := by
  classical
  obtain ⟨NC, _hNC, hc⟩ := uniform_count Q C (ε / 3) (by positivity)
  obtain ⟨NW, _hNW, hw⟩ := uniform_coefficient Q C (ε / 3) (by positivity)
  refine ⟨max 2 (max NC NW), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hweights (S : Finset (Finset ℕ)) (hS : S ∈ families Q N (2 * Q * (L + 1)) L) :
      (∏ e ∈ S, |infiniteCenteredCoefficient L e|) ≤ ((N : ℝ) ^ (-5 / 3 + ε / 3)) ^ 2 := by
    obtain ⟨hapart, hgood⟩ := mem_filter.mp hS
    have hcard := (mem_powersetCard.mp (mem_filter.mp hapart).1).2
    have h := prod_le_prod₀ (fun e _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))
      (fun e he ↦ hw N (by omega) L hband e (hgood he))
    simpa only [prod_const, hcard] using h
  calc
    _ ≤ ∑ _S ∈ families Q N (2 * Q * (L + 1)) L, ((N : ℝ) ^ (-5 / 3 + ε / 3)) ^ 2 :=
      sum_le_sum hweights
    _ = ((families Q N (2 * Q * (L + 1)) L).card : ℝ) *
        ((N : ℝ) ^ (-5 / 3 + ε / 3)) ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 + ε / 3) * ((N : ℝ) ^ (-5 / 3 + ε / 3)) ^ 2 :=
      mul_le_mul_of_nonneg_right (hc N (by omega) L hband _) (sq_nonneg _)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_add hn]
      congr 1
      ring

end PaperP1.GoodApartPairProductMass
