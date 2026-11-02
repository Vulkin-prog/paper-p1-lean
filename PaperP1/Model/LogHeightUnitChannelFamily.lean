module

public import PaperP1.Arithmetic.FixedChannelSourceGeometry
public import PaperP1.Combinatorics.GraphStarWeights
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # A literal union of all reduced exact-unit channels of logarithmic height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogHeightUnitChannelFamily

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.FixedChannelSourceGeometry

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def channels (L b₀ : ℕ) : Finset (ℕ × ℕ) :=
  ((range ((L + 1) ^ 3 + 1)) ×ˢ (range ((L + 1) ^ 3 + 1))).filter fun ab ↦
    0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.1.Coprime ab.2 ∧ b₀ ≤ ab.2

def families (N L b₀ : ℕ) : Finset (Finset ℕ) :=
  (channels L b₀).biUnion fun ab ↦ (unitSources N ab.1 ab.2 L).image fun xy ↦ {xy.1, xy.2}

theorem channel_data {L b₀ : ℕ} {ab : ℕ × ℕ} (hab : ab ∈ channels L b₀) :
    0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.1.Coprime ab.2 ∧ b₀ ≤ ab.2 ∧ ab.2 ≤ (L + 1) ^ 3 := by
  obtain ⟨hmem, ha, hablt, hcop, hb⟩ := mem_filter.mp hab
  have hheight := mem_range.mp (mem_product.mp hmem).2
  exact ⟨ha, hablt, hcop, hb, by omega⟩

theorem channel_card_bound (L b₀ : ℕ) :
    ((channels L b₀).card : ℝ) ≤ 4 * ((L + 1 : ℕ) : ℝ) ^ 6 := by
  have hc : (channels L b₀).card ≤ ((L + 1) ^ 3 + 1) ^ 2 := by
    have h := card_filter_le
      ((range ((L + 1) ^ 3 + 1)) ×ˢ (range ((L + 1) ^ 3 + 1)))
      (fun ab : ℕ × ℕ ↦ 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.1.Coprime ab.2 ∧ b₀ ≤ ab.2)
    simpa only [channels, card_product, card_range, pow_two] using h
  have hB : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ 3 :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ L + 1 by omega))
  have hcR : ((channels L b₀).card : ℝ) ≤ (((L + 1 : ℕ) : ℝ) ^ 3 + 1) ^ 2 := by exact_mod_cast hc
  calc
    _ ≤ (((L + 1 : ℕ) : ℝ) ^ 3 + 1) ^ 2 := hcR
    _ ≤ (2 * ((L + 1 : ℕ) : ℝ) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hB]) 2
    _ = _ := by ring

theorem weighted_bound {N L b₀ : ℕ} (hN : 0 < N) (w : Finset ℕ → ℝ) (hw : ∀ e, 0 ≤ w e)
    (K : ℝ) (hK : 0 ≤ K)
    (hcap : ∀ ab ∈ channels L b₀, ∀ xy ∈ unitSources N ab.1 ab.2 L, w {xy.1, xy.2} ≤ K) :
    (∑ e ∈ families N L b₀, w e) ≤ 4 * ((L + 1 : ℕ) : ℝ) ^ 8 * N * K := by
  let A : ℕ × ℕ → Finset (Finset ℕ) := fun ab ↦ (unitSources N ab.1 ab.2 L).image (fun xy ↦ {xy.1, xy.2})
  change (∑ e ∈ (channels L b₀).biUnion A, w e) ≤ _
  calc
    _ ≤ ∑ ab ∈ channels L b₀, ∑ e ∈ A ab, w e :=
      GraphStarWeights.sum_biUnion_le_nonneg (channels L b₀) A w hw
    _ ≤ ∑ ab ∈ channels L b₀, ∑ xy ∈ unitSources N ab.1 ab.2 L, w {xy.1, xy.2} := by
      apply sum_le_sum
      intro ab _
      dsimp only [A]
      exact sum_image_le_of_nonneg (f := w) (fun e _ ↦ hw e)
    _ ≤ ∑ ab ∈ channels L b₀, ((L + 1 : ℕ) : ℝ) ^ 2 * N * K := by
      apply sum_le_sum
      intro ab hab
      calc
        _ ≤ ∑ _xy ∈ unitSources N ab.1 ab.2 L, K := sum_le_sum fun xy hxy ↦ hcap ab hab xy hxy
        _ = ((unitSources N ab.1 ab.2 L).card : ℝ) * K := by rw [sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast unit_sources_card hN (channel_data hab).1) hK
    _ = ((channels L b₀).card : ℝ) * (((L + 1 : ℕ) : ℝ) ^ 2 * N * K) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (4 * ((L + 1 : ℕ) : ℝ) ^ 6) * (((L + 1 : ℕ) : ℝ) ^ 2 * N * K) :=
      mul_le_mul_of_nonneg_right (channel_card_bound L b₀) (by positivity)
    _ = _ := by ring

end PaperP1.LogHeightUnitChannelFamily
