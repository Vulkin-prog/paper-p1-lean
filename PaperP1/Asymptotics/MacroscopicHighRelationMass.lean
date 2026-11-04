module

public import PaperP1.Arithmetic.BoundedGeometricPairCount
public import PaperP1.Asymptotics.MacroscopicRelationPowers
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # Actual positive and signed high-channel relation sums on the macroscopic interval

The finite mask includes both coefficient orientations and every reduced
height up to B^3. Its actual host count and actual relation power are
both proved before summing. The height-three sector has power 4/3.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicHighRelationMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedPairRankLoss
  PaperP1.EnlargedPairGeometry PaperP1.MacroscopicIntervalGeometry PaperP1.CriticalBandScale

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def highPairs (M : ℕ) (δ : ℝ) (L q : ℕ) : Finset (ℕ × ℕ) :=
  ((PaperP1.BoundedGeometricPairCount.coefficients (L + 1)).filter fun ab ↦
    q ≤ max ab.1 ab.2 ∧ ab.1.Coprime ab.2).biUnion fun ab ↦
      ((starts M δ) ×ˢ (starts M δ)).filter fun xy ↦ Geometric ab.1 ab.2 xy.1 xy.2 L

def affineWeight (η : Bool) (r : ℕ) : ℝ := (if η then 1 else 0) * (2 ^ r : ℝ) - 1

theorem high_subset_covered {M L q : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) :
    highPairs M δ L q ⊆ PaperP1.BoundedGeometricPairCount.covered M L := by
  intro xy hxy
  obtain ⟨ab, hab', hpair⟩ := mem_biUnion.mp hxy
  obtain ⟨hab, _hq, _hcop⟩ := mem_filter.mp hab'
  obtain ⟨hblock, hg⟩ := mem_filter.mp hpair
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  apply mem_biUnion.mpr
  refine ⟨ab, hab, mem_filter.mpr ⟨?_, hg⟩⟩
  exact mem_product.mpr
    ⟨mem_Ico.mpr ⟨starts_pos hM hδ hx, (mem_starts_iff.mp hx).2⟩,
      mem_Ico.mpr ⟨starts_pos hM hδ hy, (mem_starts_iff.mp hy).2⟩⟩

theorem high_card_bound {M L q : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) :
    (highPairs M δ L q).card ≤ 5 * M * (L + 1) ^ 10 :=
  (card_le_card (high_subset_covered hM hδ)).trans (PaperP1.BoundedGeometricPairCount.covered_card M L)

theorem affine_weight_abs_le (η : Bool) (r : ℕ) : |affineWeight η r| ≤ (2 ^ r : ℝ) := by
  have hp : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  cases η with
  | false => simpa only [affineWeight, Bool.false_eq_true, ite_false, zero_mul, zero_sub, abs_neg, abs_one] using hp
  | true =>
    have he : affineWeight true r = (2 ^ r : ℝ) - 1 := by simp [affineWeight]
    rw [he, abs_of_nonneg (by linarith only [hp])]
    linarith

theorem uniform_power_sum (C δ : ℝ) (hδ : 0 < δ) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      (∑ xy ∈ highPairs M δ L q, (2 ^ pairLoss xy.1 xy.2 L : ℝ)) ≤ (M : ℝ) ^ (1 + 1 / (q : ℝ) + ε) := by
  obtain ⟨MR, hR⟩ := PaperP1.MacroscopicRelationPowers.uniform_height C δ hδ q hq (ε / 2) (by positivity)
  obtain ⟨MP, hP⟩ := PaperP1.LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 5 10 (ε / 2) (by positivity)
  obtain ⟨MB, hB⟩ := critical_band_scale C
  refine ⟨max MR (max MP MB), ?_⟩
  intro M hM L hcrit
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hwidth := (hB M (by omega) L hcrit).2
  have hpoint : ∀ xy ∈ highPairs M δ L q,
      (2 ^ pairLoss xy.1 xy.2 L : ℝ) ≤ (M : ℝ) ^ (1 / (q : ℝ) + ε / 2) := by
    intro xy hxy
    obtain ⟨ab, hab', hpair⟩ := mem_biUnion.mp hxy
    obtain ⟨hab, hqmax, hcop⟩ := mem_filter.mp hab'
    obtain ⟨hblock, hg⟩ := mem_filter.mp hpair
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    obtain ⟨haI, hbI⟩ := mem_product.mp hab
    obtain ⟨ha1, haB⟩ := mem_Icc.mp haI
    obtain ⟨hb1, hbB⟩ := mem_Icc.mp hbI
    exact hR M (by omega) L ab.1 ab.2 xy.1 xy.2 hcrit (by omega) (by omega)
      hcop hqmax haB hbB hx hy hg
  have hcard : ((highPairs M δ L q).card : ℝ) ≤ 5 * M * ((L + 1 : ℕ) : ℝ) ^ 10 := by
    exact_mod_cast high_card_bound (by omega : 2 ≤ M) hδ (L := L) (q := q)
  have hpoly : 5 * ((L + 1 : ℕ) : ℝ) ^ 10 ≤ (M : ℝ) ^ (ε / 2) := by
    have hp := hP M (by omega) L hwidth
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 5 * (L + 1 : ℝ) ^ 10)] at hp
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  calc
    _ ≤ ∑ _xy ∈ highPairs M δ L q, (M : ℝ) ^ (1 / (q : ℝ) + ε / 2) := sum_le_sum hpoint
    _ = (highPairs M δ L q).card * (M : ℝ) ^ (1 / (q : ℝ) + ε / 2) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (5 * M * ((L + 1 : ℕ) : ℝ) ^ 10) * (M : ℝ) ^ (1 / (q : ℝ) + ε / 2) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hm.le _)
    _ = (M : ℝ) * (5 * ((L + 1 : ℕ) : ℝ) ^ 10) * (M : ℝ) ^ (1 / (q : ℝ) + ε / 2) := by ring
    _ ≤ (M : ℝ) * (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (1 / (q : ℝ) + ε / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hm.le) (Real.rpow_nonneg hm.le _)
    _ = (M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (1 / (q : ℝ) + ε / 2) := by rw [Real.rpow_one]
    _ = (M : ℝ) ^ (1 + 1 / (q : ℝ) + ε) := by rw [← Real.rpow_add hm, ← Real.rpow_add hm]; congr 1; ring

theorem uniform_weights (C δ : ℝ) (hδ : 0 < δ) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      (∑ xy ∈ highPairs M δ L q, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)) ≤ (M : ℝ) ^ (1 + 1 / (q : ℝ) + ε) ∧
      ∀ η : ℕ × ℕ → Bool, (∑ xy ∈ highPairs M δ L q, |affineWeight (η xy) (pairLoss xy.1 xy.2 L)|) ≤
        (M : ℝ) ^ (1 + 1 / (q : ℝ) + ε) := by
  obtain ⟨M₀, h⟩ := uniform_power_sum C δ hδ q hq ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit
  have hs := h M hM L hcrit
  constructor
  · exact (sum_le_sum fun _xy _hxy ↦ sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans hs
  · intro η
    exact (sum_le_sum fun xy _hxy ↦ affine_weight_abs_le (η xy) (pairLoss xy.1 xy.2 L)).trans hs

theorem high_height_three (C δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      (∑ xy ∈ highPairs M δ L 3, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)) ≤ (M : ℝ) ^ (4 / 3 + ε) ∧
      ∀ η : ℕ × ℕ → Bool, (∑ xy ∈ highPairs M δ L 3, |affineWeight (η xy) (pairLoss xy.1 xy.2 L)|) ≤
        (M : ℝ) ^ (4 / 3 + ε) := by
  have h := uniform_weights C δ hδ 3 (by norm_num) ε hε
  simpa only [Nat.cast_ofNat, show (1 : ℝ) + 1 / (3 : ℝ) + ε = 4 / 3 + ε by ring] using h

end PaperP1.MacroscopicHighRelationMass
