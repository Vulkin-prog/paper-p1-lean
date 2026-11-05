module

public import PaperP1.Asymptotics.SubsetDenseNonalignedHosts
public import PaperP1.Asymptotics.SubsetKernelPowers

/-! # The full nonaligned two-subset interaction bound has no geometric counting input

Sparse components use the actual product weight. All dense hosts have a
subpower count by the pinned-support confinement theorem.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetInteractionMass

open Finset PaperP1.Model PaperP1.SubsetEvenLoss PaperP1.SubsetComponentHostData

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_bound (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (Dwidth Dcut : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dwidth * (L + 1) →
      1 ≤ R → 2 * R ≤ H → H ≤ Dcut * (L + 1) → ∀ old new : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      (∀ y ∈ dyadicBlock N, ∀ n ∈ new y, |(n : ℤ) - y| ≤ (R : ℤ)) →
      (∀ y ∈ dyadicBlock N, (new y).card ≤ 2 * (L + 1)) →
      ∀ F : Finset (ℕ × ℕ),
      (∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dwidth p.1 p.2 L) →
      (F.card : ℝ) ≤ (N : ℝ) ^ (1 + ε / 8) → ∀ w : ℕ × ℕ → ℝ,
      (∀ p ∈ F, w p ≤ (N : ℝ) ^ (-5 / 3 + ε / 8)) →
      (∀ p ∈ F, w p ≤ (N : ℝ) ^ (-10 / 3 + ε / 8) * (2 ^ loss H (old p.1) (new p.2) : ℝ)) →
      (∑ p ∈ F, w p) ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ND, _hND, hd⟩ := SubsetDenseNonalignedHosts.uniform_dense Q hQ C δ (1 / 12)
    Dwidth Dcut hδ (by norm_num)
  obtain ⟨NS, hs⟩ := SubsetKernelPowers.few_components Q C (1 / 12) δ
    Dwidth Dcut (by norm_num) hδ
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-5 / 3 + 3 * δ)
    (ε - 3 * δ) (by dsimp [δ]; linarith only [hε])
  refine ⟨3 + ND + NS + NF, by omega, ?_⟩
  intro N hN L H R hband hR hRpos hamb hH old new hold hnew _hcardNew F hF hnon hcard w hSingle hProduct
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := F.filter fun p ↦ ((nontrivial p.1 p.2 H R (old p.1) (new p.2)).card : ℝ) ≤
    (1 / 12) * ((L + 1 : ℕ) : ℝ)
  let D := F \ P
  have hPF : P ⊆ F := filter_subset _ _
  have hDF : D ⊆ F := sdiff_subset
  have hPpoint (p : ℕ × ℕ) (hp : p ∈ P) : w p ≤ (N : ℝ) ^ (-13 / 4 + 2 * δ) := by
    obtain ⟨hx, hy⟩ := hF p (hPF hp)
    have hkernel := hs N (by omega) L H R hband hR hamb hH p.1 hx p.2 hy
      (old p.1) (new p.2) (hold p.1 hx) (hnew p.2 hy) (mem_filter.mp hp).2
    have hh := (hProduct p (hPF hp)).trans
      (mul_le_mul_of_nonneg_left hkernel (by positivity : 0 ≤ (N : ℝ) ^ (-10 / 3 + δ)))
    rw [← Real.rpow_add hn] at hh
    convert hh using 1
    congr 1
    ring
  have hPsum : (∑ p ∈ P, w p) ≤ (N : ℝ) ^ (-5 / 3 + 3 * δ) := by
    calc
      _ ≤ ∑ _p ∈ P, (N : ℝ) ^ (-13 / 4 + 2 * δ) := sum_le_sum (fun p hp ↦ hPpoint p hp)
      _ = (P.card : ℝ) * (N : ℝ) ^ (-13 / 4 + 2 * δ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ (1 + δ) * (N : ℝ) ^ (-13 / 4 + 2 * δ) :=
        mul_le_mul_of_nonneg_right
          ((show (P.card : ℝ) ≤ F.card by exact_mod_cast card_le_card hPF).trans hcard) (by positivity)
      _ = (N : ℝ) ^ (-9 / 4 + 3 * δ) := by rw [← Real.rpow_add hn]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])
  have hDcard : (D.card : ℝ) ≤ (N : ℝ) ^ δ := by
    apply hd N (by omega) L H R hband hR hRpos hH old new hold hnew D
      (fun p hp ↦ hF p (hDF hp)) (fun p hp ↦ hnon p (hDF hp))
    intro p hp
    have hh : ¬((nontrivial p.1 p.2 H R (old p.1) (new p.2)).card : ℝ) ≤
        (1 / 12) * ((L + 1 : ℕ) : ℝ) := fun hc ↦
      (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨hDF hp, hc⟩)
    exact (not_le.mp hh).le
  have hDsum : (∑ p ∈ D, w p) ≤ (N : ℝ) ^ (-5 / 3 + 3 * δ) := by
    calc
      _ ≤ ∑ _p ∈ D, (N : ℝ) ^ (-5 / 3 + δ) := sum_le_sum (fun p hp ↦ hSingle p (hDF hp))
      _ = (D.card : ℝ) * (N : ℝ) ^ (-5 / 3 + δ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ δ * (N : ℝ) ^ (-5 / 3 + δ) := mul_le_mul_of_nonneg_right hDcard (by positivity)
      _ = (N : ℝ) ^ (-5 / 3 + 2 * δ) := by rw [← Real.rpow_add hn]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ])
  have hpart := sum_sdiff (f := w) hPF
  change (∑ p ∈ D, w p) + (∑ p ∈ P, w p) = _ at hpart
  have hsum : (∑ p ∈ F, w p) ≤ 2 * (N : ℝ) ^ (-5 / 3 + 3 * δ) := by
    linarith only [hpart, hPsum, hDsum]
  exact hsum.trans (by
    simpa only [show (-5 / 3 + 3 * δ) + (ε - 3 * δ) = -5 / 3 + ε by ring] using hf N (by omega))

end PaperP1.SubsetInteractionMass
