module

public import PaperP1.Asymptotics.StrongAlignedDensePairCount
public import PaperP1.Model.TwoTargetJointWeight
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # Strongly aligned dense minimal pair crossings cost N⁻¹ above their actual source joint mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongAlignedDenseJointMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.TwoTargetPrimitiveData PaperP1.FiniteFamilyEnumeration

theorem uniform_joint (s : ℕ) (θ C η ε : ℝ) (hθ : 0 < θ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e : Finset ℕ, e.card = s → e ⊆ dyadicBlock N → ∀ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧ p.1 ≠ p.2 ∧ p.1 ∉ e ∧ p.2 ∉ e ∧
        CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∧
        θ * L < (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ∧
        η * L ≤ (Module.finrank F₂ ↥(sourceSpace e L ⊓ span (fun x ↦ squareClassSpace x L) {p.1, p.2}) : ℝ)) →
      (∀ p ∈ P, ∀ B : Finset ℕ, B ⊂ {p.1, p.2} →
        Disjoint (sourceSpace e L) (span (fun x ↦ squareClassSpace x L) B)) →
      (∑ p ∈ P, infiniteJointMoment L (TwoTargetFamilyCover.family e p)) ≤
        infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε) := by
  let M := 2 * (2 : ℝ) ^ C
  obtain ⟨NC, _hNC, hc⟩ := StrongAlignedDensePairCount.uniform_count s θ C η (ε / 2) hθ hη (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption M (-1 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NC + NM + NF + NG, by omega, ?_⟩
  intro N hN L hband e hecard heG P hP hproper
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount := hc N (by omega) L hband (centres e hecard) (centres_mem _ e hecard heG)
    (sourceSpace e L) (source_enumeration e L hecard).le P (by
      intro p hp
      obtain ⟨hy, hz, _hneq, _hyE, _hzE, halign, hstrong, hdense⟩ := hP p hp
      rw [RetainedNullity.span_pair] at hdense
      exact ⟨hy, hz, halign, hstrong, hdense⟩)
  have hpoint (p : ℕ × ℕ) (hp : p ∈ P) :
      infiniteJointMoment L (TwoTargetFamilyCover.family e p) ≤ infiniteJointMoment L e * (M / N) := by
    obtain ⟨hy, _hz, hneq, hyE, _hzE, _halign, _hstrong, _hdense⟩ := hP p hp
    have hcard : ({p.1, p.2} : Finset ℕ).card = 2 := card_pair hneq
    have hcuts := MinimalSpanCrossing.disjoint_singletons (fun x ↦ squareClassSpace x L)
      (sourceSpace e L) {p.1, p.2} (by omega) (hproper p hp)
    exact (TwoTargetJointWeight.one_target_bound L hL e p.1 p.2 hyE
      (hcuts p.1 (mem_insert_self _ _))).trans
        (mul_le_mul_of_nonneg_left (hm N (by omega) L hband p.1 hy) (infiniteJointMoment_nonneg L e))
  have hfactor : M * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  calc
    _ ≤ ∑ _p ∈ P, infiniteJointMoment L e * (M / N) := sum_le_sum hpoint
    _ = (P.card : ℝ) * (infiniteJointMoment L e * (M / N)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (infiniteJointMoment L e * (M / N)) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg (infiniteJointMoment_nonneg L e) (by dsimp [M]; positivity))
    _ = infiniteJointMoment L e * (M * (N : ℝ) ^ (-1 + ε / 2)) := by
      rw [show -1 + ε / 2 = ε / 2 - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfactor (infiniteJointMoment_nonneg L e)

end PaperP1.StrongAlignedDenseJointMass
