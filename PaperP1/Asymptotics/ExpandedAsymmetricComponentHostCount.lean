module

public import PaperP1.Asymptotics.AsymmetricComponentHostCount
public import PaperP1.Asymptotics.ExpandedSmoothGeneralHostCount
public import PaperP1.Asymptotics.ExpandedSmoothDegreeOneHostCount
public import PaperP1.Arithmetic.ExpandedAsymmetricSupportEnvelope

/-! # Actual asymmetric geometric hosts with an expanded old-centre interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExpandedAsymmetricComponentHostCount

open Finset PaperP1.Model PaperP1.AsymmetricComponentHostData PaperP1.AsymmetricComponentHostCount

theorem cast_expanded (Q : ℕ) (hQ : 1 ≤ Q) {N : ℕ} (F : Finset (ℕ × ℕ))
    (hF : ∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) :
    ∀ p ∈ F.image castPair, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧
      p.1.natAbs ≤ 2 * (Q * N) ∧ p.2.natAbs ≤ 2 * N := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
  obtain ⟨hx, hy⟩ := hF q hq
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
  obtain ⟨hylo, hyhi⟩ := mem_Ico.mp hy
  have hxhi' : q.1 < N + Q * N := hxhi
  have hNM : N ≤ Q * N := by simpa only [one_mul] using Nat.mul_le_mul_right N hQ
  change (N : ℤ) ≤ (q.1 : ℤ) ∧ (N : ℤ) ≤ (q.2 : ℤ) ∧ q.1 ≤ 2 * (Q * N) ∧ q.2 ≤ 2 * N
  exact ⟨by exact_mod_cast hxlo, by exact_mod_cast hylo, by omega, hyhi.le⟩

theorem uniform_general (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (Dold Dcut K : ℕ) (hε : 0 < ε) :
    ∃ Ds k : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k K Ds →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dold * (L + 1) →
      ∀ (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H), H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L) →
      (∀ p ∈ F, k ≤ (small p.1 p.2 L H R hnew hamb (old p.1) K).card) →
      (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨Ds, k, hDs, hk⟩ := ExpandedSmoothGeneralHostCount.uniform_hosts Q hQ C ε (10 * (Dcut + 1)) Dold K hε
  obtain ⟨Nw, hw⟩ := EnlargedOffsetRegime.uniform_widths C Dold
  refine ⟨Ds, k, hDs, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hc⟩ := hk hCover hPila
  refine ⟨A, hA, max Nc Nw, ?_⟩
  intro N hN L H R hcrit hR hnew hamb hH old hold F hF hnon hcomponents
  classical
  have hRN : R < N := (hw N (by omega) L R hcrit hR).2.2
  have hW : R - 1 + 1 = R := by omega
  have hnon' : ∀ p ∈ F.image castPair, ¬CompressedTargetAlignment.Aligned Dold p.1.natAbs p.2.natAbs L := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact hnon q hq
  have hsystems : ∀ p ∈ F.image castPair,
      ∃ q ∈ GeneralSplitRadicalPatternPool.pool k (R - 1) (10 * (H + 1)) K,
      SmoothGeneralNonalignedHostCount.Valid K q ∧ ∃ w : Fin k → ℤ, ∀ i,
      w i ^ 2 = GeneralSplitRadicalPatternPool.coefficient q i *
        SplitRadicalPointHeight.integerProduct (q.1.1 i) p.1 * SplitRadicalPointHeight.integerProduct (q.1.2 i) p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    obtain ⟨hx, hy⟩ := hF q hq
    exact AsymmetricComponentHostData.exists_general
      (hRN.trans_le (mem_Ico.mp hx).1) (hRN.trans_le (mem_Ico.mp hy).1)
      hnew hamb (old q.1) (hold q.1 hx) k K (hcomponents q hq)
  have hbound := hc N (by omega) L (R - 1) (10 * (H + 1)) hcrit
    (by simpa only [hW] using hR) (cutoff_budget hH)
    (F.image castPair) (fun p hp ↦ by
      obtain ⟨hxlo, hylo, hxhi, hyhi⟩ := cast_expanded Q hQ F hF p hp
      have hNM : N ≤ Q * N := by simpa only [one_mul] using Nat.mul_le_mul_right N hQ
      exact ⟨hxlo, hylo, hxhi, hyhi.trans (Nat.mul_le_mul_left 2 hNM)⟩) hnon' hsystems
  simpa only [card_image_of_injective _ castPair_injective] using hbound

theorem uniform_linear (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (Dold Dcut K : ℕ) (hε : 0 < ε) :
    ∃ k : ℕ, UniformOrdinarySurfaceCover.UniformCover k K →
      (∀ M, UniformAffineCurvePointCount.UniformBound k M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dold * (L + 1) →
      ∀ (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H), H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      ∀ a : ℕ, 0 < a → a + 1 ≤ K →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, a = 1 → ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L) →
      (∀ p ∈ F, k ≤ (typed p.1 p.2 L H R hnew hamb (old p.1) a).card) →
      (F.card : ℝ) ≤ A * (N : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := ExpandedSmoothDegreeOneHostCount.uniform_hosts Q hQ C ε (10 * (Dcut + 1)) Dold K hε
  obtain ⟨Nw, hw⟩ := EnlargedOffsetRegime.uniform_widths C Dold
  refine ⟨k, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hc⟩ := hk hCover hPila
  refine ⟨A, hA, max Nc Nw, ?_⟩
  intro N hN L H R hcrit hR hnew hamb hH old hold a ha hK F hF hnon hcomponents
  classical
  have hRN : R < N := (hw N (by omega) L R hcrit hR).2.2
  have hW : R - 1 + 1 = R := by omega
  have hnon' : ∀ p ∈ F.image castPair, a = 1 → ¬CompressedTargetAlignment.Aligned Dold p.1.natAbs p.2.natAbs L := by
    intro p hp ha1
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact hnon q hq ha1
  have hsystems : ∀ p ∈ F.image castPair,
      ∃ q ∈ SplitRadicalPatternPool.pool k (R - 1) (10 * (H + 1)) K,
      SmoothDegreeOneHostCount.Valid a K q ∧ ∃ w : Fin k → ℤ, ∀ i,
      w i ^ 2 = SplitRadicalPatternPool.coefficient q i *
        SplitRadicalPointHeight.integerProduct (q.1.1 i) p.1 * (p.2 + q.1.2 i) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    obtain ⟨hx, hy⟩ := hF q hq
    exact AsymmetricComponentHostData.exists_linear
      (hRN.trans_le (mem_Ico.mp hx).1) (hRN.trans_le (mem_Ico.mp hy).1)
      hnew hamb (old q.1) (hold q.1 hx) k a K hK (hcomponents q hq)
  have hbound := hc N (by omega) L (R - 1) (10 * (H + 1)) hcrit
    (by simpa only [hW] using hR) (cutoff_budget hH) a ha
    (F.image castPair) (cast_expanded Q hQ F hF) hnon' hsystems
  simpa only [card_image_of_injective _ castPair_injective] using hbound
theorem uniform_dense (Q : ℕ) (hQ : 1 ≤ Q) (C ε η : ℝ) (Dold Dcut : ℕ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Ds k : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (sizeCap Dcut η) Ds →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dold * (L + 1) →
      ∀ (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H), H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ (nontrivial p.1 p.2 L H R hnew hamb (old p.1)).card) →
      (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨Ds, k, hDs, hk⟩ := uniform_general Q hQ C ε Dold Dcut (sizeCap Dcut η) hε
  obtain ⟨Ns, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨Nl, hl⟩ := ElementaryLogGrowth.log_ge_eventually
    (2 * (k : ℝ) / (η * CriticalBandScale.lowerScale))
  refine ⟨Ds, k, hDs, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hc⟩ := hk hCover hPila
  refine ⟨A, hA, max Nc (max Ns Nl), ?_⟩
  intro N hN L H R hcrit hR hnew hamb hH old hold F hF hnon hdense
  have hscale := (hs N (by omega) L hcrit).1
  have hlog := (div_le_iff₀ (mul_pos hη CriticalBandScale.lowerScale_pos)).mp (hl N (by omega)).1
  have hscaled := mul_le_mul_of_nonneg_left hscale hη.le
  have hlarge : (k : ℝ) ≤ (η / 2) * ((L + 1 : ℕ) : ℝ) := by nlinarith only [hlog, hscaled]
  apply hc N (by omega) L H R hcrit hR hnew hamb hH old hold F hF hnon
  intro p hp
  have hh := hlarge.trans (small_density Dcut η hη hnew hamb (old p.1) hH (hdense p hp))
  exact_mod_cast hh

end PaperP1.ExpandedAsymmetricComponentHostCount
