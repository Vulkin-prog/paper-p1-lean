module

public import PaperP1.Asymptotics.SubsetComponentHostData
public import PaperP1.Asymptotics.ExpandedAsymmetricComponentHostCount

/-! # Existing geometric counts apply to two actual finite subsets

Both prescribed sets vary after one common threshold. Actual components
construct the complete root systems required by the geometric counts.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetComponentHostCount

open Finset PaperP1.Model PaperP1.SubsetComponentHostData PaperP1.AsymmetricComponentHostCount

theorem uniform_general (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (Dold Dcut K : ℕ) (hε : 0 < ε) :
    ∃ Ds k : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k K Ds →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dold * (L + 1) →
      1 ≤ R → H ≤ Dcut * (L + 1) →
      ∀ old new : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      (∀ y ∈ dyadicBlock N, ∀ n ∈ new y, |(n : ℤ) - y| ≤ (R : ℤ)) →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L) →
      (∀ p ∈ F, k ≤ (small p.1 p.2 H R (old p.1) (new p.2) K).card) →
      (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨Ds, k, hDs, hk⟩ := ExpandedSmoothGeneralHostCount.uniform_hosts Q hQ C ε (10 * (Dcut + 1)) Dold K hε
  obtain ⟨Nw, hw⟩ := EnlargedOffsetRegime.uniform_widths C Dold
  refine ⟨Ds, k, hDs, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hc⟩ := hk hCover hPila
  refine ⟨A, hA, max Nc Nw, ?_⟩
  intro N hN L H R hcrit hR hRpos hH old new hold hnew F hF hnon hcomponents
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
    exact SubsetComponentHostData.exists_general
      (hRN.trans_le (mem_Ico.mp hx).1) (hRN.trans_le (mem_Ico.mp hy).1)
      hRpos (old q.1) (new q.2) (hold q.1 hx) (hnew q.2 hy) k K (hcomponents q hq)
  have hbound := hc N (by omega) L (R - 1) (10 * (H + 1)) hcrit
    (by simpa only [hW] using hR) (cutoff_budget hH)
    (F.image castPair) (fun p hp ↦ by
      obtain ⟨hxlo, hylo, hxhi, hyhi⟩ := ExpandedAsymmetricComponentHostCount.cast_expanded Q hQ F hF p hp
      have hNM : N ≤ Q * N := by simpa only [one_mul] using Nat.mul_le_mul_right N hQ
      exact ⟨hxlo, hylo, hxhi, hyhi.trans (Nat.mul_le_mul_left 2 hNM)⟩) hnon' hsystems
  simpa only [card_image_of_injective _ castPair_injective] using hbound

theorem uniform_linear (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (Dold Dcut K : ℕ) (hε : 0 < ε) :
    ∃ k : ℕ, UniformOrdinarySurfaceCover.UniformCover k K →
      (∀ M, UniformAffineCurvePointCount.UniformBound k M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dold * (L + 1) →
      1 ≤ R → H ≤ Dcut * (L + 1) →
      ∀ old new : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      (∀ y ∈ dyadicBlock N, ∀ n ∈ new y, |(n : ℤ) - y| ≤ (R : ℤ)) →
      ∀ a : ℕ, 0 < a → a + 1 ≤ K →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, a = 1 → ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L) →
      (∀ p ∈ F, k ≤ (typed p.1 p.2 H R (old p.1) (new p.2) a).card) →
      (F.card : ℝ) ≤ A * (N : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := ExpandedSmoothDegreeOneHostCount.uniform_hosts Q hQ C ε (10 * (Dcut + 1)) Dold K hε
  obtain ⟨Nw, hw⟩ := EnlargedOffsetRegime.uniform_widths C Dold
  refine ⟨k, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hc⟩ := hk hCover hPila
  refine ⟨A, hA, max Nc Nw, ?_⟩
  intro N hN L H R hcrit hR hRpos hH old new hold hnew a ha hK F hF hnon hcomponents
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
    exact SubsetComponentHostData.exists_linear
      (hRN.trans_le (mem_Ico.mp hx).1) (hRN.trans_le (mem_Ico.mp hy).1)
      hRpos (old q.1) (new q.2) (hold q.1 hx) (hnew q.2 hy) k a K hK (hcomponents q hq)
  have hbound := hc N (by omega) L (R - 1) (10 * (H + 1)) hcrit
    (by simpa only [hW] using hR) (cutoff_budget hH) a ha
    (F.image castPair) (ExpandedAsymmetricComponentHostCount.cast_expanded Q hQ F hF) hnon' hsystems
  simpa only [card_image_of_injective _ castPair_injective] using hbound
theorem small_density {x y L H R : ℕ} (Dcut : ℕ) (η : ℝ) (hη : 0 < η)
    (U V : Finset ℕ) (hH : H ≤ Dcut * (L + 1))
    (hdense : η * ((L + 1 : ℕ) : ℝ) ≤ (nontrivial x y H R U V).card) :
    (η / 2) * ((L + 1 : ℕ) : ℝ) ≤ (small x y H R U V (sizeCap Dcut η)).card := by
  have hceil : 4 * ((Dcut + 1 : ℕ) : ℝ) / η ≤ (sizeCap Dcut η : ℝ) := Nat.le_ceil _
  have hprod := (div_le_iff₀ hη).mp hceil
  have hcap : (0 : ℝ) < ((sizeCap Dcut η + 1 : ℕ) : ℝ) := by positivity
  have hratio : 2 * ((Dcut + 1 : ℕ) : ℝ) / ((sizeCap Dcut η + 1 : ℕ) : ℝ) ≤ η / 2 := by
    apply (div_le_iff₀ hcap).mpr
    push_cast
    push_cast at hprod
    nlinarith only [hprod, hη]
  have hHB : ((H + 1 : ℕ) : ℝ) ≤ ((Dcut + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show H + 1 ≤ (Dcut + 1) * (L + 1) by nlinarith only [hH])
  have hcost : 2 * ((H + 1 : ℕ) : ℝ) / ((sizeCap Dcut η + 1 : ℕ) : ℝ) ≤
      (η / 2) * ((L + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ (2 * ((Dcut + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ)) /
          ((sizeCap Dcut η + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (by linarith only [hHB]) hcap.le
      _ = (2 * ((Dcut + 1 : ℕ) : ℝ) / ((sizeCap Dcut η + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)
  have hs := MediumPrimeColumns.small_component_card_real (AsymmetricEnvelopeGraph.start x R)
    (AsymmetricEnvelopeGraph.start y R) H (nontrivial x y H R U V) (sizeCap Dcut η)
  change ((nontrivial x y H R U V).card : ℝ) -
    2 * ((H + 1 : ℕ) : ℝ) / ((sizeCap Dcut η + 1 : ℕ) : ℝ) ≤
      ((small x y H R U V (sizeCap Dcut η)).card : ℝ) at hs
  linarith only [hs, hcost, hdense]


theorem uniform_dense (Q : ℕ) (hQ : 1 ≤ Q) (C ε η : ℝ) (Dold Dcut : ℕ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Ds k : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (sizeCap Dcut η) Ds →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dold * (L + 1) →
      1 ≤ R → H ≤ Dcut * (L + 1) →
      ∀ old new : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      (∀ y ∈ dyadicBlock N, ∀ n ∈ new y, |(n : ℤ) - y| ≤ (R : ℤ)) →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ (nontrivial p.1 p.2 H R (old p.1) (new p.2)).card) →
      (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨Ds, k, hDs, hk⟩ := uniform_general Q hQ C ε Dold Dcut (sizeCap Dcut η) hε
  obtain ⟨Ns, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨Nl, hl⟩ := ElementaryLogGrowth.log_ge_eventually
    (2 * (k : ℝ) / (η * CriticalBandScale.lowerScale))
  refine ⟨Ds, k, hDs, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hc⟩ := hk hCover hPila
  refine ⟨A, hA, max Nc (max Ns Nl), ?_⟩
  intro N hN L H R hcrit hR hRpos hH old new hold hnew F hF hnon hdense
  have hscale := (hs N (by omega) L hcrit).1
  have hlog := (div_le_iff₀ (mul_pos hη CriticalBandScale.lowerScale_pos)).mp (hl N (by omega)).1
  have hscaled := mul_le_mul_of_nonneg_left hscale hη.le
  have hlarge : (k : ℝ) ≤ (η / 2) * ((L + 1 : ℕ) : ℝ) := by nlinarith only [hlog, hscaled]
  apply hc N (by omega) L H R hcrit hR hRpos hH old new hold hnew F hF hnon
  intro p hp
  have hh := hlarge.trans (small_density Dcut η hη (old p.1) (new p.2) hH (hdense p hp))
  exact_mod_cast hh


end PaperP1.SubsetComponentHostCount
