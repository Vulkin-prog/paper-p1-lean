module

public import PaperP1.Arithmetic.EnlargedNormalizedDefectDiagnostics
public import PaperP1.Asymptotics.MacroscopicNormalizedDefectHosts

/-! # Actual nonprivate and extra-kernel macroscopic pair hosts

Each exceptional pair is proved to have a defective normalized value.
The common square-root threshold precedes every positive lower-endpoint
exponent. All sets use the original ordered source and target labels.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicKernelExceptionHosts

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.EnlargedPairGeometry
  PaperP1.GoodEdgeCompression PaperP1.NormalizedPairRankLoss PaperP1.NormalizedUnitCount
  PaperP1.MacroscopicIntervalGeometry

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def cutoff (Q L : ℕ) : ℕ := 8 * Q * (L + 1)

def nonprivatePairs (M : ℕ) (δ : ℝ) (H a b L : ℕ) : Finset (ℕ × ℕ) :=
  ((starts M δ) ×ˢ (starts M δ)).filter fun xy ↦ Geometric a b xy.1 xy.2 L ∧
    ¬PrivateAbove (H : ℝ) (PaperP1.NormalizedWindowSets.union a b xy.1 xy.2 L)

def residualPairs (M : ℕ) (δ : ℝ) (a b L : ℕ) : Finset (ℕ × ℕ) :=
  ((starts M δ) ×ˢ (starts M δ)).filter fun xy ↦ Geometric a b xy.1 xy.2 L ∧
    0 < Module.finrank F₂ (PaperP1.FiniteResidualRank.valueKernel (PaperP1.NormalizedWindowSets.union a b xy.1 xy.2 L))

def extraLossPairs (M : ℕ) (δ : ℝ) (a b L : ℕ) : Finset (ℕ × ℕ) :=
  ((starts M δ) ×ˢ (starts M δ)).filter fun xy ↦ Geometric a b xy.1 xy.2 L ∧
    (units a b xy.1 xy.2 L).card - 1 < pairLoss xy.1 xy.2 L

theorem cutoff_bounds {Q b L : ℕ} (hb : 0 < b) (hbQ : b ≤ Q) : 2 * radius b L < cutoff Q L := by
  have hm := Nat.mul_le_mul_right (L + 1) hbQ
  have hpos : 0 < Q * (L + 1) := Nat.mul_pos (hb.trans_le hbQ) (by omega)
  unfold radius cutoff
  nlinarith only [hm, hpos]

theorem cutoff_real (Q L : ℕ) : (cutoff Q L : ℝ) = (8 * (Q : ℝ)) * ((L + 1 : ℕ) : ℝ) := by
  simp only [cutoff, Nat.cast_mul, Nat.cast_ofNat]

theorem nonprivate_subset {M H a b L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ)
    (hab : a ≤ b) (hcut : 2 * radius b L < H) :
    nonprivatePairs M δ H a b L ⊆ PaperP1.MacroscopicNormalizedDefectHosts.pairs M δ H a b L := by
  intro xy hxy
  obtain ⟨hblock, hg, hbad⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  have hxpos : 0 < xy.1 := by have := starts_pos hM hδ hx; omega
  have hypos : 0 < xy.2 := by have := starts_pos hM hδ hy; omega
  exact mem_filter.mpr ⟨hblock, hg,
    PaperP1.EnlargedNormalizedDefectDiagnostics.normalized_bad_witness hab hxpos hypos hg hcut hbad⟩

theorem residual_subset {M H a b L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ)
    (hab : a ≤ b) (hcut : 2 * radius b L ≤ H) :
    residualPairs M δ a b L ⊆ PaperP1.MacroscopicNormalizedDefectHosts.pairs M δ H a b L := by
  intro xy hxy
  obtain ⟨hblock, hg, hpos⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  have hxpos : 0 < xy.1 := by have := starts_pos hM hδ hx; omega
  have hypos : 0 < xy.2 := by have := starts_pos hM hδ hy; omega
  exact mem_filter.mpr ⟨hblock, hg,
    PaperP1.EnlargedNormalizedDefectDiagnostics.kernel_defect_witness hab hxpos hypos hg hcut hpos⟩

theorem extra_subset {M H a b L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ)
    (ha : 0 < a) (hab : a ≤ b) (hcut : 2 * radius b L ≤ H) :
    extraLossPairs M δ a b L ⊆ PaperP1.MacroscopicNormalizedDefectHosts.pairs M δ H a b L := by
  intro xy hxy
  obtain ⟨hblock, hg, hextra⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  exact mem_filter.mpr ⟨hblock, hg,
    PaperP1.EnlargedNormalizedDefectDiagnostics.extra_loss_witness ha hab
      (starts_pos hM hδ hx) (starts_pos hM hδ hy) hg hcut hextra⟩

theorem nonprivate_count (C : ℝ) (Q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ δ : ℝ, 0 < δ → ∀ L a b : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → a ≤ b → b ≤ Q →
      ((nonprivatePairs M δ (cutoff Q L) a b L).card : ℝ) ≤ (M : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨M₀, h⟩ := PaperP1.MacroscopicNormalizedDefectHosts.uniform_count C (8 * (Q : ℝ)) (by positivity) Q ε hε
  refine ⟨M₀, ?_⟩
  intro M hM δ hδ L a b hcrit ha hab hbQ
  have hcut := cutoff_bounds (ha.trans_le hab) hbQ (L := L)
  have hc : ((nonprivatePairs M δ (cutoff Q L) a b L).card : ℝ) ≤
      (PaperP1.MacroscopicNormalizedDefectHosts.pairs M δ (cutoff Q L) a b L).card := by
    exact_mod_cast card_le_card (nonprivate_subset (by omega : 2 ≤ M) hδ hab hcut)
  exact hc.trans (h M hM δ hδ L (cutoff Q L) a b hcrit ha hab hbQ (le_of_eq (cutoff_real Q L)))

theorem residual_count (C : ℝ) (Q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ δ : ℝ, 0 < δ → ∀ L a b : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → a ≤ b → b ≤ Q →
      ((residualPairs M δ a b L).card : ℝ) ≤ (M : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨M₀, h⟩ := PaperP1.MacroscopicNormalizedDefectHosts.uniform_count C (8 * (Q : ℝ)) (by positivity) Q ε hε
  refine ⟨M₀, ?_⟩
  intro M hM δ hδ L a b hcrit ha hab hbQ
  have hcut := cutoff_bounds (ha.trans_le hab) hbQ (L := L)
  have hc : ((residualPairs M δ a b L).card : ℝ) ≤
      (PaperP1.MacroscopicNormalizedDefectHosts.pairs M δ (cutoff Q L) a b L).card := by
    exact_mod_cast card_le_card (residual_subset (by omega : 2 ≤ M) hδ hab hcut.le)
  exact hc.trans (h M hM δ hδ L (cutoff Q L) a b hcrit ha hab hbQ (le_of_eq (cutoff_real Q L)))

theorem extra_loss_count (C : ℝ) (Q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ δ : ℝ, 0 < δ → ∀ L a b : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → a ≤ b → b ≤ Q →
      ((extraLossPairs M δ a b L).card : ℝ) ≤ (M : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨M₀, h⟩ := PaperP1.MacroscopicNormalizedDefectHosts.uniform_count C (8 * (Q : ℝ)) (by positivity) Q ε hε
  refine ⟨M₀, ?_⟩
  intro M hM δ hδ L a b hcrit ha hab hbQ
  have hcut := cutoff_bounds (ha.trans_le hab) hbQ (L := L)
  have hc : ((extraLossPairs M δ a b L).card : ℝ) ≤
      (PaperP1.MacroscopicNormalizedDefectHosts.pairs M δ (cutoff Q L) a b L).card := by
    exact_mod_cast card_le_card (extra_subset (by omega : 2 ≤ M) hδ ha hab hcut.le)
  exact hc.trans (h M hM δ hδ L (cutoff Q L) a b hcrit ha hab hbQ (le_of_eq (cutoff_real Q L)))

end PaperP1.MacroscopicKernelExceptionHosts
