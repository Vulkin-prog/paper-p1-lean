module

public import PaperP1.Asymptotics.SharpChannelCompressedActivityUnderInputs
public import PaperP1.Model.RetainedIndependentDeficitComparison

/-! # The full original distinguished good-pair activity with arbitrary real cutoffs

The original compatible good-edge definition is used literally. Targets may
be irregular, incompatible, or have zero marginal. The stronger separated
bound holds for both principal channels together and hence for either one.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalCompressedActivityUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ChannelCompressedActivityBounds
  PaperP1.SharpChannelCompressedActivityUnderInputs

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def originalPairs (H : ℝ) (N L : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (CompressedPairMass.pairs (dyadicBlock N) L).filter fun p ↦ p.1 ∈ GoodEdgeCompression.goodEdges H N L

def originalSeparated (H : ℝ) (N L : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (originalPairs H N L).filter fun p ↦ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2)

theorem original_cover {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) :
    originalPairs H N L ⊆ pairs N 0 2 3 L ∪ pairs N 0 3 4 L := by
  intro p hp
  obtain ⟨hpP, hpGood⟩ := mem_filter.mp hp
  rcases mem_union.mp (RetainedIndependentDeficitComparison.good_subset_zero_channels hN H hpGood) with h23 | h34
  · exact mem_union_left _ (mem_filter.mpr ⟨hpP, h23⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨hpP, h34⟩)

theorem separated_cover {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) :
    originalSeparated H N L ⊆ separated N 0 2 3 L ∪ separated N 0 3 4 L := by
  intro p hp
  obtain ⟨hpP, hsep⟩ := mem_filter.mp hp
  rcases mem_union.mp (original_cover hN H hpP) with h23 | h34
  · exact mem_union_left _ (mem_filter.mpr ⟨h23, hsep⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨h34, hsep⟩)

theorem separated_mass_le_channels {N L : ℕ} (hN : 2 ≤ N) (H w : ℝ) (hw : 0 ≤ w) :
    CompressedPairMass.mass (originalSeparated H N L) L w ≤
      CompressedPairMass.mass (separated N 0 2 3 L) L w +
        CompressedPairMass.mass (separated N 0 3 4 L) L w := by
  apply (CompressedPairMass.mass_mono _ _ (separated_cover hN H) L w hw).trans
  apply GraphStarWeights.sum_union_le_nonneg
  intro p
  exact mul_nonneg (pow_nonneg hw _)
    (add_nonneg (add_nonneg (InfiniteStarts.infiniteJointMoment_nonneg L _) (abs_nonneg _)) (abs_nonneg _))

theorem companion_T15_1_original (C w ε : ℝ) (hw : 0 < w) (hε : 0 < ε) :
    ∃ p23 p34 : Parameters, ∃ pall : CompressedPairMassUnderInputs.Parameters,
      Hypotheses p23 3 (ε / 2) → Hypotheses p34 4 (ε / 2) →
      CompressedPairMassUnderInputs.Hypotheses pall ε →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      CompressedPairMass.mass (originalSeparated H N L) L w ≤ (N : ℝ) ^ (-41 / 30 + ε) ∧
      CompressedPairMass.mass (originalPairs H N L) L w ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨p23, p34, hs⟩ := companion_T15_1_separated C w (ε / 2) hw (by positivity)
  obtain ⟨pall, ha⟩ := CompressedPairMassUnderInputs.uniform_subfamily w C ε hw hε
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p23, p34, pall, ?_⟩
  intro hp23 hp34 hpall
  obtain ⟨NS, _hNS, hs⟩ := hs hp23 hp34
  obtain ⟨NA, _hNA, ha⟩ := ha hpall
  refine ⟨10 + NS + NA + NF, by omega, ?_⟩
  intro N hN L hband H
  have hchannels := hs N (by omega) L 0 hband
  have hfinite := separated_mass_le_channels (by omega : 2 ≤ N) H w hw.le (L := L)
  refine ⟨?_, ha N (by omega) L hband _ Subset.rfl _ (filter_subset _ _)⟩
  calc
    _ ≤ 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by linarith only [hfinite, hchannels.1, hchannels.2]
    _ ≤ (N : ℝ) ^ ((-41 / 30 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem subfamily_bounds {N L : ℕ} (H w Msep Mall : ℝ) (hw : 0 ≤ w)
    (hsep : CompressedPairMass.mass (originalSeparated H N L) L w ≤ Msep)
    (hall : CompressedPairMass.mass (originalPairs H N L) L w ≤ Mall)
    (P Q : Finset (Finset ℕ × Finset ℕ))
    (hP : P ⊆ originalSeparated H N L) (hQ : Q ⊆ originalPairs H N L) :
    CompressedPairMass.mass P L w ≤ Msep ∧ CompressedPairMass.mass Q L w ≤ Mall :=
  ⟨(CompressedPairMass.mass_mono _ _ hP L w hw).trans hsep,
    (CompressedPairMass.mass_mono _ _ hQ L w hw).trans hall⟩

end PaperP1.OriginalCompressedActivityUnderInputs
