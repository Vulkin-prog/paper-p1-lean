module

public import PaperP1.Combinatorics.InjectiveHostWeights
public import PaperP1.Arithmetic.WindowPairCentreBlocks
public import PaperP1.Arithmetic.CompressedPairIntersectionHosts
public import PaperP1.Arithmetic.CompressedTargetAlignment
public import PaperP1.Model.HomogeneousSubsetBlockInteraction

/-! # Actual private-pair weights on injectively encoded centre hosts

The host family retains every incompatible affine configuration. Its two
prescribed value sets are exactly the two original effective pair spaces.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WindowPairInteractionHosts

open Finset PaperP1.Model PaperP1.Arithmetic PaperP1.DyadicEndpointPairs
  PaperP1.HomogeneousRunMass PaperP1.WindowPairCentreBlocks

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def key (b d : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × ℕ :=
  (centre b p.1, centre d p.2)

def family (p : (ℕ × ℕ) × (ℕ × ℕ)) : Finset ℕ := {p.1.1, p.1.2} ∪ {p.2.1, p.2.2}

def sources (N H₁ H₂ a b c d L : ℕ) (i j k l : Fin (L + 1)) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (CompressedPairIntersectionHosts.pairs N a b c d L i j k l).filter fun p ↦
    p.1 ∈ PrivateChannelSources.goodSources N H₁ a b L ∧
    p.2 ∈ PrivateChannelSources.goodSources N H₂ c d L ∧
    ¬CompressedTargetAlignment.Aligned (2 * b) (key b d p).1 (key b d p).2 L

def weight (L b d : ℕ) (P : Finset ((ℕ × ℕ) × (ℕ × ℕ))) (q : ℕ × ℕ) : ℝ :=
  probability L (family (InjectiveHostWeights.recover P (key b d) q))

theorem source_data {N H₁ H₂ a b c d L : ℕ} {i j k l : Fin (L + 1)}
    {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ sources N H₁ H₂ a b c d L i j k l) :
    p.1 ∈ sourcePairs N a b L i j ∧ p.2 ∈ sourcePairs N c d L k l ∧
      p.1 ∈ PrivateChannelSources.goodSources N H₁ a b L ∧
      p.2 ∈ PrivateChannelSources.goodSources N H₂ c d L ∧
      ¬CompressedTargetAlignment.Aligned (2 * b) (key b d p).1 (key b d p).2 L := by
  obtain ⟨hpair, hp₁, hp₂, hnon⟩ := mem_filter.mp hp
  obtain ⟨hfirst, hsecond⟩ := mem_product.mp (mem_filter.mp hpair).1
  exact ⟨hfirst, hsecond, hp₁, hp₂, hnon⟩

theorem key_injective {N H₁ H₂ a b c d L : ℕ} (hN : 0 < N)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (i j k l : Fin (L + 1)) :
    Set.InjOn (key b d) (sources N H₁ H₂ a b c d L i j k l) := by
  intro p hp q hq heq
  exact Prod.ext
    (centre_injective hN ha hb i j (source_data hp).1 (source_data hq).1 (congrArg Prod.fst heq))
    (centre_injective hN hc hd k l (source_data hp).2.1 (source_data hq).2.1 (congrArg Prod.snd heq))

theorem weight_key {N H₁ H₂ a b c d L : ℕ} (hN : 0 < N)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (i j k l : Fin (L + 1))
    {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ sources N H₁ H₂ a b c d L i j k l) :
    weight L b d (sources N H₁ H₂ a b c d L i j k l) (key b d p) = probability L (family p) := by
  rw [weight, InjectiveHostWeights.recover_apply _ _ (key_injective hN ha hb hc hd i j k l) hp]

theorem sum_eq {N H₁ H₂ a b c d L : ℕ} (hN : 0 < N)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (i j k l : Fin (L + 1)) :
    (∑ q ∈ (sources N H₁ H₂ a b c d L i j k l).image (key b d),
      weight L b d (sources N H₁ H₂ a b c d L i j k l) q) =
      ∑ p ∈ sources N H₁ H₂ a b c d L i j k l, probability L (family p) := by
  rw [sum_image (key_injective hN ha hb hc hd i j k l)]
  exact sum_congr rfl (fun p hp ↦ weight_key hN ha hb hc hd i j k l hp)

theorem upper_loss {N a b c d L : ℕ} (hN : 2 ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (i j k l : Fin (L + 1)) {p : (ℕ × ℕ) × (ℕ × ℕ)}
    (hp : p.1 ∈ sourcePairs N a b L i j) (hq : p.2 ∈ sourcePairs N c d L k l) (H : ℕ) :
    probability L (family p) ≤ probability L {p.1.1, p.1.2} * probability L {p.2.1, p.2.2} *
      (2 ^ SubsetEvenLoss.loss H (block N a b L i j (key b d p).1)
        (block N c d L k l (key b d p).2) : ℝ) := by
  apply HomogeneousSubsetBlockInteraction.upper_loss
  · dsimp only [key]
    rw [space_eq hN ha hb i j hp]
    exact PaperP1.RetainedNullity.span_pair _ _ _
  · dsimp only [key]
    rw [space_eq hN hc hd k l hq]
    exact PaperP1.RetainedNullity.span_pair _ _ _

def allSources (N H₁ H₂ a b c d L : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (CompressedPairIntersectionHosts.allPairs N a b c d L).filter fun p ↦
    p.1 ∈ PrivateChannelSources.goodSources N H₁ a b L ∧
    p.2 ∈ PrivateChannelSources.goodSources N H₂ c d L ∧
    ¬CompressedTargetAlignment.Aligned (2 * b) (key b d p).1 (key b d p).2 L

def mass (N H₁ H₂ a b c d L : ℕ) : ℝ :=
  ∑ p ∈ allSources N H₁ H₂ a b c d L, probability L (family p)

theorem all_sources_cover (N H₁ H₂ a b c d L : ℕ) :
    allSources N H₁ H₂ a b c d L ⊆ univ.biUnion
      (fun w : (Fin (L + 1) × Fin (L + 1)) × (Fin (L + 1) × Fin (L + 1)) ↦
        sources N H₁ H₂ a b c d L w.1.1 w.1.2 w.2.1 w.2.2) := by
  intro p hp
  obtain ⟨hpA, hp₁, hp₂, hnon⟩ := mem_filter.mp hp
  obtain ⟨w, hw, hpw⟩ := mem_biUnion.mp (CompressedPairIntersectionHosts.all_pairs_cover N a b c d L hpA)
  exact mem_biUnion.mpr ⟨w, hw, mem_filter.mpr ⟨hpw, hp₁, hp₂, hnon⟩⟩

end PaperP1.WindowPairInteractionHosts
