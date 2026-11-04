module

public import PaperP1.Model.WindowPairInteractionHosts
public import PaperP1.Combinatorics.EncodedPairUnionWeights
public import PaperP1.Model.FiniteInteriorUnitEdges
public import PaperP1.Asymptotics.ScaledAlignedTripleMass

/-! # Literal interacting ordered pairs of raw private-channel edges -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivatePairInteractions

open Finset PaperP1.Model PaperP1.Arithmetic PaperP1.WindowPairInteractionHosts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def edge (xy : ℕ × ℕ) : Finset ℕ := {xy.1, xy.2}

def pairKey (p : (ℕ × ℕ) × (ℕ × ℕ)) : Finset ℕ × Finset ℕ := (edge p.1, edge p.2)

def points (N H₁ H₂ a b c d L : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((PrivateChannelSources.goodSources N H₁ a b L) ×ˢ (PrivateChannelSources.goodSources N H₂ c d L)).filter fun p ↦
    edge p.1 ≠ edge p.2 ∧ SeparatedHomogeneousMass.Separated L (family p) ∧
      (squareClassSpace p.1.1 L ⊔ squareClassSpace p.1.2 L) ⊓
        (squareClassSpace p.2.1 L ⊔ squareClassSpace p.2.2 L) ≠ ⊥

def mass (N H₁ H₂ a b c d L : ℕ) : ℝ :=
  ∑ p ∈ points N H₁ H₂ a b c d L, HomogeneousRunMass.probability L (family p)

theorem pair_key_injective {N H₁ H₂ a b c d L : ℕ} (hN : 2 ≤ N) (hab : a < b) (hcd : c < d)
    (hlarge₁ : (a + b) * (L + 1) < N) (hlarge₂ : (c + d) * (L + 1) < N)
    (P : Finset ((ℕ × ℕ) × (ℕ × ℕ)))
    (hP : ∀ p ∈ P, p.1 ∈ PrivateChannelSources.goodSources N H₁ a b L ∧
      p.2 ∈ PrivateChannelSources.goodSources N H₂ c d L) : Set.InjOn pairKey P := by
  intro p hp q hq heq
  exact Prod.ext
    (PrivateChannelActivity.pair_map_injective hN hab hlarge₁ (hP p hp).1 (hP q hq).1 (congrArg Prod.fst heq))
    (PrivateChannelActivity.pair_map_injective hN hcd hlarge₂ (hP p hp).2 (hP q hq).2 (congrArg Prod.snd heq))

theorem source_data {N H₁ H₂ a b c d L : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)}
    (hp : p ∈ points N H₁ H₂ a b c d L) :
    p.1 ∈ PrivateChannelSources.goodSources N H₁ a b L ∧
      p.2 ∈ PrivateChannelSources.goodSources N H₂ c d L ∧ edge p.1 ≠ edge p.2 ∧
      SeparatedHomogeneousMass.Separated L (family p) ∧
      (squareClassSpace p.1.1 L ⊔ squareClassSpace p.1.2 L) ⊓
        (squareClassSpace p.2.1 L ⊔ squareClassSpace p.2.2 L) ≠ ⊥ := by
  obtain ⟨hpS, hne, hsep, hdep⟩ := mem_filter.mp hp
  exact ⟨(mem_product.mp hpS).1, (mem_product.mp hpS).2, hne, hsep, hdep⟩

theorem family_data {N H₁ H₂ a b c d L : ℕ} (hN : 2 ≤ N) (hab : a < b) (hcd : c < d)
    (hlarge₁ : (a + b) * (L + 1) < N) (hlarge₂ : (c + d) * (L + 1) < N)
    {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ points N H₁ H₂ a b c d L) :
    family p ⊆ dyadicBlock N ∧ (family p).card = 3 ∨ family p ⊆ dyadicBlock N ∧ (family p).card = 4 := by
  obtain ⟨hp₁, hp₂, hne, _hsep, _hdep⟩ := source_data hp
  have he := PrivateChannelActivity.pair_data hN hab hlarge₁ (mem_image.mpr ⟨p.1, hp₁, rfl⟩)
  have hf := PrivateChannelActivity.pair_data hN hcd hlarge₂ (mem_image.mpr ⟨p.2, hp₂, rfl⟩)
  change edge p.1 ⊆ dyadicBlock N ∧ (edge p.1).card = 2 at he
  change edge p.2 ⊆ dyadicBlock N ∧ (edge p.2).card = 2 at hf
  have hsub : family p ⊆ dyadicBlock N := union_subset he.1 hf.1
  by_cases hdis : Disjoint (edge p.1) (edge p.2)
  · exact Or.inr ⟨hsub, by change (edge p.1 ∪ edge p.2).card = 4; rw [card_union_of_disjoint hdis, he.2, hf.2]⟩
  · exact Or.inl ⟨hsub, PaperP1.TwoEdgeTripleCover.union_card_three he.2 hf.2 hne hdis⟩

theorem edge_mem_interior {N H a b L Q : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hint : b < 2 * a) (hcop : a.Coprime b) (hbQ : b ≤ Q) (hlarge : (a + b) * (L + 1) < N)
    {xy : ℕ × ℕ} (hxy : xy ∈ PrivateChannelSources.goodSources N H a b L) :
    edge xy ∈ FiniteInteriorUnitEdges.edges N L Q := by
  obtain ⟨hx, hy, hu, _hprivate⟩ := PrivateChannelSources.mem_goodSources.mp hxy
  have hdata := PrivateChannelActivity.pair_data hN hab hlarge (mem_image.mpr ⟨xy, hxy, rfl⟩)
  have hunit : (NormalizedUnitCount.units a b xy.1 xy.2 L).Nonempty := card_pos.mp (by omega)
  refine mem_filter.mpr ⟨mem_powersetCard.mpr hdata, (a, b), ?_, xy.1, xy.2, rfl, hunit⟩
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨ha, by omega⟩, mem_Icc.mpr ⟨ha.trans hab, hbQ⟩⟩,
    hab, hint, hcop⟩

theorem shared_host {N H₁ H₂ a b c d L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hint : b < 2 * a) (hcop : a.Coprime b) (hc : 0 < c) (hcd : c < d)
    (hint' : d < 2 * c) (hcop' : c.Coprime d)
    (hlarge₁ : (a + b) * (L + 1) < N) (hlarge₂ : (c + d) * (L + 1) < N)
    {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ points N H₁ H₂ a b c d L) (hcard : (family p).card = 3) :
    family p ⊆ dyadicBlock N ∧ (family p).card = 3 ∧ SeparatedHomogeneousMass.Separated L (family p) ∧
      2 ≤ ((FiniteInteriorUnitEdges.edges N L (max b d)).filter fun e ↦ e ⊆ family p).card := by
  obtain ⟨hp₁, hp₂, hne, hsep, _hdep⟩ := source_data hp
  have he := edge_mem_interior hN ha hab hint hcop (le_max_left b d) hlarge₁ hp₁
  have hf := edge_mem_interior hN hc hcd hint' hcop' (le_max_right b d) hlarge₂ hp₂
  have hsub : family p ⊆ dyadicBlock N := (family_data hN hab hcd hlarge₁ hlarge₂ hp).elim And.left And.left
  refine ⟨hsub, hcard, hsep, ?_⟩
  have hinc : ({edge p.1, edge p.2} : Finset (Finset ℕ)) ⊆
      (FiniteInteriorUnitEdges.edges N L (max b d)).filter (fun e ↦ e ⊆ family p) := by
    intro e he'
    simp only [mem_insert, mem_singleton] at he'
    rcases he' with rfl | rfl
    · exact mem_filter.mpr ⟨he, subset_union_left⟩
    · exact mem_filter.mpr ⟨hf, subset_union_right⟩
  simpa only [card_pair hne] using card_le_card hinc

theorem aligned_host {N H₁ H₂ a b c d L : ℕ} (hN : 2 ≤ N) (hab : a < b) (hcd : c < d)
    (hlarge₁ : (a + b) * (L + 1) < N) (hlarge₂ : (c + d) * (L + 1) < N) (hd : 0 < d)
    {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ points N H₁ H₂ a b c d L) (hcard : (family p).card = 4)
    (halign : CompressedTargetAlignment.Aligned (2 * b) (key b d p).1 (key b d p).2 L) :
    family p ∈ ScaledAlignedTripleMass.extensions {(a, b)} (max b d) (2 * b) 1 N L := by
  obtain ⟨hp₁, hp₂, _hne, hsep, _hdep⟩ := source_data hp
  have he := PrivateChannelActivity.pair_data hN hab hlarge₁ (mem_image.mpr ⟨p.1, hp₁, rfl⟩)
  have hf := PrivateChannelActivity.pair_data hN hcd hlarge₂ (mem_image.mpr ⟨p.2, hp₂, rfl⟩)
  change edge p.1 ⊆ dyadicBlock N ∧ (edge p.1).card = 2 at he
  change edge p.2 ⊆ dyadicBlock N ∧ (edge p.2).card = 2 at hf
  have hdis : Disjoint (edge p.1) (edge p.2) := by
    apply disjoint_iff_inter_eq_empty.mpr
    have hcount := card_union_add_card_inter (edge p.1) (edge p.2)
    apply card_eq_zero.mp
    change (edge p.1 ∪ edge p.2).card = 4 at hcard
    omega
  have hfresh : p.2.1 ∉ edge p.1 := fun hh ↦ disjoint_left.mp hdis hh (by simp [edge])
  let T : Finset ℕ := {p.1.1, p.1.2, p.2.1}
  have hTsub : T ⊆ family p := by
    intro x hx
    simp only [T, mem_insert, mem_singleton, family, mem_union] at hx ⊢
    tauto
  have hTcard : T.card = 3 := by
    have heq : T = insert p.2.1 (edge p.1) := by
      ext x
      simp only [T, edge, mem_insert, mem_singleton]
      tauto
    rw [heq, card_insert_of_notMem hfresh, he.2]
  have hunit := (mem_filter.mp (PrivateChannelSources.good_sources_subset_unitSources N H₁ a b L hp₁)).2
  have hThost : T ∈ ScaledAlignedTripleMass.hosts {(a, b)} (max b d) (2 * b) N L := by
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hTsub.trans (union_subset he.1 hf.1), hTcard⟩,
      (a, b), mem_singleton_self _, p.1.1, p.1.2, p.2.1, d, rfl, hunit, hd, le_max_right b d, halign⟩
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨union_subset he.1 hf.1, hcard⟩, hsep, T, hThost, hTsub⟩

theorem nonaligned_mem {N H₁ H₂ a b c d L : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)}
    (hp : p ∈ points N H₁ H₂ a b c d L)
    (hnon : ¬CompressedTargetAlignment.Aligned (2 * b) (key b d p).1 (key b d p).2 L) :
    p ∈ allSources N H₁ H₂ a b c d L := by
  obtain ⟨hp₁, hp₂, _hne, _hsep, hdep⟩ := source_data hp
  have hfirst := mem_filter.mp (PrivateChannelSources.good_sources_subset_unitSources N H₁ a b L hp₁)
  have hsecond := mem_filter.mp (PrivateChannelSources.good_sources_subset_unitSources N H₂ c d L hp₂)
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hfirst.1, hsecond.1⟩, hfirst.2, hsecond.2, hdep⟩,
    hp₁, hp₂, hnon⟩

end PaperP1.PrivatePairInteractions
