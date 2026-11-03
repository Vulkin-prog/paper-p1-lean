module

public import PaperP1.Asymptotics.StrongAlignedUnitChannels
public import PaperP1.Asymptotics.DenseCompressedPairCount
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Every strongly aligned dense target pair has subpower count, including nonprivate normalizations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongAlignedDensePairCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

def channels (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 Q ×ˢ Icc 1 Q).filter fun ab ↦ ab.1 ≤ ab.2

theorem uniform_count (s : ℕ) (θ C η ε : ℝ) (hθ : 0 < θ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ q, x q ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ q, squareClassSpace (x q) L →
      ∀ F : Finset (ℕ × ℕ),
      (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧
        CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∧
        θ * L < (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ∧
        η * L ≤ (Module.finrank F₂ ↥(W ⊓ (squareClassSpace p.1 L ⊔ squareClassSpace p.2 L)) : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  classical
  obtain ⟨Q, _hQ, hbounded⟩ := StrongAlignedUnitChannels.bounded_channels θ hθ
  obtain ⟨NB, _hNB, hb⟩ := hbounded C
  have hcounts (ab : channels Q) := DenseCompressedPairCount.uniform_count s ab.val.1 ab.val.2
    (by
      have ha := (mem_Icc.mp (mem_product.mp (mem_filter.mp ab.property).1).1).1
      omega) (mem_filter.mp ab.property).2 C η (ε / 2) hη (by positivity)
  choose NC hNC hc using hcounts
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * (channels Q).card : ℝ) (ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NB + NF + univ.sup NC, by omega, ?_⟩
  intro N hN L hband x hx W hW F hF
  let A := fun ab : ℕ × ℕ ↦ DenseCompressedPairs.pairs N ab.1 ab.2 L W η ∪
    (DenseCompressedPairs.pairs N ab.1 ab.2 L W η).image Prod.swap
  have hcover : F ⊆ (channels Q).biUnion A := by
    intro p hp
    obtain ⟨hy, hz, halign, hstrong, hdense⟩ := hF p hp
    obtain ⟨a, b, ha, hab, hbQ, hunit⟩ := hb N (by omega) L hband p.1 p.2 hy hz hstrong halign
    have habmem : (a, b) ∈ channels Q := mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, mem_Icc.mpr ⟨by omega, hbQ⟩⟩, hab⟩
    apply mem_biUnion.mpr
    refine ⟨(a, b), habmem, ?_⟩
    rcases hunit with hunit | hunit
    · exact mem_union_left _ ((DenseCompressedPairs.mem_pairs N a b L W η p).mpr ⟨hy, hz, hunit, hdense⟩)
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨(p.2, p.1), (DenseCompressedPairs.mem_pairs N a b L W η _).mpr
        ⟨hz, hy, hunit, by
          rw [sup_comm (squareClassSpace p.2 L) (squareClassSpace p.1 L)]
          exact hdense⟩, ?_⟩
      cases p
      rfl
  have hA (ab : ℕ × ℕ) (hab : ab ∈ channels Q) : ((A ab).card : ℝ) ≤ 2 * (N : ℝ) ^ (ε / 2) := by
    let v : channels Q := ⟨ab, hab⟩
    have hNv : NC v ≤ univ.sup NC := le_sup (f := NC) (mem_univ v)
    have hcount := hc v N (by omega) L hband x hx W hW
    have hcard : (A ab).card ≤ 2 * (DenseCompressedPairs.pairs N ab.1 ab.2 L W η).card := by
      have hu := card_union_le (DenseCompressedPairs.pairs N ab.1 ab.2 L W η)
        ((DenseCompressedPairs.pairs N ab.1 ab.2 L W η).image Prod.swap)
      have hi := card_image_le (s := DenseCompressedPairs.pairs N ab.1 ab.2 L W η) (f := Prod.swap)
      dsimp only [A]
      omega
    have hcardR : ((A ab).card : ℝ) ≤ 2 * (DenseCompressedPairs.pairs N ab.1 ab.2 L W η).card := by exact_mod_cast hcard
    exact hcardR.trans (mul_le_mul_of_nonneg_left hcount (by norm_num))
  have hfinite : (F.card : ℝ) ≤ ∑ ab ∈ channels Q, ((A ab).card : ℝ) := by
    exact_mod_cast (card_le_card hcover).trans card_biUnion_le
  calc
    _ ≤ _ := hfinite
    _ ≤ ∑ _ab ∈ channels Q, 2 * (N : ℝ) ^ (ε / 2) := sum_le_sum hA
    _ = (2 * (channels Q).card : ℝ) * (N : ℝ) ^ (ε / 2) := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ (N : ℝ) ^ (ε / 2 + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.StrongAlignedDensePairCount
