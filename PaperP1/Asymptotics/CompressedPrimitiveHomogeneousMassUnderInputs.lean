module

public import PaperP1.Asymptotics.CompressedPrimitiveFiniteOrdersUnderInputs
public import PaperP1.Asymptotics.CompressedPrimitiveHomogeneousTail

/-! # The homogeneous primitive compressed mass at every cardinality above two targets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedPrimitiveHomogeneousMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ChannelCompressedPrimitiveSets

theorem uniform_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hb : 3 ≤ b) (hb4 : b ≤ 4) (C w ε : ℝ) (hw : 0 < w) (hε : 0 < ε) :
    ∃ p : DensePrimitiveTripleMassUnderInputs.Parameters,
      DensePrimitiveTripleMassUnderInputs.Hypotheses p →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass N a b L 2 w ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  classical
  obtain ⟨s, hs, NT, _hNT, ht⟩ := CompressedPrimitiveHomogeneousTail.uniform_tail a b ha hab hcop hb hb4
    C w (ε / 2) hw (by positivity)
  obtain ⟨p, hp⟩ := CompressedPrimitiveFiniteOrdersUnderInputs.bounded_cardinality
    s a b ha hab hcop hb hb4 C w (ε / 2) hw (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2
    (-2 + 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NS, _hNS, hsmall⟩ := hp hgeo
  refine ⟨10 + NT + NS + NF, by omega, ?_⟩
  intro N hN L hband
  let F := points N a b L 2
  let P := fun q : (ℕ × ℕ) × Finset ℕ ↦ q.2.card < s
  let W := fun q : (ℕ × ℕ) × Finset ℕ ↦ weight L w q.1 q.2
  have hlow : (∑ q ∈ F.filter P, W q) ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by
    apply hsmall N (by omega) L hband
    intro q hq
    obtain ⟨hqF, hsize⟩ := mem_filter.mp hq
    obtain ⟨hsource, hreg, htwo, hprim⟩ := mem_points.mp hqF
    exact ⟨hsource, hreg, htwo, hsize, hprim⟩
  have hlarge : F.filter (fun q ↦ ¬ P q) = points N a b L s := by
    ext q
    simp only [mem_filter, mem_points, P, F, not_lt]
    constructor
    · rintro ⟨⟨hsource, hreg, _htwo, hprim⟩, hsize⟩
      exact ⟨hsource, hreg, hsize, hprim⟩
    · rintro ⟨hsource, hreg, hsize, hprim⟩
      exact ⟨⟨hsource, hreg, hs.trans hsize, hprim⟩, hsize⟩
  have hhigh : (∑ q ∈ F.filter (fun q ↦ ¬ P q), W q) ≤
      (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by
    rw [hlarge]
    change (∑ q ∈ points N a b L s, weight L w q.1 q.2) ≤ _
    rw [← mass_eq_points]
    exact ht N (by omega) L hband
  have hpart := sum_filter_add_sum_filter_not F P W
  calc
    _ ≤ 2 * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by
      rw [mass_eq_points]
      change (∑ q ∈ F, W q) ≤ _
      linarith only [hpart, hlow, hhigh]
    _ ≤ (N : ℝ) ^ ((-2 + 1 / (b : ℝ) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.CompressedPrimitiveHomogeneousMassUnderInputs
