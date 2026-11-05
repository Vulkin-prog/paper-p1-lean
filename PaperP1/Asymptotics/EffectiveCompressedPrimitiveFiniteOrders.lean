module

public import PaperP1.Asymptotics.EffectiveCompressedPrimitiveMass
public import PaperP1.Model.EffectiveChannelCompressedPrimitiveSets

/-! # One finite bundle handles bounded compressed orders with every effective target -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveCompressedPrimitiveFiniteOrders

open Finset Filter PaperP1.Arithmetic PaperP1.Model PaperP1.FixedChannelSourceGeometry

theorem uniform_orders (s a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hb : 3 ≤ b) (hb4 : b ≤ 4) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ t ∈ Ico 2 s,
      EffectiveCompressedPrimitivePopulation.mass N a b L t ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  obtain ⟨NT, _hNT, hT⟩ := EffectiveCompressedPrimitiveMass.three_blocks a b ha hab hcop hb hb4 C ε hε
  have heach (t : ℕ) (ht : t ∈ Ico 3 s) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      EffectiveCompressedPrimitivePopulation.mass N a b L t ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
    obtain ⟨N₀, _hN₀, hm⟩ := EffectiveCompressedPrimitiveElementaryMass.from_four
      t a b (mem_Ico.mp ht).1 ha hab hcop hb hb4 C ε hε
    exact eventually_atTop.mpr ⟨N₀, fun N hN ↦ hm N hN⟩
  obtain ⟨NU, hU⟩ := eventually_atTop.mp ((Finset.eventually_all (Ico 3 s)).mpr heach)
  refine ⟨max 3 (max NU NT), by omega, ?_⟩
  intro N hN L hband t ht
  by_cases ht2 : t = 2
  · subst t
    exact hT N (by omega) L hband
  · exact hU N (by omega) t (mem_Ico.mpr ⟨by have hh := (mem_Ico.mp ht).1; omega, (mem_Ico.mp ht).2⟩)
      L hband

theorem bounded_cardinality (s a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hb : 3 ≤ b) (hb4 : b ≤ 4) (C w ε : ℝ) (hw : 0 < w) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ P : Finset ((ℕ × ℕ) × Finset ℕ),
      (∀ q ∈ P, q.1 ∈ unitSources N a b L ∧ q.2 ⊆ dyadicBlock N ∧
        2 ≤ q.2.card ∧ q.2.card < s ∧ PairPrimitiveCompression.Primitive L {q.1.1, q.1.2} q.2) →
      (∑ q ∈ P, EffectiveChannelCompressedPrimitiveSets.weight L w q.1 q.2) ≤
        (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  classical
  let K := ∑ t ∈ Ico 2 s, w ^ (t + 2)
  obtain ⟨NM, _hNM, hm⟩ := uniform_orders s a b ha hab hcop hb hb4 C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K
    (-2 + 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 3 (max NM NF), by omega, ?_⟩
  intro N hN L hband P hP
  let v := fun q : (ℕ × ℕ) × Finset ℕ ↦ HomogeneousRunMass.probability L ({q.1.1, q.1.2} ∪ q.2)
  let W := fun q : (ℕ × ℕ) × Finset ℕ ↦ EffectiveChannelCompressedPrimitiveSets.weight L w q.1 q.2
  have hsplit := sum_fiberwise_of_maps_to (s := P) (t := Ico 2 s) (g := fun q ↦ q.2.card)
    (fun q hq ↦ mem_Ico.mpr ⟨(hP q hq).2.2.1, (hP q hq).2.2.2.1⟩) W
  have hrow (t : ℕ) (ht : t ∈ Ico 2 s) :
      (∑ q ∈ P.filter (fun q ↦ q.2.card = t), W q) ≤
        w ^ (t + 2) * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by
    let F := P.filter fun q ↦ q.2.card = t
    have hcap := EffectiveCompressedPrimitiveTransport.finite_mass_bound F (by
      intro q hq
      obtain ⟨hqP, hcard⟩ := mem_filter.mp hq
      have hd := hP q hqP
      exact ⟨hd.1, hd.2.1, hcard, hd.2.2.2.2⟩)
    calc
      _ = w ^ (t + 2) * ∑ q ∈ F, v q := by
        rw [mul_sum]
        exact sum_congr rfl (fun q hq ↦ by dsimp [W, EffectiveChannelCompressedPrimitiveSets.weight, v]; rw [(mem_filter.mp hq).2])
      _ ≤ w ^ (t + 2) * EffectiveCompressedPrimitivePopulation.mass N a b L t :=
        mul_le_mul_of_nonneg_left hcap (pow_nonneg hw.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hm N (by omega) L hband t ht) (pow_nonneg hw.le _)
  calc
    _ = ∑ t ∈ Ico 2 s, ∑ q ∈ P.filter (fun q ↦ q.2.card = t), W q := hsplit.symm
    _ ≤ ∑ t ∈ Ico 2 s, w ^ (t + 2) * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := sum_le_sum hrow
    _ = K * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := (sum_mul _ _ _).symm
    _ ≤ (N : ℝ) ^ ((-2 + 1 / (b : ℝ) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.EffectiveCompressedPrimitiveFiniteOrders
