module

public import PaperP1.Asymptotics.PairCompressedDenseExtensions
public import PaperP1.Asymptotics.HomogeneousFullChannelMass
public import PaperP1.Model.PairCompressedPrimitivePopulation

/-! # Summing dense compressed extensions over every actual fixed-channel source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairCompressedDenseMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PairCompressedPrimitiveFamilies
  PaperP1.PairCompressedPrimitivePopulation PaperP1.FixedChannelSourceGeometry

theorem uniform_bound (a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset ((ℕ × ℕ) × (Fin 2 → ℕ)), F ⊆ points N a b L 2 →
      (∀ q ∈ F, η * L ≤ (nullity q.1 L q.2 : ℝ)) →
      (∑ q ∈ F, HomogeneousRunMass.probability L (family q.1 q.2)) ≤
        (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  classical
  obtain ⟨NE, _hNE, he⟩ := PairCompressedDenseExtensions.uniform_extensions C η (ε / 2) hη (by positivity)
  obtain ⟨NS, _hNS, hs⟩ := HomogeneousFullChannelMass.uniform_bound C (ε / 2) a b ha hab hcop (by positivity)
  refine ⟨max 3 (max NS NE), by omega, ?_⟩
  intro N hN L hband F hF hρ
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let w := fun q : (ℕ × ℕ) × (Fin 2 → ℕ) ↦ HomogeneousRunMass.probability L (family q.1 q.2)
  have hsplit := sum_fiberwise_of_maps_to (s := F) (t := unitSources N a b L) (g := Prod.fst)
    (fun q hq ↦ (mem_points.mp (hF hq)).1) w
  have hrow (xy : ℕ × ℕ) (hxy : xy ∈ unitSources N a b L) :
      (∑ q ∈ F.filter (fun q ↦ q.1 = xy), w q) ≤
        HomogeneousRunMass.probability L {xy.1, xy.2} * (N : ℝ) ^ (-1 + ε / 2) := by
    let P := F.filter fun q ↦ q.1 = xy
    let Z := P.image Prod.snd
    have hinj : Set.InjOn Prod.snd (P : Set ((ℕ × ℕ) × (Fin 2 → ℕ))) := by
      intro q hq u hu heq
      exact Prod.ext ((mem_filter.mp hq).2.trans (mem_filter.mp hu).2.symm) heq
    have hZ : ∀ z ∈ Z, (∀ i, z i ∈ RegularStarts.regularStarts N L) ∧
        Primitive xy L z ∧ η * L ≤ (nullity xy L z : ℝ) := by
      intro z hz
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
      obtain ⟨hqF, hroot⟩ := mem_filter.mp hq
      have hd := mem_points.mp (hF hqF)
      exact ⟨hd.2.1, hroot ▸ hd.2.2.2, hroot ▸ hρ q hqF⟩
    have hblocks := mem_product.mp (mem_filter.mp hxy).1
    have hmass := he N (by omega) L hband xy hblocks.1 hblocks.2 Z hZ
    have heq : (∑ z ∈ Z, HomogeneousRunMass.probability L (family xy z)) = ∑ q ∈ P, w q := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro q hq
      dsimp [w]
      rw [(mem_filter.mp hq).2]
    exact heq ▸ hmass
  calc
    _ = ∑ xy ∈ unitSources N a b L, ∑ q ∈ F.filter (fun q ↦ q.1 = xy), w q := hsplit.symm
    _ ≤ ∑ xy ∈ unitSources N a b L,
        HomogeneousRunMass.probability L {xy.1, xy.2} * (N : ℝ) ^ (-1 + ε / 2) := sum_le_sum hrow
    _ = (∑ xy ∈ unitSources N a b L, HomogeneousRunMass.probability L {xy.1, xy.2}) *
        (N : ℝ) ^ (-1 + ε / 2) := (sum_mul _ _ _).symm
    _ ≤ (N : ℝ) ^ (-1 + 1 / (b : ℝ) + ε / 2) * (N : ℝ) ^ (-1 + ε / 2) :=
      mul_le_mul_of_nonneg_right (hs N (by omega) L hband) (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.PairCompressedDenseMass
