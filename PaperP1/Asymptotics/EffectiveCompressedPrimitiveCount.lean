module

public import PaperP1.Model.EffectiveCompressedPrimitivePopulation
public import PaperP1.Asymptotics.ValueHeightHalfCount
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # Full effective compressed primitive host counts, including irregular targets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveCompressedPrimitiveCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.PairCompressedPrimitiveFamilies PaperP1.EffectiveCompressedPrimitivePopulation
  PaperP1.DyadicEndpointPairs

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def encode {t : ℕ} (b : ℕ) (p : (ℕ × ℕ) × (Fin t → ℕ)) : Fin (t + 1) → ℕ :=
  Fin.cons (WindowPairCentreBlocks.centre b p.1) p.2

def blocks (N a b L t : ℕ) (i j : Fin (L + 1)) : Fin (t + 1) → ℕ → Finset ℕ :=
  Fin.cons (WindowPairCentreBlocks.block N a b L i j)
    (fun _ x ↦ if x ∈ dyadicBlock N then NormalizedWindowSets.values x L else ∅)

theorem encode_injective {N a b L t : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) : Set.InjOn (encode (t := t) b) (fixedPoints N a b L t i j) := by
  intro p hp q hq heq
  obtain ⟨hroot, htail⟩ := Fin.cons_injective2 heq
  exact Prod.ext (WindowPairCentreBlocks.centre_injective hN ha hb i j
    (mem_fixedPoints.mp hp).1 (mem_fixedPoints.mp hq).1 hroot) htail

theorem encode_mem {N a b L t : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 3 ≤ b)
    (hb4 : b ≤ 4) (i j : Fin (L + 1)) {p : (ℕ × ℕ) × (Fin t → ℕ)}
    (hp : p ∈ fixedPoints N a b L t i j) :
    encode b p ∈ EffectiveWindowLists.lists (range (12 * N + 1)) (blocks N a b L t i j) ∅ := by
  obtain ⟨hsource, hz, hinj, hprim⟩ := mem_fixedPoints.mp hp
  obtain ⟨hx, _hy, _hu⟩ := mem_sourcePairs.mp hsource
  have hrootlo : 2 * N < WindowPairCentreBlocks.centre b p.1 := by
    dsimp [WindowPairCentreBlocks.centre]
    nlinarith only [hN, Nat.mul_le_mul hb (mem_Ico.mp hx).1]
  have hroothi : WindowPairCentreBlocks.centre b p.1 < 12 * N + 1 := by
    dsimp [WindowPairCentreBlocks.centre]
    have h := Nat.mul_le_mul hb4 (Nat.le_of_lt (mem_Ico.mp hx).2)
    nlinarith only [h]
  have hzD : ∀ k, p.2 k ∈ dyadicBlock N := fun k ↦ hz k
  have hencode : Function.Injective (encode b p) := by
    apply Fin.cons_injective_of_injective _ hinj
    rintro ⟨k, hk⟩
    have hhi := (mem_Ico.mp (hzD k)).2
    omega
  obtain ⟨u, hu, hsum⟩ := full_relation p.1 p.2 hprim
  apply (EffectiveWindowLists.mem_lists _ _ _ _).mpr
  refine ⟨?_, hencode, u, ?_, ?_⟩
  · intro k
    refine Fin.cases (by exact mem_range.mpr hroothi) (fun l ↦ ?_) k
    apply mem_range.mpr
    have h := (mem_Ico.mp (hzD l)).2
    change p.2 l < 12 * N + 1
    omega
  · intro k
    have hspace : FiniteEvenSquareClasses.space (blocks N a b L t i j k (encode b p k)) =
        spaces p.1 L p.2 k := by
      refine Fin.cases ?_ (fun l ↦ ?_) k
      · exact WindowPairCentreBlocks.space_eq hN ha (by omega) i j hsource
      · simpa only [blocks, encode, spaces, Fin.cons_succ, ite_eq_left (hzD l)] using
          NormalizedWindowSets.space_values (p.2 l) L
    exact ⟨hspace.symm ▸ (hu k).1, (hu k).2⟩
  · rw [hsum]
    exact Submodule.zero_mem _

theorem fixed_offsets (t a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hb : 3 ≤ b) (hb4 : b ≤ 4) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ i j : Fin (L + 1),
      ((fixedPoints N a b L t i j).card : ℝ) ≤ (N : ℝ) ^ (((t : ℝ) + 1) / 2 + ε) := by
  classical
  obtain ⟨NC, hc⟩ := ValueHeightHalfCount.article_10_1 (t + 1) 0 (1 / 2) 12 8 C ε
    (by norm_num) (by norm_num) hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NC NG), by omega, ?_⟩
  intro N hN L hband i j
  have hgeom := hg N (by omega) L hband
  have hNtwo : 2 ≤ N := by omega
  have hLN : L ≤ N := by omega
  have hvalues : ∀ k, ∀ x ∈ range (12 * N + 1), ∀ v ∈ blocks N a b L t i j k x,
      (1 / 2 : ℝ) * N ≤ v ∧ (v : ℝ) ≤ 12 * N := by
    intro k x _hx v hv
    revert hv
    refine Fin.cases ?_ (fun l ↦ ?_) k
    · intro hv
      obtain ⟨xy, hxy, hv⟩ := mem_biUnion.mp hv
      obtain ⟨hx, hy, _⟩ := mem_sourcePairs.mp (mem_filter.mp hxy).1
      rcases mem_union.mp hv with hv | hv
      · exact CompressedSourceBlocks.normalized_heights hNtwo hLN hx (by omega) hb4 hv
      · exact CompressedSourceBlocks.normalized_heights hNtwo hLN hy ha (hab.trans hb4) hv
    · intro hv
      change v ∈ (if x ∈ dyadicBlock N then NormalizedWindowSets.values x L else ∅) at hv
      by_cases hx : x ∈ dyadicBlock N
      · rw [ite_eq_left hx] at hv
        have h := (OriginalWindowValueBounds.values_geometry N L x hNtwo (mem_Ico.mp hx) hLN v hv).1
        exact ⟨h.1, h.2.trans (by nlinarith only [Nat.cast_nonneg (α := ℝ) N])⟩
      · simp only [ite_eq_right hx, Finset.notMem_empty] at hv
  have hdist : ∀ k, ∀ x ∈ range (12 * N + 1), ∀ v ∈ blocks N a b L t i j k x,
      (((v : ℤ) - x).natAbs : ℝ) ≤ 8 * (L + 1 : ℕ) := by
    intro k x _hx v hv
    revert hv
    refine Fin.cases ?_ (fun l ↦ ?_) k
    · intro hv
      have h := WindowPairCentreBlocks.block_distance (by omega : 0 < N) hab i j hv
      rw [Int.abs_eq_natAbs] at h
      have hh : ((v : ℤ) - x).natAbs ≤ 2 * b * (L + 1) := by exact_mod_cast h
      exact_mod_cast hh.trans (Nat.mul_le_mul_right (L + 1) (by omega : 2 * b ≤ 8))
    · intro hv
      change v ∈ (if x ∈ dyadicBlock N then NormalizedWindowSets.values x L else ∅) at hv
      by_cases hx : x ∈ dyadicBlock N
      · rw [ite_eq_left hx] at hv
        have h := (OriginalWindowValueBounds.values_geometry N L x hNtwo (mem_Ico.mp hx) hLN v hv).2
        exact_mod_cast h.trans (by omega : L + 1 ≤ 8 * (L + 1))
      · simp only [ite_eq_right hx, Finset.notMem_empty] at hv
  calc
    _ ≤ ((EffectiveWindowLists.lists (range (12 * N + 1)) (blocks N a b L t i j) ∅).card : ℝ) := by
      exact_mod_cast card_le_card_of_injOn (encode b)
        (fun _ hp ↦ encode_mem hNtwo ha hb hb4 i j hp)
        (encode_injective (by omega) ha (by omega) i j)
    _ ≤ (N : ℝ) ^ (((t + 1 : ℕ) : ℝ) / 2 + ε) := by
      simpa only [Finset.univ_eq_empty, biUnion_empty] using
        hc N (by omega) L Fin.elim0 _ _ Fin.elim0 hband hvalues
          (fun k ↦ Fin.elim0 k) hdist (fun k ↦ Fin.elim0 k)
    _ = _ := by norm_num

theorem uniform_count (t a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hb : 3 ≤ b) (hb4 : b ≤ 4) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((points N a b L t).card : ℝ) ≤ (N : ℝ) ^ (((t : ℝ) + 1) / 2 + ε) := by
  classical
  obtain ⟨NC, _hNC, hc⟩ := fixed_offsets t a b ha hab hb hb4 C (ε / 2) (by positivity)
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NP, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (CriticalBandScale.upperScale ^ 2) 2 (ε / 2) (by positivity)
  refine ⟨max 2 (max NC (max NS NP)), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := (hs N (by omega) L hband).2
  have hpoly : ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ ≤ (CriticalBandScale.upperScale * Real.log N) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2
      _ = CriticalBandScale.upperScale ^ 2 * (Real.log N) ^ 2 := mul_pow _ _ _
      _ ≤ _ := by simpa only [Real.rpow_ofNat] using hp N (by omega)
  have hfinite := (card_le_card (offsets_cover N a b L t)).trans card_biUnion_le
  calc
    _ ≤ ∑ ij : Fin (L + 1) × Fin (L + 1), ((fixedPoints N a b L t ij.1 ij.2).card : ℝ) := by
      exact_mod_cast hfinite
    _ ≤ ∑ _ij : Fin (L + 1) × Fin (L + 1), (N : ℝ) ^ (((t : ℝ) + 1) / 2 + ε / 2) :=
      sum_le_sum fun ij _ ↦ hc N (by omega) L hband ij.1 ij.2
    _ = ((L + 1 : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ (((t : ℝ) + 1) / 2 + ε / 2) := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (((t : ℝ) + 1) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.EffectiveCompressedPrimitiveCount
