module

public import PaperP1.Arithmetic.NormalizedPrivateDefects
public import PaperP1.Arithmetic.DyadicEndpointPairs
public import PaperP1.Arithmetic.GlobalDefectCount

/-! # Actual nonprivate normalized source pairs inject into polynomially many defect lists -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedDefectSources

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.GoodEdgeCompression PaperP1.DefectivePredicate
  PaperP1.NormalizedPrivateDefects PaperP1.DyadicEndpointPairs PaperP1.GlobalDefectCount

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def value (a b L : ℕ) (xy : ℕ × ℕ) (k : Fin (L + 1)) (side : Bool) : ℕ :=
  if side then a * startCompleteVertexLabel xy.2 L k else b * startCompleteVertexLabel xy.1 L k

def defectSources (N H a b L : ℕ) (i j k : Fin (L + 1)) (side : Bool) : Finset (ℕ × ℕ) :=
  (sourcePairs N a b L i j).filter fun xy ↦ HDefective H (value a b L xy k side)

def coveredSources (N H a b L : ℕ) : Finset (ℕ × ℕ) :=
  univ.biUnion fun c : (Fin (L + 1) × Fin (L + 1)) × (Fin (L + 1) × Bool) ↦
    defectSources N H a b L c.1.1 c.1.2 c.2.1 c.2.2

def badSources (N H a b L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun xy ↦
    (units a b xy.1 xy.2 L).Nonempty ∧ ¬PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b xy.1 xy.2 L)

theorem value_injective {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (i j k : Fin (L + 1)) (side : Bool) :
    Set.InjOn (fun xy ↦ value a b L xy k side) (sourcePairs N a b L i j) := by
  intro xy hxy uv huv heq
  have hx := hN.trans_le (mem_Ico.mp (mem_sourcePairs.mp hxy).1).1
  have hy := hN.trans_le (mem_Ico.mp (mem_sourcePairs.mp hxy).2.1).1
  have hu := hN.trans_le (mem_Ico.mp (mem_sourcePairs.mp huv).1).1
  have hv := hN.trans_le (mem_Ico.mp (mem_sourcePairs.mp huv).2.1).1
  cases side
  · change b * startCompleteVertexLabel xy.1 L k = b * startCompleteVertexLabel uv.1 L k at heq
    have hl := mul_left_cancel₀ hb.ne' heq
    rw [startCompleteVertexLabel_eq_offset hx, startCompleteVertexLabel_eq_offset hu] at hl
    have hfirst : xy.1 = uv.1 := by omega
    apply first_anchor_injective hN ha hb i j hxy huv
    exact congrArg (fun x : ℕ ↦ b * startCompleteVertexLabel x L i) hfirst
  · change a * startCompleteVertexLabel xy.2 L k = a * startCompleteVertexLabel uv.2 L k at heq
    have hr := mul_left_cancel₀ ha.ne' heq
    rw [startCompleteVertexLabel_eq_offset hy, startCompleteVertexLabel_eq_offset hv] at hr
    have hsecond : xy.2 = uv.2 := by omega
    apply second_anchor_injective hN ha hb i j hxy huv
    exact congrArg (fun y : ℕ ↦ a * startCompleteVertexLabel y L j) hsecond

theorem value_bounds {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    {xy : ℕ × ℕ} (hx : xy.1 ∈ dyadicBlock N) (hy : xy.2 ∈ dyadicBlock N)
    (k : Fin (L + 1)) (side : Bool) : 0 < value a b L xy k side ∧ value a b L xy k side ≤ b * (2 * N + L) := by
  have hx2 : 2 ≤ xy.1 := hN.trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ xy.2 := hN.trans (mem_Ico.mp hy).1
  have hxhi := (mem_Ico.mp hx).2
  have hyhi := (mem_Ico.mp hy).2
  have hk := k.isLt
  cases side
  · change 0 < b * startCompleteVertexLabel xy.1 L k ∧ b * startCompleteVertexLabel xy.1 L k ≤ _
    rw [startCompleteVertexLabel_eq_offset (by omega)]
    constructor
    · exact Nat.mul_pos hb (by omega)
    · exact Nat.mul_le_mul_left b (by omega)
  · change 0 < a * startCompleteVertexLabel xy.2 L k ∧ a * startCompleteVertexLabel xy.2 L k ≤ _
    rw [startCompleteVertexLabel_eq_offset (by omega)]
    constructor
    · exact Nat.mul_pos ha (by omega)
    · exact Nat.mul_le_mul hab (by omega)

theorem defect_sources_card {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (i j k : Fin (L + 1)) (side : Bool) :
    (defectSources N H a b L i j k side).card ≤ (positiveDefectsBelow H (b * (2 * N + L))).card := by
  apply card_le_card_of_injOn (fun xy ↦ value a b L xy k side)
  · intro xy hxy
    obtain ⟨hsource, hdef⟩ := mem_filter.mp hxy
    have hxy' := mem_sourcePairs.mp hsource
    have hv := value_bounds hN ha hb hab hxy'.1 hxy'.2.1 k side
    exact mem_positiveDefectsBelow.mpr ⟨hv.1.ne', hv.2, hdef⟩
  · intro xy hxy uv huv heq
    exact value_injective (by omega) ha hb i j k side (mem_filter.mp hxy).1 (mem_filter.mp huv).1 heq

theorem covered_sources_card {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    (coveredSources N H a b L).card ≤ 2 * (L + 1) ^ 3 * (positiveDefectsBelow H (b * (2 * N + L))).card := by
  calc
    _ ≤ ∑ c : (Fin (L + 1) × Fin (L + 1)) × (Fin (L + 1) × Bool),
        (defectSources N H a b L c.1.1 c.1.2 c.2.1 c.2.2).card := card_biUnion_le
    _ ≤ ∑ _c : (Fin (L + 1) × Fin (L + 1)) × (Fin (L + 1) × Bool),
        (positiveDefectsBelow H (b * (2 * N + L))).card := by
      apply sum_le_sum
      intro c _
      exact defect_sources_card hN ha hb hab _ _ _ _
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      nsmul_eq_mul, Nat.cast_id]; ring

theorem bad_sources_subset {N H a b L : ℕ} (hN : 2 ≤ N) (hb : 0 < b) (hab : a ≤ b)
    (hcut : 2 * b * (L + 1) ≤ H) : badSources N H a b L ⊆ coveredSources N H a b L := by
  intro xy hxy
  obtain ⟨hblock, hunits, hbad⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  have hxpos : 0 < xy.1 := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < xy.2 := by have := (mem_Ico.mp hy).1; omega
  obtain ⟨n, hn, hdef⟩ := normalized_bad_witness hb hab hxpos hypos hunits hcut hbad
  obtain ⟨u, hu⟩ := hunits
  have hsource : xy ∈ sourcePairs N a b L u.1 u.2 := mem_sourcePairs.mpr ⟨hx, hy, mem_units.mp hu⟩
  rcases mem_union.mp hn with hleft | hright
  · change n ∈ (values xy.1 L).image (fun v ↦ b * v) at hleft
    obtain ⟨v, hv, hvn⟩ := mem_image.mp hleft
    obtain ⟨k, hk⟩ := mem_values.mp hv
    apply mem_biUnion.mpr
    refine ⟨((u.1, u.2), (k, false)), mem_univ _, mem_filter.mpr ⟨hsource, ?_⟩⟩
    change HDefective H (b * startCompleteVertexLabel xy.1 L k)
    rw [hk, hvn]
    exact hdef
  · change n ∈ (values xy.2 L).image (fun v ↦ a * v) at hright
    obtain ⟨v, hv, hvn⟩ := mem_image.mp hright
    obtain ⟨k, hk⟩ := mem_values.mp hv
    apply mem_biUnion.mpr
    refine ⟨((u.1, u.2), (k, true)), mem_univ _, mem_filter.mpr ⟨hsource, ?_⟩⟩
    change HDefective H (a * startCompleteVertexLabel xy.2 L k)
    rw [hk, hvn]
    exact hdef

theorem bad_sources_card {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (hcut : 2 * b * (L + 1) ≤ H) :
    (badSources N H a b L).card ≤ 2 * (L + 1) ^ 3 * (positiveDefectsBelow H (b * (2 * N + L))).card :=
  (card_le_card (bad_sources_subset hN hb hab hcut)).trans (covered_sources_card hN ha hb hab)

end PaperP1.NormalizedDefectSources
