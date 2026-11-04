module

public import PaperP1.Arithmetic.NormalizedDefectSources
public import PaperP1.Arithmetic.EnlargedPairGeometry

/-! # Exact defect-pair host counts on the whole positive bounded source interval

The geometric residual replaces an exact-unit witness in the injection.
Thus the count covers the full enlarged alignment, including zero units.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedNormalizedDefectPairs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets
  PaperP1.NormalizedDefectSources PaperP1.DefectivePredicate PaperP1.EnlargedPairGeometry
  PaperP1.GlobalDefectCount

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def atIndex (M H a b L : ℕ) (k : Fin (L + 1)) (side : Bool) : Finset (ℕ × ℕ) :=
  ((Ico 2 M) ×ˢ (Ico 2 M)).filter fun xy ↦
    Geometric a b xy.1 xy.2 L ∧ HDefective H (value a b L xy k side)

def covered (M H a b L : ℕ) : Finset (ℕ × ℕ) :=
  univ.biUnion fun c : Fin (L + 1) × Bool ↦ atIndex M H a b L c.1 c.2

def pairs (M H a b L : ℕ) : Finset (ℕ × ℕ) :=
  ((Ico 2 M) ×ˢ (Ico 2 M)).filter fun xy ↦ Geometric a b xy.1 xy.2 L ∧
    ∃ n ∈ NormalizedWindowSets.union a b xy.1 xy.2 L, HDefective H n

theorem value_bounds {M a b L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    {xy : ℕ × ℕ} (hx : xy.1 ∈ Ico 2 M) (hy : xy.2 ∈ Ico 2 M)
    (k : Fin (L + 1)) (side : Bool) :
    0 < value a b L xy k side ∧ value a b L xy k side ≤ b * (M + L) := by
  have hxI := mem_Ico.mp hx
  have hyI := mem_Ico.mp hy
  have hk := k.isLt
  cases side
  · change 0 < b * startCompleteVertexLabel xy.1 L k ∧ b * startCompleteVertexLabel xy.1 L k ≤ _
    rw [startCompleteVertexLabel_eq_offset (by omega)]
    exact ⟨Nat.mul_pos hb (by omega), Nat.mul_le_mul_left b (by omega)⟩
  · change 0 < a * startCompleteVertexLabel xy.2 L k ∧ a * startCompleteVertexLabel xy.2 L k ≤ _
    rw [startCompleteVertexLabel_eq_offset (by omega)]
    exact ⟨Nat.mul_pos ha (by omega), Nat.mul_le_mul hab (by omega)⟩

theorem key_injective {M a b L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (k : Fin (L + 1)) (side : Bool) :
    Set.InjOn (fun xy : ℕ × ℕ ↦ ((b : ℤ) * xy.1 - (a : ℤ) * xy.2, value a b L xy k side))
      ((Ico 2 M) ×ˢ (Ico 2 M) : Finset (ℕ × ℕ)) := by
  intro xy hxy uv huv heq
  obtain ⟨hx, hy⟩ := mem_product.mp hxy
  obtain ⟨hu, hv⟩ := mem_product.mp huv
  have hxpos : 0 < xy.1 := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < xy.2 := by have := (mem_Ico.mp hy).1; omega
  have hupos : 0 < uv.1 := by have := (mem_Ico.mp hu).1; omega
  have hvpos : 0 < uv.2 := by have := (mem_Ico.mp hv).1; omega
  have hr := congrArg Prod.fst heq
  have hn := congrArg Prod.snd heq
  change (b : ℤ) * xy.1 - (a : ℤ) * xy.2 = (b : ℤ) * uv.1 - (a : ℤ) * uv.2 at hr
  cases side
  · change b * startCompleteVertexLabel xy.1 L k = b * startCompleteVertexLabel uv.1 L k at hn
    have hl := mul_left_cancel₀ hb.ne' hn
    rw [startCompleteVertexLabel_eq_offset hxpos, startCompleteVertexLabel_eq_offset hupos] at hl
    have hfirst : xy.1 = uv.1 := by omega
    have hprod : (a : ℤ) * xy.2 = (a : ℤ) * uv.2 := by rw [hfirst] at hr; linarith only [hr]
    have hsecond : xy.2 = uv.2 := by
      exact_mod_cast mul_left_cancel₀ (by exact_mod_cast ha.ne' : (a : ℤ) ≠ 0) hprod
    exact Prod.ext hfirst hsecond
  · change a * startCompleteVertexLabel xy.2 L k = a * startCompleteVertexLabel uv.2 L k at hn
    have hl := mul_left_cancel₀ ha.ne' hn
    rw [startCompleteVertexLabel_eq_offset hypos, startCompleteVertexLabel_eq_offset hvpos] at hl
    have hsecond : xy.2 = uv.2 := by omega
    have hprod : (b : ℤ) * xy.1 = (b : ℤ) * uv.1 := by rw [hsecond] at hr; linarith only [hr]
    have hfirst : xy.1 = uv.1 := by
      exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hb.ne' : (b : ℤ) ≠ 0) hprod
    exact Prod.ext hfirst hsecond

theorem atIndex_card {M H a b L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (k : Fin (L + 1)) (side : Bool) :
    (atIndex M H a b L k side).card ≤
      (2 * ((a + b) * (L + 1)) + 1) * (positiveDefectsBelow H (b * (M + L))).card := by
  let K := (a + b) * (L + 1)
  let f : ℕ × ℕ → ℤ × ℕ := fun xy ↦ ((b : ℤ) * xy.1 - (a : ℤ) * xy.2, value a b L xy k side)
  have hc : (atIndex M H a b L k side).card ≤
      ((Icc (-(K : ℤ)) K) ×ˢ positiveDefectsBelow H (b * (M + L))).card := by
    apply card_le_card_of_injOn f
    · intro xy hxy
      obtain ⟨hblock, hg, hd⟩ := mem_filter.mp hxy
      obtain ⟨hx, hy⟩ := mem_product.mp hblock
      have hv := value_bounds ha hb hab hx hy k side
      have hg' : |(b : ℤ) * xy.1 - (a : ℤ) * xy.2| ≤ (K : ℤ) := by
        simpa only [Geometric, K, Nat.cast_mul] using hg
      exact mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp hg'), mem_positiveDefectsBelow.mpr ⟨hv.1.ne', hv.2, hd⟩⟩
    · intro xy hxy uv huv heq
      exact key_injective ha hb k side (mem_filter.mp hxy).1 (mem_filter.mp huv).1 heq
  have hK : (Icc (-(K : ℤ)) K).card = 2 * K + 1 := by rw [Int.card_Icc]; omega
  rwa [card_product, hK] at hc

theorem pairs_subset_covered (M H a b L : ℕ) : pairs M H a b L ⊆ covered M H a b L := by
  intro xy hxy
  obtain ⟨hblock, hg, n, hn, hd⟩ := mem_filter.mp hxy
  rcases mem_union.mp hn with hleft | hright
  · change n ∈ (values xy.1 L).image (fun v ↦ b * v) at hleft
    obtain ⟨v, hv, hvn⟩ := mem_image.mp hleft
    obtain ⟨k, hk⟩ := mem_values.mp hv
    apply mem_biUnion.mpr
    refine ⟨(k, false), mem_univ _, mem_filter.mpr ⟨hblock, hg, ?_⟩⟩
    change HDefective H (b * startCompleteVertexLabel xy.1 L k)
    rw [hk, hvn]
    exact hd
  · change n ∈ (values xy.2 L).image (fun v ↦ a * v) at hright
    obtain ⟨v, hv, hvn⟩ := mem_image.mp hright
    obtain ⟨k, hk⟩ := mem_values.mp hv
    apply mem_biUnion.mpr
    refine ⟨(k, true), mem_univ _, mem_filter.mpr ⟨hblock, hg, ?_⟩⟩
    change HDefective H (a * startCompleteVertexLabel xy.2 L k)
    rw [hk, hvn]
    exact hd

theorem covered_card {M H a b L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    (covered M H a b L).card ≤ 2 * (L + 1) * (2 * ((a + b) * (L + 1)) + 1) *
      (positiveDefectsBelow H (b * (M + L))).card := by
  calc
    _ ≤ ∑ c : Fin (L + 1) × Bool, (atIndex M H a b L c.1 c.2).card := card_biUnion_le
    _ ≤ ∑ _c : Fin (L + 1) × Bool,
        (2 * ((a + b) * (L + 1)) + 1) * (positiveDefectsBelow H (b * (M + L))).card := by
      exact sum_le_sum fun _ _ ↦ atIndex_card ha hb hab _ _
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_id]
      ring

theorem pairs_card {M H a b L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    (pairs M H a b L).card ≤ 2 * (L + 1) * (2 * ((a + b) * (L + 1)) + 1) *
      (positiveDefectsBelow H (b * (M + L))).card :=
  (card_le_card (pairs_subset_covered M H a b L)).trans (covered_card ha hb hab)

theorem prefactor_bound {a b L Q : ℕ} (hab : a ≤ b) (hbQ : b ≤ Q) :
    2 * (L + 1) * (2 * ((a + b) * (L + 1)) + 1) ≤ (8 * Q + 2) * (L + 1) ^ 2 := by
  have hsum : a + b ≤ 2 * Q := by omega
  have hm := Nat.mul_le_mul_right (L + 1) hsum
  have hB : 1 ≤ L + 1 := by omega
  calc
    _ ≤ 2 * (L + 1) * (4 * Q * (L + 1) + 1) :=
      Nat.mul_le_mul_left _ (by nlinarith only [hm])
    _ ≤ 2 * (L + 1) * ((4 * Q + 1) * (L + 1)) :=
      Nat.mul_le_mul_left _ (by nlinarith only [hB])
    _ = _ := by ring

end PaperP1.BoundedNormalizedDefectPairs
