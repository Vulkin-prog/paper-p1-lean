module

public import PaperP1.Arithmetic.SourceTranslationInterval
public import PaperP1.Arithmetic.DyadicEndpointPairs
public import PaperP1.Arithmetic.ExactMatchCongruences
public import PaperP1.Arithmetic.EnlargedPairGeometry

/-! # Actual source pairs are in bijection with their dyadic integer translations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualSourceTranslations

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedUnitCount
  PaperP1.SourceTranslationInterval PaperP1.DyadicEndpointPairs

def sourceAt (a b : ℕ) (u v t : ℤ) : ℕ × ℕ :=
  (((a : ℤ) * t - u).toNat, ((b : ℤ) * t - v).toNat)

theorem sourceAt_cast {N a b B : ℕ} {u v t : ℤ} (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * B ≤ N) (hu : |u| ≤ B) (hv : |v| ≤ B)
    (ht : t ∈ translations N a b u v) :
    ((sourceAt a b u v t).1 : ℤ) = (a : ℤ) * t - u ∧
      ((sourceAt a b u v t).2 : ℤ) = (b : ℤ) * t - v := by
  obtain ⟨hxlo, _, hylo, _⟩ := (mem_translations ha hab hlarge hu hv).mp ht
  exact ⟨Int.toNat_of_nonneg ((Nat.cast_nonneg N).trans hxlo),
    Int.toNat_of_nonneg ((Nat.cast_nonneg N).trans hylo)⟩

theorem sourceAt_mem {N a b L : ℕ} (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) ≤ N) (i j : Fin (L + 1))
    {t : ℤ} (ht : t ∈ translations N a b (offset i) (offset j)) :
    sourceAt a b (offset i) (offset j) t ∈ sourcePairs N a b L i j := by
  have hu := EnlargedPairGeometry.offset_abs i
  have hv := EnlargedPairGeometry.offset_abs j
  have hcast := sourceAt_cast ha hab hlarge hu hv ht
  obtain ⟨hxlo, hxhi, hylo, hyhi⟩ := (mem_translations ha hab hlarge hu hv).mp ht
  rw [← hcast.1] at hxlo hxhi
  rw [← hcast.2] at hylo hyhi
  have hx : (sourceAt a b (offset i) (offset j) t).1 ∈ dyadicBlock N := by
    exact mem_Ico.mpr ⟨by exact_mod_cast hxlo, by exact_mod_cast hxhi⟩
  have hy : (sourceAt a b (offset i) (offset j) t).2 ∈ dyadicBlock N := by
    exact mem_Ico.mpr ⟨by exact_mod_cast hylo, by exact_mod_cast hyhi⟩
  have hxpos : 0 < (sourceAt a b (offset i) (offset j) t).1 := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < (sourceAt a b (offset i) (offset j) t).2 := by have := (mem_Ico.mp hy).1; omega
  have hX : (startCompleteVertexLabel (sourceAt a b (offset i) (offset j) t).1 L i : ℤ) = (a : ℤ) * t := by
    rw [label_cast hxpos, hcast.1]
    ring
  have hY : (startCompleteVertexLabel (sourceAt a b (offset i) (offset j) t).2 L j : ℤ) = (b : ℤ) * t := by
    rw [label_cast hypos, hcast.2]
    ring
  apply mem_sourcePairs.mpr
  refine ⟨hx, hy, ?_⟩
  have hunit : (b : ℤ) * (startCompleteVertexLabel (sourceAt a b (offset i) (offset j) t).1 L i : ℤ) =
      (a : ℤ) * (startCompleteVertexLabel (sourceAt a b (offset i) (offset j) t).2 L j : ℤ) := by
    rw [hX, hY]
    ring
  exact_mod_cast hunit

theorem sourceAt_injective {N a b B : ℕ} {u v : ℤ} (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * B ≤ N) (hu : |u| ≤ B) (hv : |v| ≤ B) :
    Set.InjOn (sourceAt a b u v) (translations N a b u v : Set ℤ) := by
  intro t ht s hs heq
  have hcastT := (sourceAt_cast ha hab hlarge hu hv ht).1
  have hcastS := (sourceAt_cast ha hab hlarge hu hv hs).1
  have hfirst := congrArg (fun xy : ℕ × ℕ ↦ (xy.1 : ℤ)) heq
  rw [hcastT, hcastS] at hfirst
  have hprod : (a : ℤ) * t = (a : ℤ) * s := by linarith only [hfirst]
  exact mul_left_cancel₀ (by exact_mod_cast ha.ne' : (a : ℤ) ≠ 0) hprod

theorem translations_card {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) ≤ N) (i j : Fin (L + 1)) :
    (translations N a b (offset i) (offset j)).card = (sourcePairs N a b L i j).card := by
  apply card_bij (fun t _ ↦ sourceAt a b (offset i) (offset j) t)
  · intro t ht
    exact sourceAt_mem ha hab hlarge i j ht
  · intro t ht s hs heq
    exact sourceAt_injective ha hab hlarge (EnlargedPairGeometry.offset_abs i)
      (EnlargedPairGeometry.offset_abs j) ht hs heq
  · intro xy hxy
    obtain ⟨hx, hy, hunit⟩ := mem_sourcePairs.mp hxy
    have hx2 : 2 ≤ xy.1 := hN.trans (mem_Ico.mp hx).1
    have hy2 : 2 ≤ xy.2 := hN.trans (mem_Ico.mp hy).1
    obtain ⟨t, _, hbaseX, hbaseY⟩ := ExactMatchCongruences.source_parameter ha hcop hx2 i j hunit
    have hX : (a : ℤ) * t - offset i = (xy.1 : ℤ) := by
      have h : (xy.1 : ℤ) + offset i = (a : ℤ) * t := by
        rw [← label_cast (by omega : 0 < xy.1)]
        exact_mod_cast hbaseX
      linarith only [h]
    have hY : (b : ℤ) * t - offset j = (xy.2 : ℤ) := by
      have h : (xy.2 : ℤ) + offset j = (b : ℤ) * t := by
        rw [← label_cast (by omega : 0 < xy.2)]
        exact_mod_cast hbaseY
      linarith only [h]
    refine ⟨(t : ℤ), ?_, ?_⟩
    · apply (mem_translations ha hab hlarge (EnlargedPairGeometry.offset_abs i)
        (EnlargedPairGeometry.offset_abs j)).mpr
      rw [hX, hY]
      exact ⟨by exact_mod_cast (mem_Ico.mp hx).1, by exact_mod_cast (mem_Ico.mp hx).2,
        by exact_mod_cast (mem_Ico.mp hy).1, by exact_mod_cast (mem_Ico.mp hy).2⟩
    · apply Prod.ext
      · change ((a : ℤ) * t - offset i).toNat = xy.1
        rw [hX, Int.toNat_natCast]
      · change ((b : ℤ) * t - offset j).toNat = xy.2
        rw [hY, Int.toNat_natCast]

theorem source_card_error {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) ≤ N)
    (i j : Fin (L + 1)) :
    |((sourcePairs N a b L i j).card : ℚ) - (N : ℚ) * (2 / (b : ℚ) - 1 / (a : ℚ))| ≤
      ((L + 1 : ℕ) : ℚ) / a + ((L + 1 : ℕ) : ℚ) / b + 1 := by
  rw [← translations_card hN ha hab hcop hlarge i j]
  exact translation_count_error ha (ha.trans hab) hinterior hlarge
    (EnlargedPairGeometry.offset_abs i) (EnlargedPairGeometry.offset_abs j)

theorem source_pair_order {N a b L : ℕ} (hN : 0 < N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (i j : Fin (L + 1)) {xy : ℕ × ℕ}
    (hxy : xy ∈ sourcePairs N a b L i j) : xy.1 < xy.2 := by
  obtain ⟨hx, hy, hunit⟩ := mem_sourcePairs.mp hxy
  have hxpos := hN.trans_le (mem_Ico.mp hx).1
  have hypos := hN.trans_le (mem_Ico.mp hy).1
  have hunitZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hunit
  push_cast at hunitZ
  rw [label_cast hxpos, label_cast hypos] at hunitZ
  have hgap : (1 : ℤ) ≤ (b : ℤ) - a := by
    have h : (a : ℤ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    linarith only [h]
  have hgapX := mul_le_mul_of_nonneg_right hgap (Nat.cast_nonneg (α := ℤ) xy.1)
  have hbu := mul_le_mul_of_nonneg_left (abs_le.mp (EnlargedPairGeometry.offset_abs i)).1
    (Nat.cast_nonneg (α := ℤ) b)
  have hav := mul_le_mul_of_nonneg_left (abs_le.mp (EnlargedPairGeometry.offset_abs j)).2
    (Nat.cast_nonneg (α := ℤ) a)
  have hlargeZ : ((a + b : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ) < N := by exact_mod_cast hlarge
  have hxN : (N : ℤ) ≤ xy.1 := by exact_mod_cast (mem_Ico.mp hx).1
  by_contra hnot
  have hrev : (xy.2 : ℤ) ≤ xy.1 := by exact_mod_cast (show xy.2 ≤ xy.1 by omega)
  have hrevA := mul_le_mul_of_nonneg_left hrev (Nat.cast_nonneg (α := ℤ) a)
  push_cast at hlargeZ hbu hav
  nlinarith only [hunitZ, hgapX, hbu, hav, hlargeZ, hxN, hrevA]

def symmetricSources (N a b L : ℕ) (i j : Fin (L + 1)) : Finset (ℕ × ℕ) :=
  sourcePairs N a b L i j ∪ (sourcePairs N a b L i j).image Prod.swap

theorem symmetric_card {N a b L : ℕ} (hN : 0 < N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (i j : Fin (L + 1)) :
    (symmetricSources N a b L i j).card = 2 * (sourcePairs N a b L i j).card := by
  have hdisjoint : Disjoint (sourcePairs N a b L i j) ((sourcePairs N a b L i j).image Prod.swap) := by
    apply disjoint_left.mpr
    intro xy hxy hswap
    obtain ⟨uv, huv, heq⟩ := mem_image.mp hswap
    have hforward := source_pair_order hN hab hlarge i j hxy
    have hback := source_pair_order hN hab hlarge i j huv
    rw [← heq] at hforward
    change uv.2 < uv.1 at hforward
    omega
  have hinj : Function.Injective (Prod.swap : (ℕ × ℕ) → ℕ × ℕ) := by
    intro xy uv heq
    have h := congrArg Prod.swap heq
    simpa using h
  rw [symmetricSources, card_union_of_disjoint hdisjoint, card_image_of_injective _ hinj]
  omega

def coefficient (a b : ℕ) : ℚ := 2 * (2 * (a : ℚ) - b) / ((a : ℚ) * b)

theorem coefficient_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    coefficient a b = 2 * (2 / (b : ℚ) - 1 / (a : ℚ)) := by
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold coefficient
  field_simp

theorem leading_coefficients : coefficient 2 3 = 1 / 3 ∧ coefficient 3 4 = 1 / 3 := by
  norm_num [coefficient]

theorem symmetric_card_error {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N)
    (i j : Fin (L + 1)) :
    |((symmetricSources N a b L i j).card : ℚ) - (N : ℚ) * coefficient a b| ≤
      2 * (((L + 1 : ℕ) : ℚ) / a + ((L + 1 : ℕ) : ℚ) / b + 1) := by
  have hcount := source_card_error hN ha hab hinterior hcop hlarge.le i j
  rw [symmetric_card (by omega : 0 < N) hab hlarge i j, Nat.cast_mul, Nat.cast_ofNat,
    coefficient_eq ha (ha.trans hab)]
  calc
    _ = |(2 : ℚ) * (((sourcePairs N a b L i j).card : ℚ) -
        (N : ℚ) * (2 / (b : ℚ) - 1 / (a : ℚ)))| := by congr 1; ring
    _ = 2 * |((sourcePairs N a b L i j).card : ℚ) -
        (N : ℚ) * (2 / (b : ℚ) - 1 / (a : ℚ))| := by rw [abs_mul]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hcount (by norm_num)

theorem simple_errors {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N)
    (i j : Fin (L + 1)) :
    |((sourcePairs N a b L i j).card : ℚ) - (N : ℚ) * (2 / (b : ℚ) - 1 / (a : ℚ))| ≤
      3 * ((L + 1 : ℕ) : ℚ) ∧
    |((symmetricSources N a b L i j).card : ℚ) - (N : ℚ) * coefficient a b| ≤
      6 * ((L + 1 : ℕ) : ℚ) := by
  have hb : 0 < b := ha.trans hab
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have ha1 : (1 : ℚ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hb1 : (1 : ℚ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hB1 : (1 : ℚ) ≤ ((L + 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ L + 1 by omega)
  have hBa : ((L + 1 : ℕ) : ℚ) / a ≤ ((L + 1 : ℕ) : ℚ) := by
    apply (div_le_iff₀ haQ).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 (Nat.cast_nonneg (α := ℚ) (L + 1))
  have hBb : ((L + 1 : ℕ) : ℚ) / b ≤ ((L + 1 : ℕ) : ℚ) := by
    apply (div_le_iff₀ hbQ).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb1 (Nat.cast_nonneg (α := ℚ) (L + 1))
  have hordered := source_card_error hN ha hab hinterior hcop hlarge.le i j
  have hsym := symmetric_card_error hN ha hab hinterior hcop hlarge i j
  exact ⟨by linarith only [hordered, hBa, hBb, hB1], by linarith only [hsym, hBa, hBb, hB1]⟩

end PaperP1.ActualSourceTranslations
