module

public import PaperP1.Arithmetic.ActualSourceTranslations

/-! # Literal channel translations on an arbitrary interval of starts

The endpoints need not be dyadic. Counts retain the lower endpoint and
both orientations, including every actual complete-window vertex.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntervalSourceTranslations

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount
  PaperP1.SourceTranslationInterval

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def translations (lo hi a b : ℕ) (u v : ℤ) : Finset ℤ :=
  Ico ⌈lower lo a u⌉ ⌈lower hi b v⌉

def sourcePairs (lo hi a b L : ℕ) (i j : Fin (L + 1)) : Finset (ℕ × ℕ) :=
  ((Ico lo hi) ×ˢ (Ico lo hi)).filter fun xy ↦
    b * startCompleteVertexLabel xy.1 L i = a * startCompleteVertexLabel xy.2 L j

def symmetricSources (lo hi a b L : ℕ) (i j : Fin (L + 1)) : Finset (ℕ × ℕ) :=
  sourcePairs lo hi a b L i j ∪ (sourcePairs lo hi a b L i j).image Prod.swap

theorem lower_upper_order {lo hi a b B : ℕ} {u v : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hwidth : b * lo + (a + b) * B ≤ a * hi) (hu : |u| ≤ B) (hv : |v| ≤ B) :
    lower lo a u ≤ lower hi b v := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hw : (b : ℚ) * lo + ((a : ℚ) + b) * B ≤ a * hi := by exact_mod_cast hwidth
  have huQ : |(u : ℚ)| ≤ B := by exact_mod_cast hu
  have hvQ : |(v : ℚ)| ≤ B := by exact_mod_cast hv
  have hbu := mul_le_mul_of_nonneg_left (abs_le.mp huQ).2 hbQ.le
  have hav := mul_le_mul_of_nonneg_left (abs_le.mp hvQ).1 haQ.le
  apply (div_le_div_iff₀ haQ hbQ).mpr
  nlinarith only [hw, hbu, hav]

theorem mem_translations {lo hi a b B : ℕ} {u v t : ℤ} (ha : 0 < a) (hab : a < b)
    (hlohi : lo ≤ hi) (hlarge : (a + b) * B ≤ lo) (hu : |u| ≤ B) (hv : |v| ≤ B) :
    t ∈ translations lo hi a b u v ↔
      (lo : ℤ) ≤ (a : ℤ) * t - u ∧ (a : ℤ) * t - u < hi ∧
      (lo : ℤ) ≤ (b : ℤ) * t - v ∧ (b : ℤ) * t - v < hi := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast ha.trans hab
  have hloOrder := (ordered_bounds ha hab hlarge hu hv).1
  have hhiOrder := (ordered_bounds ha hab (hlarge.trans hlohi) hu hv).1
  rw [translations, mem_Ico, Int.ceil_le, Int.lt_ceil]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hXlo := (div_le_iff₀ haQ).mp hlo
    have hYhi := (lt_div_iff₀ hbQ).mp hhi
    have hYlo := (div_le_iff₀ hbQ).mp (hloOrder.trans hlo)
    have hXhi := (lt_div_iff₀ haQ).mp (hhi.trans_le hhiOrder)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : (lo : ℚ) ≤ (a : ℚ) * t - u := by linarith only [hXlo]
      exact_mod_cast h
    · have h : (a : ℚ) * t - u < hi := by linarith only [hXhi]
      exact_mod_cast h
    · have h : (lo : ℚ) ≤ (b : ℚ) * t - v := by linarith only [hYlo]
      exact_mod_cast h
    · have h : (b : ℚ) * t - v < hi := by linarith only [hYhi]
      exact_mod_cast h
  · rintro ⟨hxlo, _, _, hyhi⟩
    constructor
    · apply (div_le_iff₀ haQ).mpr
      have h : (lo : ℚ) ≤ (a : ℚ) * t - u := by exact_mod_cast hxlo
      linarith only [h]
    · apply (lt_div_iff₀ hbQ).mpr
      have h : (b : ℚ) * t - v < hi := by exact_mod_cast hyhi
      linarith only [h]

theorem translation_count_error {lo hi a b B : ℕ} {u v : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hwidth : b * lo + (a + b) * B ≤ a * hi) (hu : |u| ≤ B) (hv : |v| ≤ B) :
    |((translations lo hi a b u v).card : ℚ) - ((hi : ℚ) / b - (lo : ℚ) / a)| ≤
      (B : ℚ) / a + (B : ℚ) / b + 1 := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hinter := rational_interval_error (lower lo a u) (lower hi b v)
    (lower_upper_order ha hb hwidth hu hv)
  have huQ : |(u : ℚ)| ≤ B := by exact_mod_cast hu
  have hvQ : |(v : ℚ)| ≤ B := by exact_mod_cast hv
  have hshift : |(v : ℚ) / b - (u : ℚ) / a| ≤ (B : ℚ) / b + (B : ℚ) / a := by
    calc
      _ ≤ |(v : ℚ) / b| + |-(u : ℚ) / a| := by
        simpa only [sub_eq_add_neg, neg_div] using abs_add_le ((v : ℚ) / b) (-((u : ℚ) / a))
      _ = |(v : ℚ)| / b + |(u : ℚ)| / a := by
        rw [abs_div, abs_div, abs_neg, abs_of_pos hbQ, abs_of_pos haQ]
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hvQ hbQ.le) (div_le_div_of_nonneg_right huQ haQ.le)
  have hdiff : lower hi b v - lower lo a u =
      ((hi : ℚ) / b - (lo : ℚ) / a) + ((v : ℚ) / b - (u : ℚ) / a) := by unfold lower; ring
  calc
    _ = |(((translations lo hi a b u v).card : ℚ) - (lower hi b v - lower lo a u)) +
        ((v : ℚ) / b - (u : ℚ) / a)| := by rw [hdiff]; congr 1; ring
    _ ≤ |((translations lo hi a b u v).card : ℚ) - (lower hi b v - lower lo a u)| +
        |(v : ℚ) / b - (u : ℚ) / a| := abs_add_le _ _
    _ ≤ _ := by
      change |((Ico ⌈lower lo a u⌉ ⌈lower hi b v⌉).card : ℚ) - (lower hi b v - lower lo a u)| + _ ≤ _
      linarith only [hinter, hshift]


open PaperP1.ActualSourceTranslations (sourceAt)

theorem mem_sourcePairs {lo hi a b L : ℕ} {i j : Fin (L + 1)} {xy : ℕ × ℕ} :
    xy ∈ sourcePairs lo hi a b L i j ↔ xy.1 ∈ Ico lo hi ∧ xy.2 ∈ Ico lo hi ∧
      b * startCompleteVertexLabel xy.1 L i = a * startCompleteVertexLabel xy.2 L j := by
  simp only [sourcePairs, mem_filter, mem_product, and_assoc]

theorem sourceAt_cast {lo hi a b B : ℕ} {u v t : ℤ} (ha : 0 < a) (hab : a < b)
    (hlohi : lo ≤ hi) (hlarge : (a + b) * B ≤ lo) (hu : |u| ≤ B) (hv : |v| ≤ B)
    (ht : t ∈ translations lo hi a b u v) :
    ((sourceAt a b u v t).1 : ℤ) = (a : ℤ) * t - u ∧
      ((sourceAt a b u v t).2 : ℤ) = (b : ℤ) * t - v := by
  obtain ⟨hxlo, _, hylo, _⟩ := (mem_translations ha hab hlohi hlarge hu hv).mp ht
  exact ⟨Int.toNat_of_nonneg ((Nat.cast_nonneg lo).trans hxlo),
    Int.toNat_of_nonneg ((Nat.cast_nonneg lo).trans hylo)⟩

theorem sourceAt_mem {lo hi a b L : ℕ} (hlo : 2 ≤ lo) (ha : 0 < a) (hab : a < b)
    (hlohi : lo ≤ hi) (hlarge : (a + b) * (L + 1) ≤ lo) (i j : Fin (L + 1))
    {t : ℤ} (ht : t ∈ translations lo hi a b (offset i) (offset j)) :
    sourceAt a b (offset i) (offset j) t ∈ sourcePairs lo hi a b L i j := by
  have hu := EnlargedPairGeometry.offset_abs i
  have hv := EnlargedPairGeometry.offset_abs j
  have hcast := sourceAt_cast ha hab hlohi hlarge hu hv ht
  obtain ⟨hxlo, hxhi, hylo, hyhi⟩ := (mem_translations ha hab hlohi hlarge hu hv).mp ht
  rw [← hcast.1] at hxlo hxhi
  rw [← hcast.2] at hylo hyhi
  have hx : (sourceAt a b (offset i) (offset j) t).1 ∈ Ico lo hi :=
    mem_Ico.mpr ⟨by exact_mod_cast hxlo, by exact_mod_cast hxhi⟩
  have hy : (sourceAt a b (offset i) (offset j) t).2 ∈ Ico lo hi :=
    mem_Ico.mpr ⟨by exact_mod_cast hylo, by exact_mod_cast hyhi⟩
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

theorem sourceAt_injective {lo hi a b B : ℕ} {u v : ℤ} (ha : 0 < a) (hab : a < b)
    (hlohi : lo ≤ hi) (hlarge : (a + b) * B ≤ lo) (hu : |u| ≤ B) (hv : |v| ≤ B) :
    Set.InjOn (sourceAt a b u v) (translations lo hi a b u v : Set ℤ) := by
  intro t ht z hz heq
  have hcastT := (sourceAt_cast ha hab hlohi hlarge hu hv ht).1
  have hcastZ := (sourceAt_cast ha hab hlohi hlarge hu hv hz).1
  have hfirst := congrArg (fun xy : ℕ × ℕ ↦ (xy.1 : ℤ)) heq
  rw [hcastT, hcastZ] at hfirst
  have hprod : (a : ℤ) * t = (a : ℤ) * z := by linarith only [hfirst]
  exact mul_left_cancel₀ (by exact_mod_cast ha.ne' : (a : ℤ) ≠ 0) hprod

theorem translations_card {lo hi a b L : ℕ} (hlo : 2 ≤ lo) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlohi : lo ≤ hi) (hlarge : (a + b) * (L + 1) ≤ lo) (i j : Fin (L + 1)) :
    (translations lo hi a b (offset i) (offset j)).card = (sourcePairs lo hi a b L i j).card := by
  apply card_bij (fun t _ ↦ sourceAt a b (offset i) (offset j) t)
  · intro t ht
    exact sourceAt_mem hlo ha hab hlohi hlarge i j ht
  · intro t ht z hz heq
    exact sourceAt_injective ha hab hlohi hlarge (EnlargedPairGeometry.offset_abs i)
      (EnlargedPairGeometry.offset_abs j) ht hz heq
  · intro xy hxy
    obtain ⟨hx, hy, hunit⟩ := mem_sourcePairs.mp hxy
    have hx2 : 2 ≤ xy.1 := hlo.trans (mem_Ico.mp hx).1
    have hy2 : 2 ≤ xy.2 := hlo.trans (mem_Ico.mp hy).1
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
    · apply (mem_translations ha hab hlohi hlarge (EnlargedPairGeometry.offset_abs i)
        (EnlargedPairGeometry.offset_abs j)).mpr
      rw [hX, hY]
      exact ⟨by exact_mod_cast (mem_Ico.mp hx).1, by exact_mod_cast (mem_Ico.mp hx).2,
        by exact_mod_cast (mem_Ico.mp hy).1, by exact_mod_cast (mem_Ico.mp hy).2⟩
    · apply Prod.ext
      · change ((a : ℤ) * t - offset i).toNat = xy.1
        rw [hX, Int.toNat_natCast]
      · change ((b : ℤ) * t - offset j).toNat = xy.2
        rw [hY, Int.toNat_natCast]

theorem source_card_error {lo hi a b L : ℕ} (hlo : 2 ≤ lo) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlohi : lo ≤ hi) (hlarge : (a + b) * (L + 1) ≤ lo)
    (hwidth : b * lo + (a + b) * (L + 1) ≤ a * hi) (i j : Fin (L + 1)) :
    |((sourcePairs lo hi a b L i j).card : ℚ) - ((hi : ℚ) / b - (lo : ℚ) / a)| ≤
      ((L + 1 : ℕ) : ℚ) / a + ((L + 1 : ℕ) : ℚ) / b + 1 := by
  rw [← translations_card hlo ha hab hcop hlohi hlarge i j]
  exact translation_count_error ha (ha.trans hab) hwidth
    (EnlargedPairGeometry.offset_abs i) (EnlargedPairGeometry.offset_abs j)


theorem source_pair_separated {lo hi a b L : ℕ} (hlo : 0 < lo) (hab : a < b)
    (hlarge : (a + b) * (L + 1) + a * L < lo) (i j : Fin (L + 1)) {xy : ℕ × ℕ}
    (hxy : xy ∈ sourcePairs lo hi a b L i j) : xy.1 + L < xy.2 := by
  obtain ⟨hx, hy, hunit⟩ := mem_sourcePairs.mp hxy
  have hxpos := hlo.trans_le (mem_Ico.mp hx).1
  have hypos := hlo.trans_le (mem_Ico.mp hy).1
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
  have hlargeZ : ((a + b : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ) + (a : ℤ) * L < lo := by exact_mod_cast hlarge
  have hxlo : (lo : ℤ) ≤ xy.1 := by exact_mod_cast (mem_Ico.mp hx).1
  by_contra hnot
  have hrev : (xy.2 : ℤ) ≤ (xy.1 : ℤ) + L := by exact_mod_cast (show xy.2 ≤ xy.1 + L by omega)
  have hrevA := mul_le_mul_of_nonneg_left hrev (Nat.cast_nonneg (α := ℤ) a)
  push_cast at hlargeZ hbu hav
  nlinarith only [hunitZ, hgapX, hbu, hav, hlargeZ, hxlo, hrevA]

theorem symmetric_card {lo hi a b L : ℕ} (hlo : 0 < lo) (hab : a < b)
    (hlarge : (a + b) * (L + 1) + a * L < lo) (i j : Fin (L + 1)) :
    (symmetricSources lo hi a b L i j).card = 2 * (sourcePairs lo hi a b L i j).card := by
  have hdis : Disjoint (sourcePairs lo hi a b L i j) ((sourcePairs lo hi a b L i j).image Prod.swap) := by
    apply disjoint_left.mpr
    intro xy hxy hswap
    obtain ⟨uv, huv, heq⟩ := mem_image.mp hswap
    have hforward := source_pair_separated hlo hab hlarge i j hxy
    have hback := source_pair_separated hlo hab hlarge i j huv
    rw [← heq] at hforward
    change uv.2 + L < uv.1 at hforward
    omega
  have hinj : Function.Injective (Prod.swap : (ℕ × ℕ) → ℕ × ℕ) := by
    intro xy uv heq
    have hh := congrArg Prod.swap heq
    simpa only [Prod.swap_swap] using hh
  rw [symmetricSources, card_union_of_disjoint hdis, card_image_of_injective _ hinj]
  omega

theorem symmetric_card_error {lo hi a b L : ℕ} (hlo : 2 ≤ lo) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlohi : lo ≤ hi) (hlarge : (a + b) * (L + 1) + a * L < lo)
    (hwidth : b * lo + (a + b) * (L + 1) ≤ a * hi) (i j : Fin (L + 1)) :
    |((symmetricSources lo hi a b L i j).card : ℚ) - 2 * ((hi : ℚ) / b - (lo : ℚ) / a)| ≤
      2 * (((L + 1 : ℕ) : ℚ) / a + ((L + 1 : ℕ) : ℚ) / b + 1) := by
  have hcount := source_card_error hlo ha hab hcop hlohi (by omega) hwidth i j
  rw [symmetric_card (by omega : 0 < lo) hab hlarge i j, Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ = |(2 : ℚ) * (((sourcePairs lo hi a b L i j).card : ℚ) - ((hi : ℚ) / b - (lo : ℚ) / a))| := by congr 1; ring
    _ = 2 * |((sourcePairs lo hi a b L i j).card : ℚ) - ((hi : ℚ) / b - (lo : ℚ) / a)| := by rw [abs_mul]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hcount (by norm_num)

end PaperP1.IntervalSourceTranslations
