module

public import PaperP1.Arithmetic.IntervalResidueError
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Ring

/-! # Exact dyadic translation intervals and a two-sided finite counting error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceTranslationInterval

open Finset

def lower (N a : ℕ) (u : ℤ) : ℚ := ((N : ℚ) + u) / a

def upper (N b : ℕ) (v : ℤ) : ℚ := (2 * (N : ℚ) + v) / b

def translations (N a b : ℕ) (u v : ℤ) : Finset ℤ := Ico ⌈lower N a u⌉ ⌈upper N b v⌉

theorem rational_interval_error (α β : ℚ) (horder : α ≤ β) :
    |((Ico ⌈α⌉ ⌈β⌉).card : ℚ) - (β - α)| ≤ 1 := by
  have hceil : ⌈α⌉ ≤ ⌈β⌉ := Int.ceil_mono horder
  have hcardZ : ((Ico ⌈α⌉ ⌈β⌉).card : ℤ) = ⌈β⌉ - ⌈α⌉ := Int.card_Ico_of_le _ _ hceil
  have hcard : ((Ico ⌈α⌉ ⌈β⌉).card : ℚ) = (⌈β⌉ : ℚ) - (⌈α⌉ : ℚ) := by exact_mod_cast hcardZ
  have ha := Int.le_ceil α
  have hb := Int.le_ceil β
  have ha' := (Int.ceil_lt_add_one α).le
  have hb' := (Int.ceil_lt_add_one β).le
  rw [hcard]
  exact abs_le.mpr ⟨by linarith only [ha', hb], by linarith only [ha, hb']⟩

theorem ordered_bounds {N a b B : ℕ} {u v : ℤ} (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * B ≤ N) (hu : |u| ≤ B) (hv : |v| ≤ B) :
    lower N b v ≤ lower N a u ∧ upper N b v ≤ upper N a u := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast (ha.trans hab)
  have hgap : (1 : ℚ) ≤ (b : ℚ) - a := by
    have h : (a : ℚ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    linarith only [h]
  have hgapN := mul_le_mul_of_nonneg_right hgap (Nat.cast_nonneg (α := ℚ) N)
  have hN : ((a : ℚ) + b) * B ≤ N := by exact_mod_cast hlarge
  have huQ : |(u : ℚ)| ≤ B := by exact_mod_cast hu
  have hvQ : |(v : ℚ)| ≤ B := by exact_mod_cast hv
  have hbu := mul_le_mul_of_nonneg_left (abs_le.mp huQ).1 hbQ.le
  have hav := mul_le_mul_of_nonneg_left (abs_le.mp hvQ).2 haQ.le
  constructor
  · apply (div_le_div_iff₀ hbQ haQ).mpr
    nlinarith only [hN, hgapN, hbu, hav]
  · apply (div_le_div_iff₀ hbQ haQ).mpr
    nlinarith only [hN, hgapN, hbu, hav, Nat.cast_nonneg (α := ℚ) N]

theorem lower_le_upper {N a b B : ℕ} {u v : ℤ} (ha : 0 < a) (hb : 0 < b) (hinterior : b < 2 * a)
    (hlarge : (a + b) * B ≤ N) (hu : |u| ≤ B) (hv : |v| ≤ B) : lower N a u ≤ upper N b v := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hgap : (1 : ℚ) ≤ 2 * (a : ℚ) - b := by
    have h : (b : ℚ) + 1 ≤ 2 * a := by exact_mod_cast (show b + 1 ≤ 2 * a by omega)
    linarith only [h]
  have hgapN := mul_le_mul_of_nonneg_right hgap (Nat.cast_nonneg (α := ℚ) N)
  have hN : ((a : ℚ) + b) * B ≤ N := by exact_mod_cast hlarge
  have huQ : |(u : ℚ)| ≤ B := by exact_mod_cast hu
  have hvQ : |(v : ℚ)| ≤ B := by exact_mod_cast hv
  have hbu := mul_le_mul_of_nonneg_left (abs_le.mp huQ).2 hbQ.le
  have hav := mul_le_mul_of_nonneg_left (abs_le.mp hvQ).1 haQ.le
  apply (div_le_div_iff₀ haQ hbQ).mpr
  nlinarith only [hN, hgapN, hbu, hav]

theorem mem_translations {N a b B : ℕ} {u v t : ℤ} (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * B ≤ N) (hu : |u| ≤ B) (hv : |v| ≤ B) :
    t ∈ translations N a b u v ↔
      (N : ℤ) ≤ (a : ℤ) * t - u ∧ (a : ℤ) * t - u < 2 * N ∧
      (N : ℤ) ≤ (b : ℤ) * t - v ∧ (b : ℤ) * t - v < 2 * N := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast (ha.trans hab)
  obtain ⟨hloOrder, hhiOrder⟩ := ordered_bounds ha hab hlarge hu hv
  rw [translations, mem_Ico, Int.ceil_le, Int.lt_ceil]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hXlo := (div_le_iff₀ haQ).mp hlo
    have hYhi := (lt_div_iff₀ hbQ).mp hhi
    have hYlo := (div_le_iff₀ hbQ).mp (hloOrder.trans hlo)
    have hXhi := (lt_div_iff₀ haQ).mp (hhi.trans_le hhiOrder)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : (N : ℚ) ≤ (a : ℚ) * t - u := by linarith only [hXlo]
      exact_mod_cast h
    · have h : (a : ℚ) * t - u < 2 * N := by linarith only [hXhi]
      exact_mod_cast h
    · have h : (N : ℚ) ≤ (b : ℚ) * t - v := by linarith only [hYlo]
      exact_mod_cast h
    · have h : (b : ℚ) * t - v < 2 * N := by linarith only [hYhi]
      exact_mod_cast h
  · rintro ⟨hxlo, _, _, hyhi⟩
    constructor
    · apply (div_le_iff₀ haQ).mpr
      have h : (N : ℚ) ≤ (a : ℚ) * t - u := by exact_mod_cast hxlo
      linarith only [h]
    · apply (lt_div_iff₀ hbQ).mpr
      have h : (b : ℚ) * t - v < 2 * N := by exact_mod_cast hyhi
      linarith only [h]

theorem translation_count_error {N a b B : ℕ} {u v : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hinterior : b < 2 * a) (hlarge : (a + b) * B ≤ N) (hu : |u| ≤ B) (hv : |v| ≤ B) :
    |((translations N a b u v).card : ℚ) - (N : ℚ) * (2 / (b : ℚ) - 1 / (a : ℚ))| ≤
      (B : ℚ) / a + (B : ℚ) / b + 1 := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hinterval := rational_interval_error (lower N a u) (upper N b v)
    (lower_le_upper ha hb hinterior hlarge hu hv)
  have huQ : |(u : ℚ)| ≤ B := by exact_mod_cast hu
  have hvQ : |(v : ℚ)| ≤ B := by exact_mod_cast hv
  have hshift : |(v : ℚ) / b - (u : ℚ) / a| ≤ (B : ℚ) / b + (B : ℚ) / a := by
    calc
      _ ≤ |(v : ℚ) / b| + |-(u : ℚ) / a| := by
        simpa only [sub_eq_add_neg, neg_div] using abs_add_le ((v : ℚ) / b) (-((u : ℚ) / a))
      _ = |(v : ℚ)| / b + |(u : ℚ)| / a := by
        rw [abs_div, abs_div, abs_neg, abs_of_pos hbQ, abs_of_pos haQ]
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hvQ hbQ.le) (div_le_div_of_nonneg_right huQ haQ.le)
  have hdiff : upper N b v - lower N a u =
      (N : ℚ) * (2 / (b : ℚ) - 1 / (a : ℚ)) + ((v : ℚ) / b - (u : ℚ) / a) := by
    unfold upper lower
    ring
  calc
    _ = |(((translations N a b u v).card : ℚ) - (upper N b v - lower N a u)) +
        ((v : ℚ) / b - (u : ℚ) / a)| := by rw [hdiff]; congr 1; ring
    _ ≤ |((translations N a b u v).card : ℚ) - (upper N b v - lower N a u)| +
        |(v : ℚ) / b - (u : ℚ) / a| := abs_add_le _ _
    _ ≤ _ := by
      change |((Ico ⌈lower N a u⌉ ⌈upper N b v⌉).card : ℚ) - (upper N b v - lower N a u)| + _ ≤ _
      linarith only [hinterval, hshift]

end PaperP1.SourceTranslationInterval
