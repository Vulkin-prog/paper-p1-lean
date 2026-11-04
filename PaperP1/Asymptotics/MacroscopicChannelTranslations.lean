module

public import PaperP1.Arithmetic.IntervalSourceTranslations
public import PaperP1.Asymptotics.MacroscopicPolynomialScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Exact leading-channel translation counts on the macroscopic interval

The actual complete-vertex source pairs are counted before any signed or
unsigned relation enumeration. The threshold precedes all vertex choices.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicChannelTranslations

open Finset Filter PaperP1.MacroscopicIntervalGeometry PaperP1.IntervalSourceTranslations

theorem uniform_geometry (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      let lo := ⌈(M : ℝ) ^ δ⌉₊
      2 ≤ lo ∧ lo ≤ M ∧ 3 * (L + 1) + L < lo ∧ 2 * lo + 3 * (L + 1) ≤ M := by
  have hlim : Tendsto (fun M : ℕ ↦ (M : ℝ) ^ (δ - 1)) atTop (nhds 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - δ)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨MS, hS⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)))
  obtain ⟨MP, hP⟩ := PaperP1.MacroscopicPolynomialScale.polynomial_lt_source C δ 5 hδ (by norm_num) 1
  refine ⟨max 8 (max MS MP), ?_⟩
  intro M hM L hcrit
  dsimp only
  let lo := ⌈(M : ℝ) ^ δ⌉₊
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast (show 8 ≤ M by omega)
  have hsmall : (M : ℝ) ^ δ < (M : ℝ) / 8 := by
    calc
      _ = (M : ℝ) ^ (δ - 1) * (M : ℝ) := by
        rw [← Real.rpow_add_one hm.ne']
        congr 1
        ring
      _ < (1 / 8 : ℝ) * M := mul_lt_mul_of_pos_right (hS M (by omega)) hm
      _ = _ := by ring
  have hceil : (lo : ℝ) < (M : ℝ) ^ δ + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hm.le δ)
  have hloquarter : (lo : ℝ) ≤ (M : ℝ) / 4 := by linarith only [hsmall, hceil, hM8]
  have hlolt : lo < M := by
    have hh : (lo : ℝ) < M := by linarith only [hloquarter, hm]
    exact_mod_cast hh
  have hlomem : lo ∈ starts M δ := mem_Ico.mpr ⟨le_rfl, hlolt⟩
  have hlo2 := starts_pos (by omega : 2 ≤ M) hδ hlomem
  have hpoly := hP M (by omega) L hcrit lo hlomem
  have hwidth : 5 * (L + 1) < lo := by
    simp only [pow_one] at hpoly
    exact_mod_cast hpoly
  have hlast : 2 * lo + 3 * (L + 1) ≤ M := by
    have hwidthR : (5 : ℝ) * (L + 1 : ℕ) < lo := by exact_mod_cast hwidth
    have hh : (2 : ℝ) * lo + 3 * (L + 1 : ℕ) ≤ M := by linarith only [hwidthR, hloquarter, hm]
    exact_mod_cast hh
  exact ⟨hlo2, hlolt.le, by omega, hlast⟩

theorem one_two_counts (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → ∀ i j : Fin (L + 1),
      let lo := ⌈(M : ℝ) ^ δ⌉₊
      |((sourcePairs lo M 1 2 L i j).card : ℚ) - ((M : ℚ) / 2 - lo)| ≤ 3 * ((L + 1 : ℕ) : ℚ) ∧
      |((symmetricSources lo M 1 2 L i j).card : ℚ) - ((M : ℚ) - 2 * lo)| ≤ 6 * ((L + 1 : ℕ) : ℚ) := by
  obtain ⟨M₀, h⟩ := uniform_geometry C δ hδ hδ1
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit i j
  obtain ⟨hlo, hloM, hlarge, hwidth⟩ := h M hM L hcrit
  let lo := ⌈(M : ℝ) ^ δ⌉₊
  have hsource := source_card_error hlo (by omega : 0 < 1) (by omega : 1 < 2) (by norm_num : Nat.Coprime 1 2)
    hloM (by omega : (1 + 2) * (L + 1) ≤ lo) (by simpa only [one_mul] using hwidth) i j
  have hsym := symmetric_card_error hlo (by omega : 0 < 1) (by omega : 1 < 2) (by norm_num : Nat.Coprime 1 2)
    hloM (by simpa only [one_mul] using hlarge) (by simpa only [one_mul] using hwidth) i j
  have hB : (1 : ℚ) ≤ ((L + 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ L + 1 by omega)
  constructor
  · norm_num only [Nat.cast_one, Nat.cast_ofNat, div_one] at hsource
    exact hsource.trans (by linarith only [hB])
  · norm_num only [Nat.cast_one, Nat.cast_ofNat, div_one] at hsym
    have heq : 2 * ((M : ℚ) / 2 - (lo : ℚ)) = (M : ℚ) - 2 * lo := by ring
    rw [heq] at hsym
    exact hsym.trans (by linarith only [hB])


theorem one_two_real_counts (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → ∀ i j : Fin (L + 1),
      let lo := ⌈(M : ℝ) ^ δ⌉₊
      |((sourcePairs lo M 1 2 L i j).card : ℝ) - ((M : ℝ) / 2 - (M : ℝ) ^ δ)| ≤
        4 * ((L + 1 : ℕ) : ℝ) ∧
      |((symmetricSources lo M 1 2 L i j).card : ℝ) - ((M : ℝ) - 2 * (M : ℝ) ^ δ)| ≤
        8 * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨M₀, h⟩ := one_two_counts C δ hδ hδ1
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit i j
  obtain ⟨hs, ht⟩ := h M hM L hcrit i j
  let lo := ⌈(M : ℝ) ^ δ⌉₊
  have hsR : |((sourcePairs lo M 1 2 L i j).card : ℝ) - ((M : ℝ) / 2 - lo)| ≤
      3 * ((L + 1 : ℕ) : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hs
    norm_num only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat] at hc
    exact hc
  have htR : |((symmetricSources lo M 1 2 L i j).card : ℝ) - ((M : ℝ) - 2 * lo)| ≤
      6 * ((L + 1 : ℕ) : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr ht
    norm_num only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat] at hc
    exact hc
  have hceil : (lo : ℝ) < (M : ℝ) ^ δ + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg M) δ)
  have hlo : (M : ℝ) ^ δ ≤ lo := Nat.le_ceil _
  have hB : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ L + 1 by omega)
  obtain ⟨hslo, hshi⟩ := abs_le.mp hsR
  obtain ⟨htlo, hthi⟩ := abs_le.mp htR
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith only [hslo, hshi, htlo, hthi, hceil, hlo, hB]

theorem one_two_separated (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → ∀ i j : Fin (L + 1),
      ∀ xy ∈ symmetricSources ⌈(M : ℝ) ^ δ⌉₊ M 1 2 L i j, L < Nat.dist xy.1 xy.2 := by
  obtain ⟨M₀, h⟩ := uniform_geometry C δ hδ hδ1
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit i j xy hxy
  obtain ⟨hlo, _hloM, hlarge, _hwidth⟩ := h M hM L hcrit
  have hsep : ∀ uv ∈ sourcePairs ⌈(M : ℝ) ^ δ⌉₊ M 1 2 L i j, uv.1 + L < uv.2 := by
    intro uv huv
    exact source_pair_separated (by omega : 0 < ⌈(M : ℝ) ^ δ⌉₊) (by omega : 1 < 2)
      (by simpa only [one_mul] using hlarge) i j huv
  rcases mem_union.mp hxy with hxy | hxy
  · have hh := hsep xy hxy
    unfold Nat.dist
    omega
  · obtain ⟨uv, huv, rfl⟩ := mem_image.mp hxy
    have hh := hsep uv huv
    change L < Nat.dist uv.2 uv.1
    unfold Nat.dist
    omega

end PaperP1.MacroscopicChannelTranslations
