module

public import PaperP1.Arithmetic.ChannelMatchDensity
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Basic.Real.Basic

/-! # The literal finite fixed-channel coefficient and its sharp universal bound -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.FixedChannelGamma

open Finset PaperP1.ChannelMatchDensity

def numeratorBound (a b : ℕ) : ℕ := b * (a + b - 1)

def candidates (a b : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (numeratorBound a b)) ×ˢ (Icc 1 (2 * numeratorBound a b))).filter fun cd ↦
    cd.1.Coprime cd.2 ∧ b * cd.2 < 2 * cd.1 ∧ cd.1 < 2 * a * cd.2 ∧ ¬cd.1 ∣ a ∧ ¬cd.1 ∣ b

def values (a b : ℕ) : Finset ℚ := insert (1 / (b : ℚ)) ((candidates a b).image fun cd ↦ density a b cd.1)

def gamma (a b : ℕ) : ℚ := (values a b).max' ⟨_, mem_insert_self _ _⟩

def gammaReal (a b : ℕ) : ℝ := (gamma a b : ℚ)

theorem mem_candidates {a b c d : ℕ} (hb : 1 ≤ b) :
    (c, d) ∈ candidates a b ↔
      1 ≤ c ∧ c ≤ numeratorBound a b ∧ 1 ≤ d ∧ c.Coprime d ∧
        b * d < 2 * c ∧ c < 2 * a * d ∧ ¬c ∣ a ∧ ¬c ∣ b := by
  simp only [candidates, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨hc, hcB⟩, ⟨hd, _⟩⟩, hcop, hlo, hhi, hca, hcb⟩
    exact ⟨hc, hcB, hd, hcop, hlo, hhi, hca, hcb⟩
  · rintro ⟨hc, hcB, hd, hcop, hlo, hhi, hca, hcb⟩
    have hmul : d ≤ b * d := by simpa only [one_mul] using Nat.mul_le_mul_right d hb
    have hdB : d ≤ 2 * numeratorBound a b := by omega
    exact ⟨⟨⟨hc, hcB⟩, ⟨hd, hdB⟩⟩, hcop, hlo, hhi, hca, hcb⟩

theorem ratio_conditions {a b c d : ℕ} (hd : 0 < d) :
    (b : ℚ) / 2 < (c : ℚ) / d ∧ (c : ℚ) / d < 2 * a ↔
      b * d < 2 * c ∧ c < 2 * a * d := by
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 2) hdQ, div_lt_iff₀ hdQ]
  simp only [mul_comm (c : ℚ) 2]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem mem_values_iff_source {a b : ℕ} (hb : 1 ≤ b) (v : ℚ) :
    v ∈ values a b ↔ v = 1 / (b : ℚ) ∨
      ∃ c d : ℕ, 1 ≤ c ∧ c ≤ numeratorBound a b ∧ 1 ≤ d ∧ c.Coprime d ∧
        (b : ℚ) / 2 < (c : ℚ) / d ∧ (c : ℚ) / d < 2 * a ∧
          ¬c ∣ a ∧ ¬c ∣ b ∧ density a b c = v := by
  constructor
  · intro hv
    rcases mem_insert.mp hv with hv | hv
    · exact Or.inl hv
    · obtain ⟨⟨c, d⟩, hcd, rfl⟩ := mem_image.mp hv
      obtain ⟨hc, hcB, hd, hcop, hlo, hhi, hca, hcb⟩ := (mem_candidates hb).mp hcd
      obtain ⟨hloQ, hhiQ⟩ := (ratio_conditions (by omega : 0 < d)).mpr ⟨hlo, hhi⟩
      exact Or.inr ⟨c, d, hc, hcB, hd, hcop, hloQ, hhiQ, hca, hcb, rfl⟩
  · rintro (hv | ⟨c, d, hc, hcB, hd, hcop, hloQ, hhiQ, hca, hcb, heq⟩)
    · exact mem_insert.mpr (Or.inl hv)
    · have hrat := (ratio_conditions (by omega : 0 < d)).mp ⟨hloQ, hhiQ⟩
      exact mem_insert_of_mem (mem_image.mpr ⟨(c, d),
        (mem_candidates hb).mpr ⟨hc, hcB, hd, hcop, hrat.1, hrat.2, hca, hcb⟩, heq⟩)
theorem base_le_gamma (a b : ℕ) : 1 / (b : ℚ) ≤ gamma a b :=
  (values a b).le_max' _ (mem_insert_self _ _)

theorem density_le_gamma {a b c d : ℕ} (hcd : (c, d) ∈ candidates a b) : density a b c ≤ gamma a b :=
  (values a b).le_max' _ (mem_insert_of_mem (mem_image.mpr ⟨(c, d), hcd, rfl⟩))

theorem density_le_gamma_of_conditions {a b c d : ℕ} (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hcB : c ≤ numeratorBound a b) (hd : 1 ≤ d) (hcop : c.Coprime d)
    (hlo : b * d < 2 * c) (hhi : c < 2 * a * d) (hca : ¬c ∣ a) (hcb : ¬c ∣ b) :
    density a b c ≤ gamma a b :=
  density_le_gamma ((mem_candidates hb).mpr ⟨hc, hcB, hd, hcop, hlo, hhi, hca, hcb⟩)

theorem gamma_le_two_thirds {a b : ℕ} (hab : a.Coprime b) (hb : 3 ≤ b) : gamma a b ≤ 2 / 3 := by
  apply (values a b).max'_le
  intro v hv
  rcases mem_insert.mp hv with hv | hv
  · subst v
    apply (div_le_iff₀ (by exact_mod_cast (show 0 < b by omega) : (0 : ℚ) < b)).mpr
    have hbQ : (3 : ℚ) ≤ b := by exact_mod_cast hb
    nlinarith
  · obtain ⟨⟨c, d⟩, hcd, rfl⟩ := mem_image.mp hv
    obtain ⟨hc, _, _, _, _, _, hca, hcb⟩ := (mem_candidates (by omega : 1 ≤ b)).mp hcd
    exact density_le_two_thirds hab hc hca hcb

theorem gamma_le {a b : ℕ} {v : ℚ} (hbase : 1 / (b : ℚ) ≤ v)
    (hvalues : ∀ cd ∈ candidates a b, density a b cd.1 ≤ v) : gamma a b ≤ v := by
  apply (values a b).max'_le
  intro w hw
  rcases mem_insert.mp hw with hw | hw
  · simpa only [hw] using hbase
  · obtain ⟨cd, hcd, rfl⟩ := mem_image.mp hw
    exact hvalues cd hcd

theorem two_three_density_bound {c d : ℕ} (hcd : (c, d) ∈ candidates 2 3) : density 2 3 c ≤ 1 / 3 := by
  obtain ⟨hc, hcB, hd, hcop, hlo, hhi, hca, hcb⟩ := (mem_candidates (by norm_num : 1 ≤ 3)).mp hcd
  norm_num [numeratorBound] at hcB
  interval_cases c <;> norm_num [density] at *
  all_goals
    have hd3 : d ≤ 3 := by omega
    interval_cases d <;> norm_num at *

theorem three_four_density_bound {c d : ℕ} (hcd : (c, d) ∈ candidates 3 4) : density 3 4 c ≤ 1 / 2 := by
  obtain ⟨hc, hcB, hd, hcop, hlo, hhi, hca, hcb⟩ := (mem_candidates (by norm_num : 1 ≤ 4)).mp hcd
  norm_num [numeratorBound] at hcB
  interval_cases c <;> norm_num [density] at *
  all_goals
    have hd2 : d ≤ 2 := by omega
    interval_cases d; norm_num at *

theorem gamma_two_three : gamma 2 3 = 1 / 3 := by
  exact le_antisymm (gamma_le le_rfl (fun _ h ↦ two_three_density_bound h)) (base_le_gamma 2 3)

theorem gamma_three_four : gamma 3 4 = 1 / 2 := by
  apply le_antisymm (gamma_le (by norm_num) (fun _ h ↦ three_four_density_bound h))
  have hcd : (8, 3) ∈ candidates 3 4 := by
    apply (mem_candidates (by norm_num : 1 ≤ 4)).mpr
    norm_num [numeratorBound]
  have h := density_le_gamma hcd
  have hden : density 3 4 8 = 1 / 2 := by norm_num [density]
  rw [hden] at h
  exact h

theorem gamma_eight_nine : gamma 8 9 = 2 / 3 := by
  apply le_antisymm (gamma_le_two_thirds (a := 8) (b := 9) (by norm_num) (by norm_num))
  have h := density_le_gamma_of_conditions (a := 8) (b := 9) (c := 6) (d := 1)
    (by norm_num) (by norm_num) (by norm_num [numeratorBound]) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hden : density 8 9 6 = 2 / 3 := by norm_num [density]
  rw [hden] at h
  exact h

/-- The bound is attained by a genuine admissible fixed channel. -/
theorem universal_bound_attained :
    ∃ a b : ℕ, a.Coprime b ∧ 3 ≤ b ∧ b < 2 * a ∧ a < b ∧ gamma a b = 2 / 3 := by
  exact ⟨8, 9, by norm_num, by norm_num, by norm_num, by norm_num, gamma_eight_nine⟩

theorem isGreatest_real_values (a b : ℕ) :
    IsGreatest ((fun q : ℚ ↦ (q : ℝ)) '' (values a b : Set ℚ)) (gammaReal a b) := by
  refine ⟨⟨gamma a b, (values a b).max'_mem _, rfl⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact Rat.cast_le.mpr ((values a b).le_max' q hq)

theorem gammaReal_le_two_thirds {a b : ℕ} (hab : a.Coprime b) (hb : 3 ≤ b) :
    gammaReal a b ≤ 2 / 3 := by
  have h := (Rat.cast_le (K := ℝ)).mpr (gamma_le_two_thirds hab hb)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem gammaReal_two_three : gammaReal 2 3 = 1 / 3 := by
  rw [gammaReal, gamma_two_three]
  norm_num

theorem gammaReal_three_four : gammaReal 3 4 = 1 / 2 := by
  rw [gammaReal, gamma_three_four]
  norm_num

theorem gammaReal_eight_nine : gammaReal 8 9 = 2 / 3 := by
  rw [gammaReal, gamma_eight_nine]
  norm_num

end PaperP1.FixedChannelGamma
