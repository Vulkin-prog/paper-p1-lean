module

public import PaperP1.Arithmetic.CoprimeIntervalPairs
public import Mathlib.Data.Nat.ModEq

/-! # A quantitative CRT supply of neighboring integers with prescribed square divisors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AdjacentSquareDivisibility

open Finset

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def solutions (N d e : ℕ) : Finset ℕ := (Ico N (2 * N)).filter fun n ↦ d ^ 2 ∣ n ∧ e ^ 2 ∣ n + 1

theorem residue_exists {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hcop : d.Coprime e) :
    ∃ r : ℕ, r < d ^ 2 * e ^ 2 ∧ d ^ 2 ∣ r ∧ e ^ 2 ∣ r + 1 := by
  have hcop2 : (d ^ 2).Coprime (e ^ 2) := hcop.pow 2 2
  let r := Nat.chineseRemainder hcop2 0 (e ^ 2 - 1)
  refine ⟨r.val, Nat.chineseRemainder_lt_mul hcop2 0 (e ^ 2 - 1) (by positivity) (by positivity),
    Nat.modEq_zero_iff_dvd.mp r.prop.1, ?_⟩
  have hh := r.prop.2.add_right 1
  rw [Nat.sub_add_cancel (show 1 ≤ e ^ 2 from Nat.one_le_pow _ _ he)] at hh
  exact Nat.modEq_zero_iff_dvd.mp (hh.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))

theorem residue_progression_count {q r N : ℕ} (hq : 0 < q) (hr : r < q) :
    N / q - 1 ≤ ((Ico N (2 * N)).filter fun n ↦ ∃ k : ℕ, n = r + q * k).card := by
  let Q := N / q
  let f : ℕ → ℕ := fun k ↦ r + q * (Q + 1 + k)
  have hdiv : q * Q ≤ N := by dsimp [Q]; exact Nat.mul_div_le N q
  have hrec := Nat.div_add_mod N q
  have hmod := Nat.mod_lt N hq
  have hf (k : ℕ) (hk : k ∈ range (Q - 1)) :
      f k ∈ (Ico N (2 * N)).filter fun n ↦ ∃ j : ℕ, n = r + q * j := by
    have hk' := mem_range.mp hk
    have hQlo : q * Q + q ≤ q * (Q + 1 + k) := by
      have hh := Nat.mul_le_mul_left q (show Q + 1 ≤ Q + 1 + k by omega)
      nlinarith only [hh]
    have hQhi : q * (Q + 1 + k) + q ≤ 2 * (q * Q) := by
      have hh := Nat.mul_le_mul_left q (show Q + 1 + k + 1 ≤ 2 * Q by omega)
      nlinarith only [hh]
    have hlo : N ≤ f k := by dsimp [f, Q] at *; omega
    have hhi : f k < 2 * N := by dsimp [f]; omega
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hlo, hhi⟩, Q + 1 + k, rfl⟩
  have hinj : Set.InjOn f (range (Q - 1) : Set ℕ) := by
    intro k _ l _ hh
    have hmul : q * (Q + 1 + k) = q * (Q + 1 + l) := Nat.add_left_cancel hh
    have heq := mul_left_cancel₀ hq.ne' hmul
    omega
  have hc := card_le_card_of_injOn f hf hinj
  simpa only [card_range] using hc

theorem solutions_card_lower {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hcop : d.Coprime e) (N : ℕ) :
    N / (d ^ 2 * e ^ 2) - 1 ≤ (solutions N d e).card := by
  obtain ⟨r, hr, hdr, her⟩ := residue_exists hd he hcop
  have hq : 0 < d ^ 2 * e ^ 2 := by positivity
  have hsub : ((Ico N (2 * N)).filter fun n ↦ ∃ k : ℕ, n = r + (d ^ 2 * e ^ 2) * k) ⊆ solutions N d e := by
    intro n hn
    obtain ⟨hinterval, k, rfl⟩ := mem_filter.mp hn
    apply mem_filter.mpr
    refine ⟨hinterval, dvd_add hdr ?_, ?_⟩
    · exact dvd_mul_of_dvd_left (Nat.dvd_mul_right _ _) _
    · rw [show r + d ^ 2 * e ^ 2 * k + 1 = (r + 1) + e ^ 2 * (d ^ 2 * k) by ring]
      exact dvd_add her (dvd_mul_right _ _)
  exact (residue_progression_count hq hr).trans (card_le_card hsub)

theorem uniform_solutions_card_lower {N d e Q : ℕ} (hd : 0 < d) (he : 0 < e)
    (hcop : d.Coprime e) (hQ : 0 < Q) (hqQ : d ^ 2 * e ^ 2 ≤ Q) (hN : 4 * Q ≤ N) :
    (N : ℝ) / (2 * Q) ≤ ((solutions N d e).card : ℝ) := by
  let q := d ^ 2 * e ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hc : N / q ≤ (solutions N d e).card + 1 := by
    have hh := solutions_card_lower hd he hcop N
    change N / q - 1 ≤ (solutions N d e).card at hh
    omega
  have hrem := Nat.mod_lt N hq
  have hrec := Nat.div_add_mod N q
  have hnum : N < q * ((solutions N d e).card + 2) := by
    have hmul := Nat.mul_le_mul_left q hc
    have heq : q * ((solutions N d e).card + 2) = q * ((solutions N d e).card + 1) + q := by ring
    omega
  have hnumQ : N < Q * ((solutions N d e).card + 2) :=
    hnum.trans_le (Nat.mul_le_mul_right _ hqQ)
  have hnumR : (N : ℝ) < (Q : ℝ) * ((solutions N d e).card + 2) := by exact_mod_cast hnumQ
  have hNR : 4 * (Q : ℝ) ≤ N := by exact_mod_cast hN
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Q)).mpr
  nlinarith only [hnumR, hNR]

end PaperP1.AdjacentSquareDivisibility
