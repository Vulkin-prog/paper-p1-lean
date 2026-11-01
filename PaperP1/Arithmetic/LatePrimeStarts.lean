module

public import PaperP1.Arithmetic.PrimeRunStarts
public import PaperP1.Arithmetic.LateWindowPrimes

/-! # The actual late prime-cylinder population and its finite cardinality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LatePrimeStarts

open Finset PaperP1.Model PaperP1.OldValuePrimeBudget

def lower (N q : ℕ) : ℕ := 3 * N / (2 * q) + 5

def length (N q : ℕ) : ℕ := 2 * N / q - lower N q

def parameters (N q : ℕ) : Finset ℕ := Ico (lower N q) (lower N q + length N q)

def goodParameters (N q : ℕ) : Finset ℕ :=
  (parameters N q).filter fun u ↦ ¬q ∣ u ∧ ¬q ∣ u + 1

def starts (N q : ℕ) : Finset ℕ := (goodParameters N q).image fun u ↦ q * u + 1

theorem mem_starts (N q x : ℕ) : x ∈ starts N q ↔
    ∃ u ∈ parameters N q, ¬q ∣ u ∧ ¬q ∣ u + 1 ∧ q * u + 1 = x := by
  simp only [starts, mem_image, goodParameters, mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, hq, hq1⟩, hx⟩
    exact ⟨u, hu, hq, hq1, hx⟩
  · rintro ⟨u, hu, hq, hq1, hx⟩
    exact ⟨u, ⟨hu, hq, hq1⟩, hx⟩

theorem parameter_bounds {N q u : ℕ} (hq : 2 ≤ q) (hu : u ∈ parameters N q) :
    3 * N + 8 * q ≤ 2 * (q * u) ∧ q * (u + 1) ≤ 2 * N := by
  have hq0 : 0 < q := by omega
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp hu
  have huLower : 3 * N / (2 * q) + 5 ≤ u := hlo
  have huUpper : u + 1 ≤ 2 * N / q := by
    unfold length at hhi
    omega
  have hmulLower := Nat.mul_le_mul_left (2 * q) huLower
  have hmod := Nat.mod_add_div (3 * N) (2 * q)
  have hmodlt := Nat.mod_lt (3 * N) (by omega : 0 < 2 * q)
  have hmulUpper := Nat.mul_le_mul_left q huUpper
  have hdivUpper := Nat.div_mul_le_self (2 * N) q
  constructor <;> nlinarith

theorem starts_subset {N q : ℕ} (hq : 2 ≤ q) : starts N q ⊆ dyadicBlock N := by
  intro x hx
  obtain ⟨u, hu, _, _, rfl⟩ := (mem_starts N q x).mp hx
  obtain ⟨hlo, hhi⟩ := parameter_bounds hq hu
  apply mem_Ico.mpr
  constructor <;> nlinarith

theorem starts_late {N q x : ℕ} (hq : 2 ≤ q) (hx : x ∈ starts N q) :
    3 * N + 8 * q ≤ 2 * (x - 1) := by
  obtain ⟨u, hu, _, _, rfl⟩ := (mem_starts N q x).mp hx
  simpa only [Nat.add_sub_cancel] using (parameter_bounds hq hu).1

theorem raw_values_late {N q : ℕ} (hq : 2 ≤ q) {n : ℕ}
    (hn : n ∈ rawValues (starts N q) (q - 1)) : 3 * N ≤ 2 * n ∧ n < 2 * N := by
  obtain ⟨x, hx, hn⟩ := mem_biUnion.mp hn
  obtain ⟨u, hu, _, _, rfl⟩ := (mem_starts N q x).mp hx
  obtain ⟨hlo, hhi⟩ := parameter_bounds hq hu
  obtain ⟨hnlo, hnhi⟩ := mem_Ico.mp hn
  simp only [Nat.add_sub_cancel] at hnlo
  have hend : q * u + 1 + (q - 1) = q * (u + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [hend] at hnhi
  constructor <;> omega

theorem prime_support_subset {N q : ℕ} (hq : 2 ≤ q) :
    PaperP1.ConditionalWindowRank.oldPrimes (rawValues (starts N q) (q - 1)) ⊆
      LateWindowPrimes.cover N :=
  LateWindowPrimes.oldPrimes_subset (fun _ hn ↦ raw_values_late hq hn)

theorem parameters_card (N q : ℕ) : (parameters N q).card = length N q := by
  simp only [parameters, Nat.card_Ico, Nat.add_sub_cancel_left]

theorem starts_card (N q : ℕ) (hq : 0 < q) :
    (starts N q).card = (goodParameters N q).card := by
  apply card_image_of_injective
  intro u v h
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel h)

theorem goodParameters_card_lower (N q : ℕ) :
    length N q ≤ (goodParameters N q).card + 2 * (length N q / q + 1) := by
  let bad₀ := (parameters N q).filter fun u ↦ q ∣ u
  let bad₁ := (parameters N q).filter fun u ↦ q ∣ u + 1
  have hcover : parameters N q ⊆ (goodParameters N q ∪ bad₀) ∪ bad₁ := by
    intro u hu
    by_cases hq : q ∣ u
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hu, hq⟩))
    · by_cases hq1 : q ∣ u + 1
      · exact mem_union_right _ (mem_filter.mpr ⟨hu, hq1⟩)
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hu, hq, hq1⟩))
  have hbad₀ : bad₀.card ≤ length N q / q + 1 :=
    PaperP1.IntervalMultiples.card_multiples_interval_le _ _ _
  have hbad₁ : bad₁.card ≤ length N q / q + 1 := by
    apply PaperP1.ShortIntervalCongruences.card_common_residue_le _ (lower N q) (length N q) q
    · exact filter_subset _ _
    · intro u hu v hv
      have h := Nat.dvd_sub (mem_filter.mp hv).2 (mem_filter.mp hu).2
      simpa only [Nat.add_sub_add_right] using h
  have hcard := card_le_card hcover
  rw [parameters_card] at hcard
  have hfirst := card_union_le (goodParameters N q) bad₀
  have hsecond := card_union_le (goodParameters N q ∪ bad₀) bad₁
  omega

theorem division_lower (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / b - 1 ≤ (a / b : ℕ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hmod := Nat.mod_add_div a b
  have hmodlt := Nat.mod_lt a hb
  have heq : ((a % b : ℕ) : ℝ) + (b : ℝ) * (a / b : ℕ) = a := by exact_mod_cast hmod
  have hlt : ((a % b : ℕ) : ℝ) < b := by exact_mod_cast hmodlt
  have hbound : (a : ℝ) / b ≤ ((a / b : ℕ) : ℝ) + 1 := by
    apply (div_le_iff₀ hbR).mpr
    nlinarith
  linarith

theorem length_bounds {N q : ℕ} (hq : 0 < q) :
    (N : ℝ) / (2 * q) - 6 ≤ (length N q : ℝ) ∧
      (length N q : ℝ) ≤ (N : ℝ) / (2 * q) + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hupperLo := division_lower (2 * N) q hq
  have hupperHi : ((2 * N / q : ℕ) : ℝ) ≤ (2 * N : ℕ) / (q : ℝ) := Nat.cast_div_le
  have hlowerLo := division_lower (3 * N) (2 * q) (by omega)
  have hlowerHi : ((3 * N / (2 * q) : ℕ) : ℝ) ≤ (3 * N : ℕ) / (2 * q : ℕ) := Nat.cast_div_le
  push_cast at hupperLo hupperHi hlowerLo hlowerHi
  have hdiff : (2 * N / q : ℕ) ≤ length N q + lower N q := by unfold length; omega
  have hdiffR : ((2 * N / q : ℕ) : ℝ) ≤ (length N q : ℝ) + lower N q := by exact_mod_cast hdiff
  have hlower : (lower N q : ℝ) = (3 * N / (2 * q) : ℕ) + (5 : ℝ) := by simp only [lower, Nat.cast_add, Nat.cast_ofNat]
  rw [hlower] at hdiffR
  constructor
  · have hid : (2 * (N : ℝ)) / q - (3 * N) / (2 * q) = N / (2 * q) := by ring
    linarith
  · by_cases hle : lower N q ≤ 2 * N / q
    · have hlength : (length N q : ℝ) = ((2 * N / q : ℕ) : ℝ) - (lower N q : ℝ) := by
        unfold length
        rw [Nat.cast_sub hle]
      rw [hlength, hlower]
      have hid : (2 * (N : ℝ)) / q - (3 * N) / (2 * q) = N / (2 * q) := by ring
      linarith
    · have hzero : length N q = 0 := by unfold length; omega
      rw [hzero, Nat.cast_zero]
      positivity

theorem card_bounds {N q : ℕ} (hq : 0 < q) :
    (N : ℝ) / (2 * q) - 4 * N / (q : ℝ) ^ 2 - 8 ≤ (starts N q).card ∧
      ((starts N q).card : ℝ) ≤ (N : ℝ) / (2 * q) + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨hlenLo, hlenHi⟩ := length_bounds (N := N) hq
  have hlenNat : length N q ≤ 2 * N / q := Nat.sub_le _ _
  have hlenReal : (length N q : ℝ) ≤ ((2 * N / q : ℕ) : ℝ) := by exact_mod_cast hlenNat
  have hlenUpper : (length N q : ℝ) ≤ (2 * N : ℕ) / (q : ℝ) := hlenReal.trans Nat.cast_div_le
  have hbad : ((length N q / q : ℕ) : ℝ) ≤ 2 * N / (q : ℝ) ^ 2 := by
    calc
      _ ≤ (length N q : ℝ) / q := Nat.cast_div_le
      _ ≤ ((2 * N : ℕ) / (q : ℝ)) / q := div_le_div_of_nonneg_right hlenUpper hqR.le
      _ = _ := by push_cast; ring
  have hcountNat := goodParameters_card_lower N q
  have hcount : (length N q : ℝ) ≤ (goodParameters N q).card +
      2 * (((length N q / q : ℕ) : ℝ) + 1) := by exact_mod_cast hcountNat
  rw [starts_card N q hq]
  constructor
  · ring_nf at hbad hlenLo hcount ⊢
    linarith
  · have hcard : ((goodParameters N q).card : ℝ) ≤ length N q := by
      exact_mod_cast ((card_le_card (filter_subset _ _)).trans_eq (parameters_card N q))
    exact hcard.trans hlenHi

end PaperP1.LatePrimeStarts
