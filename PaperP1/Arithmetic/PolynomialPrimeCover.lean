module

public import PaperP1.Arithmetic.SharpPrimeCount
public import PaperP1.Arithmetic.DyadicPrimeCover
public import Mathlib.Analysis.Real.Sqrt

/-! # Prime covers in a fixed multiplicative interval

The already proved PNT supplies sufficiently many actual primes. This replaces
an exponential-in-cardinality upper endpoint by a fixed multiple of the scale.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialPrimeCover

open Finset Filter DefectCounting

def interval (P : ℕ) : Finset ℕ := smallPrimesUpTo (16 * P) \ smallPrimesUpTo P

theorem mem_interval (P p : ℕ) : p ∈ interval P ↔ p.Prime ∧ P < p ∧ p ≤ 16 * P := by
  constructor
  · intro hp
    obtain ⟨hu, hl⟩ := mem_sdiff.mp hp
    obtain ⟨hprime, hupper⟩ := mem_smallPrimesUpTo.mp hu
    have hlow : P < p := by
      by_contra hh
      exact hl (mem_smallPrimesUpTo.mpr ⟨hprime, by omega⟩)
    exact ⟨hprime, hlow, hupper⟩
  · rintro ⟨hp, hl, hu⟩
    exact mem_sdiff.mpr ⟨mem_smallPrimesUpTo.mpr ⟨hp, hu⟩,
      fun h ↦ (not_le_of_gt hl) (mem_smallPrimesUpTo.mp h).2⟩

theorem card_small_primes (P : ℕ) : (smallPrimesUpTo P).card = Nat.primeCounting P := by
  change LocalDefectBound.primeCount P = Nat.primeCounting P
  exact LocalRigidityCode.primeCount_eq_primeCounting P

theorem counting_bounds : ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
    (N : ℝ) / (2 * Real.log N) ≤ (Nat.primeCounting N : ℝ) ∧
      (Nat.primeCounting N : ℝ) ≤ 2 * N / Real.log N := by
  have ht := (SharpPrimeCount.prime_counting_ratio_tendsto.eventually
    (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))).and
    (SharpPrimeCount.prime_counting_ratio_tendsto.eventually
      (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ht
  refine ⟨max 2 N₁, by omega, ?_⟩
  intro N hN
  obtain ⟨hl, hu⟩ := hN₁ N (by omega)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  constructor
  · have hh := (le_div_iff₀ hNp).mp hl.le
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hlog)).mpr
    nlinarith
  · have hh := (div_le_iff₀ hNp).mp hu.le
    exact (le_div_iff₀ hlog).mpr hh

theorem interval_count_lower : ∃ P₀ : ℕ, 16 ≤ P₀ ∧ ∀ P ≥ P₀,
    2 * (P : ℝ) / Real.log P ≤ ((interval P).card : ℝ) := by
  obtain ⟨N₀, _hN₀, hb⟩ := counting_bounds
  refine ⟨max 16 N₀, by omega, ?_⟩
  intro P hP
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hlog16 : 0 < Real.log ((16 * P : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 16 * P by omega))
  have hlogcmp : Real.log ((16 * P : ℕ) : ℝ) ≤ 2 * Real.log (P : ℝ) := by
    have hh : Real.log 16 ≤ Real.log (P : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 16 ≤ P by omega))
    rw [Nat.cast_mul]
    norm_num only [Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hPpos.ne']
    linarith
  push_cast at hlogcmp
  have hlo := (hb (16 * P) (by omega)).1
  have hlowprod := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hlog16)).mp hlo
  push_cast at hlowprod
  have hmul := mul_le_mul_of_nonneg_left hlogcmp (Nat.cast_nonneg (α := ℝ) (Nat.primeCounting (16 * P)))
  have hlow : 4 * (P : ℝ) ≤ (Nat.primeCounting (16 * P) : ℝ) * Real.log P := by
    nlinarith only [hlowprod, hmul]
  have hupperprod := (le_div_iff₀ hlog).mp (hb P (by omega)).2
  have hsub : smallPrimesUpTo P ⊆ smallPrimesUpTo (16 * P) := by
    intro p hp
    obtain ⟨hprime, hpP⟩ := mem_smallPrimesUpTo.mp hp
    exact mem_smallPrimesUpTo.mpr ⟨hprime, by omega⟩
  have hc := card_sdiff_add_card_eq_card hsub
  change (interval P).card + (smallPrimesUpTo P).card = (smallPrimesUpTo (16 * P)).card at hc
  rw [card_small_primes, card_small_primes] at hc
  have hcR : ((interval P).card : ℝ) + (Nat.primeCounting P : ℝ) =
      (Nat.primeCounting (16 * P) : ℝ) := by exact_mod_cast hc
  have hcmul := congrArg (fun x : ℝ ↦ x * Real.log P) hcR
  apply (div_le_iff₀ hlog).mpr
  nlinarith only [hlow, hupperprod, hcmul]

theorem interval_sqrt_count : ∃ P₀ : ℕ, 2 ≤ P₀ ∧ ∀ P ≥ P₀,
    Real.sqrt (P : ℝ) ≤ ((interval P).card : ℝ) := by
  obtain ⟨P₀, hP₀, hb⟩ := interval_count_lower
  refine ⟨P₀, by omega, ?_⟩
  intro P hP
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hroot : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.mpr hPpos
  have hh := Real.log_le_sub_one_of_pos hroot
  rw [Real.log_sqrt (Nat.cast_nonneg P)] at hh
  have hlogle : Real.log (P : ℝ) ≤ 2 * Real.sqrt (P : ℝ) := by linarith
  have hprod := (div_le_iff₀ hlog).mp (hb P hP)
  have hmul := mul_le_mul_of_nonneg_left hlogle (Nat.cast_nonneg (α := ℝ) (interval P).card)
  by_contra hn
  have hlt : ((interval P).card : ℝ) < Real.sqrt (P : ℝ) := lt_of_not_ge hn
  have hltprod := mul_lt_mul_of_pos_right hlt hroot
  rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg P)] at hltprod
  nlinarith only [hprod, hmul, hltprod]

theorem uniform_pool : ∃ P₀ : ℕ, 2 ≤ P₀ ∧ ∀ P ≥ P₀, ∀ m : ℕ, m ^ 2 ≤ P →
    ∃ T : Finset ℕ, T.card = m ∧ (∀ p ∈ T, p.Prime ∧ P < p ∧ p ≤ 16 * P) ∧
      (∑ p ∈ T, p) ≤ 16 * m * P ∧
      ∀ n : ℤ, n ≠ 0 → n.natAbs < P ^ m → ∃ p ∈ T, ¬(p : ℤ) ∣ n := by
  classical
  obtain ⟨P₀, hP₀, hcount⟩ := interval_sqrt_count
  refine ⟨P₀, hP₀, ?_⟩
  intro P hP m hm
  have hmR : (m : ℝ) ^ 2 ≤ P := by exact_mod_cast hm
  have hcard : m ≤ (interval P).card := by
    exact_mod_cast (Real.le_sqrt_of_sq_le hmR).trans (hcount P hP)
  obtain ⟨T, hT, hcardT⟩ := exists_subset_card_eq hcard
  have hprime (p : ℕ) (hp : p ∈ T) : p.Prime ∧ P < p ∧ p ≤ 16 * P :=
    (mem_interval P p).mp (hT hp)
  refine ⟨T, hcardT, hprime, ?_, ?_⟩
  · calc
      (∑ p ∈ T, p) ≤ ∑ _p ∈ T, 16 * P := sum_le_sum (fun p hp ↦ (hprime p hp).2.2)
      _ = _ := by simp only [sum_const, smul_eq_mul, hcardT]; ring
  · intro n hn hsmall
    have hprod : P ^ m ≤ ∏ p ∈ T, p := by
      calc
        P ^ m = ∏ _p ∈ T, P := by simp only [prod_const, hcardT]
        _ ≤ _ := prod_le_prod₀ (fun _ _ ↦ Nat.zero_le _) (fun p hp ↦ (hprime p hp).2.1.le)
    exact DyadicPrimeCover.exists_nondividing T (fun p hp ↦ (hprime p hp).1) n hn (hsmall.trans_le hprod)

end PaperP1.PolynomialPrimeCover
