module

public import PaperP1.Asymptotics.SplitTupleExposure
public import PaperP1.Asymptotics.DyadicQuadraticBudgets

/-! # Actual dyadic prime-pattern profiles at growing degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GrowingDegreeProfiles

open Finset PaperP1.EvenPrimePatterns

def height (C N d : ℕ) : ℕ := ((C + 1) * N) ^ d

def indices (C N d : ℕ) : Finset ℕ := range (Nat.log2 (height C N d) + 1)

abbrev Code (ι : Type*) [Fintype ι] (C N d : ℕ) :=
  ↥(patterns : Finset (Finset ι)) → Fin (indices C N d).card

theorem height_pos (C N d : ℕ) (hN : 0 < N) : 0 < height C N d := by
  unfold height
  positivity

theorem mem_indices (C N d q : ℕ) (hN : 0 < N) (hq : 0 < q) (hheight : q ≤ height C N d) :
    Nat.log2 q ∈ indices C N d := by
  apply mem_range.mpr
  have hle : Nat.log2 q ≤ Nat.log2 (height C N d) :=
    (Nat.le_log2 (height_pos C N d hN).ne').mpr ((Nat.log2_self_le hq.ne').trans hheight)
  omega

theorem part_height {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (hq : ∀ i, 0 < q i) (H : ℕ) (hheight : ∀ i, q i ≤ H)
    (S : Finset ι) (hS : S ∈ patterns) : part q S ≤ H := by
  have htwo := (mem_filter.mp hS).2.1
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < S.card by omega)
  exact (Nat.le_of_dvd (hq i) (part_dvd_coordinate q S i hi)).trans (hheight i)

def actual_profile {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (hq : ∀ i, 0 < q i) (C N d : ℕ) (hN : 0 < N)
    (hheight : ∀ i, q i ≤ height C N d) : Code ι C N d := fun S ↦
  ⟨Nat.log2 (part q S.val), by
    have hm := mem_indices C N d (part q S.val) hN (part_pos q S.val)
      (part_height q hq (height C N d) hheight S.val S.property)
    simpa only [indices, card_range, mem_range] using hm⟩

theorem actual_profile_window {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (hq : ∀ i, 0 < q i) (C N d : ℕ) (hN : 0 < N)
    (hheight : ∀ i, q i ≤ height C N d) (S : (patterns : Finset (Finset ι))) :
    2 ^ (actual_profile q hq C N d hN hheight S).val ≤ part q S.val ∧
      part q S.val < 2 * 2 ^ (actual_profile q hq C N d hN hheight S).val :=
  PaperP1.DyadicQuadraticBudgets.dyadic_bounds _ (part_pos q S.val)

theorem card_codes (ι : Type*) [Fintype ι] [DecidableEq ι] (C N d : ℕ) :
    Fintype.card (Code ι C N d) = (indices C N d).card ^ (patterns : Finset (Finset ι)).card := by
  simp only [Code, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

theorem indices_card_budget (C : ℕ) (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d : ℕ, (d : ℝ) ≤ c * Real.log (Real.log N) →
      ((indices C N d).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let K : ℝ := c * (Real.log (C + 1 : ℕ) + 1) / Real.log 2 + 1
  obtain ⟨Np, hNp⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow K 2 ε hε
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (Filter.eventually_ge_atTop 1))
  refine ⟨max 2 (max Np Nl), ?_⟩
  intro N hN d hd
  have hn : 0 < N := by omega
  have hlogN : 1 ≤ Real.log N := hNl N (by omega)
  have hlogNpos : 0 < Real.log N := by linarith
  have hlogC : 0 ≤ Real.log (C + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ C + 1 by omega))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hll : Real.log (Real.log N) ≤ Real.log N :=
    (Real.log_le_sub_one_of_pos hlogNpos).trans (by linarith)
  have hd' : (d : ℝ) ≤ c * Real.log N := hd.trans (mul_le_mul_of_nonneg_left hll hc)
  have hbase : Real.log (C + 1 : ℕ) + Real.log N ≤
      (Real.log (C + 1 : ℕ) + 1) * Real.log N := by
    nlinarith only [mul_le_mul_of_nonneg_left hlogN hlogC]
  have hhlog : Real.log (height C N d : ℝ) ≤
      c * (Real.log (C + 1 : ℕ) + 1) * (Real.log N) ^ 2 := by
    have hheightlog : Real.log (height C N d : ℝ) =
        (d : ℝ) * (Real.log (C + 1 : ℕ) + Real.log N) := by
      unfold height
      rw [Nat.cast_pow, Nat.cast_mul, Real.log_pow,
        Real.log_mul (by positivity) (by exact_mod_cast hn.ne')]
    rw [hheightlog]
    calc
      _ ≤ (c * Real.log N) * ((Real.log (C + 1 : ℕ) + 1) * Real.log N) :=
        mul_le_mul hd' hbase (by positivity) (by positivity)
      _ = _ := by ring
  have hpow : (2 : ℝ) ^ Nat.log2 (height C N d) ≤ height C N d := by
    exact_mod_cast Nat.log2_self_le (height_pos C N d hn).ne'
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log2 (height C N d)) hpow
  rw [Real.log_pow] at hlog
  have hidx : (Nat.log2 (height C N d) : ℝ) ≤
      (c * (Real.log (C + 1 : ℕ) + 1) / Real.log 2) * (Real.log N) ^ 2 := by
    have hdiv := (le_div_iff₀ hlog2).mpr (hlog.trans hhlog)
    calc
      _ ≤ (c * (Real.log (C + 1 : ℕ) + 1) * (Real.log N) ^ 2) / Real.log 2 := hdiv
      _ = _ := by ring
  have hone : (1 : ℝ) ≤ (Real.log N) ^ 2 := by nlinarith
  have hp := hNp N (by omega)
  rw [Real.rpow_two] at hp
  simp only [indices, card_range, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ (c * (Real.log (C + 1 : ℕ) + 1) / Real.log 2) * (Real.log N) ^ 2 + (Real.log N) ^ 2 :=
      add_le_add hidx hone
    _ = K * (Real.log N) ^ 2 := by dsimp [K]; ring
    _ ≤ _ := hp

theorem profile_card_budget (ι : Type*) [Fintype ι] [DecidableEq ι] (C : ℕ) (c ε : ℝ)
    (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d : ℕ, (d : ℝ) ≤ c * Real.log (Real.log N) →
      (Fintype.card (Code ι C N d) : ℝ) ≤ (N : ℝ) ^ ε := by
  let k := (patterns : Finset (Finset ι)).card
  let η := ε / (k + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Np, hNp⟩ := indices_card_budget C c η hc hη
  refine ⟨max 2 Np, ?_⟩
  intro N hN d hd
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn : (0 : ℝ) ≤ N := by positivity
  have hp := hNp N (by omega) d hd
  have he : η * k ≤ ε := by
    have heq : η * (k + 1) = ε := by dsimp [η]; field_simp
    nlinarith only [heq, hη]
  rw [card_codes, Nat.cast_pow]
  calc
    _ ≤ ((N : ℝ) ^ η) ^ k := pow_le_pow_left₀ (by positivity) hp k
    _ = (N : ℝ) ^ (η * k) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 he

end PaperP1.GrowingDegreeProfiles
