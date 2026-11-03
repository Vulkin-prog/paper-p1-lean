module

public import PaperP1.Arithmetic.TernaryTopProducts
public import Mathlib.Data.Finset.Max

/-! # Deleting the smallest group from an actual maximizing selection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryTopProductDrop

open Finset PaperP1.TernaryPrimeGroups PaperP1.TernaryTopProducts

theorem drop_power (U : Fin 3 → Finset ℕ) (H k : ℕ) (hk : 2 ≤ k) :
    topProduct U H k ^ (k - 1) ≤ topProduct U H (k - 1) ^ k := by
  by_cases hp : 0 < topProduct U H k
  · obtain ⟨S, hsub, hcard, hprod⟩ := attained U H k hp
    have hne : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨a, ha, hmin⟩ := exists_min_image S (group H) hne
    let P := ∏ u ∈ S.erase a, group H u
    have hcard' : (S.erase a).card = k - 1 := by rw [card_erase_of_mem ha, hcard]
    have hsmall : group H a ^ (k - 1) ≤ P := by
      calc
        _ = ∏ _u ∈ S.erase a, group H a := by rw [prod_const, hcard']
        _ ≤ _ := prod_le_prod (fun u hu ↦ hmin u (erase_subset a S hu))
    have hP : P ≤ topProduct U H (k - 1) :=
      selected_le_top U H (k - 1) (S.erase a) ((erase_subset a S).trans hsub) hcard'
    calc
      _ = (group H a * P) ^ (k - 1) := by rw [hprod, ← mul_prod_erase S (group H) ha]
      _ = group H a ^ (k - 1) * P ^ (k - 1) := mul_pow _ _ _
      _ ≤ P * P ^ (k - 1) := Nat.mul_le_mul_right _ hsmall
      _ = P ^ k := by rw [← pow_succ']; congr 1; omega
      _ ≤ _ := Nat.pow_le_pow_left hP k
  · have hz : topProduct U H k = 0 := by omega
    rw [hz, zero_pow (by omega : k - 1 ≠ 0)]
    exact Nat.zero_le _

def thresholdExponent (k : ℕ) : ℝ := (6 * (k - 1 : ℕ) : ℝ) / (5 * k)

theorem threshold_drop (U : Fin 3 → Finset ℕ) (H k N : ℕ) (hk : 2 ≤ k)
    (hlarge : (N : ℝ) ^ (6 / 5 : ℝ) < (topProduct U H k : ℝ)) :
    (N : ℝ) ^ thresholdExponent k < (topProduct U H (k - 1) : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpower : ((N : ℝ) ^ (6 / 5 : ℝ)) ^ (k - 1) < (topProduct U H k : ℝ) ^ (k - 1) :=
    pow_lt_pow_left₀ hlarge (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by omega)
  have hdrop : (topProduct U H k : ℝ) ^ (k - 1) ≤ (topProduct U H (k - 1) : ℝ) ^ k := by
    exact_mod_cast drop_power U H k hk
  have hexp : thresholdExponent k * k = (6 / 5 : ℝ) * (k - 1 : ℕ) := by
    unfold thresholdExponent
    field_simp
  have heq : ((N : ℝ) ^ thresholdExponent k) ^ k = ((N : ℝ) ^ (6 / 5 : ℝ)) ^ (k - 1) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N), ← Real.rpow_mul_natCast (Nat.cast_nonneg N), hexp]
  exact lt_of_pow_lt_pow_left₀ k (Nat.cast_nonneg _) (heq.trans_lt (hpower.trans_le hdrop))

theorem thresholdExponent_ge (k : ℕ) (hk : 4 ≤ k) : (9 / 10 : ℝ) ≤ thresholdExponent k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkcast : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  unfold thresholdExponent
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 5 * k)).mpr
  rw [hsub]
  linarith

theorem thresholdExponent_ge_one (k : ℕ) (hk : 6 ≤ k) : 1 ≤ thresholdExponent k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkcast : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  unfold thresholdExponent
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 5 * k)).mpr
  rw [hsub]
  linarith

end PaperP1.TernaryTopProductDrop
