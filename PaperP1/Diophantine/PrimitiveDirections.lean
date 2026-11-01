module

public import PaperP1.Diophantine.BihomogeneousSwap

/-! # Primitive integral representatives of a rational direction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveDirections

open Finset

abbrev Pair := Fin 2 → ℤ

def ratio (z : Pair) : ℚ := (z 0 : ℚ) / z 1

def negative (z : Pair) : Pair := fun i ↦ -z i

theorem primitive_same_direction (v z : Pair)
    (hv : (v 0).natAbs.Coprime (v 1).natAbs)
    (hz : (z 0).natAbs.Coprime (z 1).natAbs)
    (hcross : v 0 * z 1 = v 1 * z 0) : z = v ∨ z = negative v := by
  let q := PaperP1.BidegreeOneElimination.scale (v 0) (v 1) (-z 1) (z 0)
  have hrel : v 0 * (-z 1) + v 1 * z 0 = 0 := by linarith
  obtain ⟨h0, h1⟩ := PaperP1.BidegreeOneElimination.scale_equations _ _ _ _ hv hrel
  change q * v 0 = z 0 at h0
  have h1' : q * v 1 = z 1 := by simpa only [neg_neg] using h1
  have hdiv0 : q.natAbs ∣ (z 0).natAbs := Int.natAbs_dvd_natAbs.mpr ⟨v 0, h0.symm⟩
  have hdiv1 : q.natAbs ∣ (z 1).natAbs := Int.natAbs_dvd_natAbs.mpr ⟨v 1, h1'.symm⟩
  have hqabs : q.natAbs = 1 := Nat.dvd_one.mp (by simpa only [hz.gcd_eq_one] using Nat.dvd_gcd hdiv0 hdiv1)
  have hq : q = 1 ∨ q = -1 := by simpa only [Nat.cast_one] using Int.natAbs_eq_iff.mp hqabs
  rcases hq with hq | hq
  · left
    funext i
    fin_cases i <;> simp_all
  · right
    funext i
    fin_cases i <;> simp_all [negative]

theorem equal_ratio_cross (v z : Pair) (hv : v 1 ≠ 0) (hz : z 1 ≠ 0)
    (heq : ratio v = ratio z) : v 0 * z 1 = v 1 * z 0 := by
  have hvq : (v 1 : ℚ) ≠ 0 := by exact_mod_cast hv
  have hzq : (z 1 : ℚ) ≠ 0 := by exact_mod_cast hz
  have h := (div_eq_div_iff hvq hzq).mp heq
  exact_mod_cast (show (v 0 : ℚ) * z 1 = (v 1 : ℚ) * z 0 by simpa only [mul_comm] using h)

theorem ratio_fibre_card (S : Finset Pair)
    (hprimitive : ∀ z ∈ S, (z 0).natAbs.Coprime (z 1).natAbs)
    (hden : ∀ z ∈ S, z 1 ≠ 0) (r : ℚ) :
    (S.filter fun z ↦ ratio z = r).card ≤ 2 := by
  classical
  let T := S.filter fun z ↦ ratio z = r
  change T.card ≤ 2
  by_cases hT : T.Nonempty
  · obtain ⟨v, hv⟩ := hT
    have hvS := (mem_filter.mp hv).1
    have hsub : T ⊆ {v, negative v} := by
      intro z hz
      have hzS := (mem_filter.mp hz).1
      have heq : ratio v = ratio z := (mem_filter.mp hv).2.trans (mem_filter.mp hz).2.symm
      rcases primitive_same_direction v z (hprimitive v hvS) (hprimitive z hzS)
        (equal_ratio_cross v z (hden v hvS) (hden z hzS) heq) with h | h
      · simp only [h, mem_insert, true_or]
      · exact mem_insert_of_mem (mem_singleton.mpr h)
    exact (card_le_card hsub).trans (by simpa only [card_singleton] using card_insert_le v {negative v})
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hT, card_empty, Nat.zero_le]

theorem axis_card (S : Finset Pair)
    (hprimitive : ∀ z ∈ S, (z 0).natAbs.Coprime (z 1).natAbs)
    (haxis : ∀ z ∈ S, z 1 = 0) : S.card ≤ 2 := by
  classical
  have hsub : S ⊆ {![1, 0], ![-1, 0]} := by
    intro z hz
    have hprim := hprimitive z hz
    have hzero := haxis z hz
    have habs : (z 0).natAbs = 1 := by simpa only [hzero, Int.natAbs_zero, Nat.coprime_zero_right] using hprim
    have hone : z 0 = 1 ∨ z 0 = -1 := by simpa only [Nat.cast_one] using Int.natAbs_eq_iff.mp habs
    rcases hone with hone | hone
    · have heq : z = ![1, 0] := by funext i; fin_cases i <;> simp_all
      simp only [heq, mem_insert, true_or]
    · have heq : z = ![-1, 0] := by funext i; fin_cases i <;> simp_all
      exact mem_insert_of_mem (mem_singleton.mpr heq)
  exact (card_le_card hsub).trans (by simpa only [card_singleton] using card_insert_le ![1, 0] { ![-1, 0] })

end PaperP1.PrimitiveDirections
