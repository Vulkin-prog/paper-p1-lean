module

public import PaperP1.Arithmetic.PrimeSubsetAllocations
public import Mathlib.Data.Finset.Max

/-! # A first-passage certificate needs only log(X)/log(Y)+1 factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortPrimePassage

open Finset

def order (X Y : ℝ) : ℕ := ⌊Real.log X / Real.log Y⌋₊ + 1

theorem exists_short_subset (P : Finset ℕ) (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 < Y)
    (hP : ∀ p ∈ P, Y ≤ (p : ℝ)) (hprod : X < (P.prod id : ℕ)) :
    ∃ T : Finset ℕ, T ⊆ P ∧ X < (T.prod id : ℕ) ∧ T.card ≤ order X Y := by
  classical
  let C := P.powerset.filter fun T ↦ X < (T.prod id : ℕ)
  have hPC : P ∈ C := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hprod⟩
  obtain ⟨T, hTC, hmin⟩ := exists_min_image C Finset.card ⟨P, hPC⟩
  obtain ⟨hTP, hbig⟩ := mem_filter.mp hTC
  have hsub : T ⊆ P := mem_powerset.mp hTP
  have hTne : T.Nonempty := by
    by_contra hnot
    rw [not_nonempty_iff_eq_empty.mp hnot, prod_empty, Nat.cast_one] at hbig
    linarith
  obtain ⟨p, hp⟩ := hTne
  have herase : ((T.erase p).prod id : ℕ) ≤ X := by
    by_contra hnot
    have hC : T.erase p ∈ C := mem_filter.mpr
      ⟨mem_powerset.mpr ((erase_subset p T).trans hsub), lt_of_not_ge hnot⟩
    have hlt := card_erase_lt_of_mem hp
    exact (not_lt_of_ge (hmin _ hC)) hlt
  have hYp : 0 < Y := by linarith
  have hpositive : ∀ q ∈ T.erase p, (0 : ℝ) < q :=
    fun q hq ↦ hYp.trans_le (hP q (hsub (mem_of_mem_erase hq)))
  have hprodpos : (0 : ℝ) < ((T.erase p).prod id : ℕ) := by
    rw [Nat.cast_prod]
    exact prod_pos hpositive
  have hlog : ((T.erase p).card : ℝ) * Real.log Y ≤ Real.log X := by
    calc
      _ = ∑ _q ∈ T.erase p, Real.log Y := by simp
      _ ≤ ∑ q ∈ T.erase p, Real.log q := sum_le_sum (fun q hq ↦
        Real.log_le_log hYp (hP q (hsub (mem_of_mem_erase hq))))
      _ = Real.log (((T.erase p).prod id : ℕ) : ℝ) := by
        simp only [Nat.cast_prod, id_eq]
        rw [Real.log_prod (fun q hq ↦ (hpositive q hq).ne')]
      _ ≤ _ := Real.log_le_log hprodpos herase
  have hratio : ((T.erase p).card : ℝ) ≤ Real.log X / Real.log Y :=
    (le_div_iff₀ (Real.log_pos hY)).mpr hlog
  have hcard := Nat.le_floor hratio
  rw [card_erase_of_mem hp] at hcard
  refine ⟨T, hsub, hbig, ?_⟩
  dsimp [order]
  omega

end PaperP1.ShortPrimePassage
