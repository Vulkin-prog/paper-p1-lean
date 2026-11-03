module

public import PaperP1.Combinatorics.TopProductSelection
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Largest fixed-cardinality products of an actual finite set of integer factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFactorTopProducts

open Finset

def maximum (P : Finset ℕ) (k : ℕ) : ℕ := (P.powersetCard k).sup fun A ↦ A.prod id

theorem selected_le (P A : Finset ℕ) (k : ℕ) (hA : A ⊆ P) (hcard : A.card = k) :
    A.prod id ≤ maximum P k :=
  le_sup (f := fun A ↦ A.prod id) (mem_powersetCard.mpr ⟨hA, hcard⟩)

theorem attained (P : Finset ℕ) (k : ℕ) (hp : 0 < maximum P k) :
    ∃ A ⊆ P, A.card = k ∧ maximum P k = A.prod id := by
  have hne : (P.powersetCard k).Nonempty := by
    by_contra hnot
    have hz : maximum P k = 0 := by simp only [maximum, not_nonempty_iff_eq_empty.mp hnot, sup_empty, bot_eq_zero]
    omega
  obtain ⟨A, hA, heq⟩ := exists_mem_eq_sup (P.powersetCard k) hne (fun A ↦ A.prod id)
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hA
  exact ⟨A, hsub, hcard, heq⟩

theorem zero_of_fewer (P : Finset ℕ) (k : ℕ) (hk : P.card < k) : maximum P k = 0 := by
  have he : P.powersetCard k = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro A hA
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hA
    have hle := card_le_card hsub
    omega
  simp only [maximum, he, sup_empty, bot_eq_zero]

theorem attained_largest (P : Finset ℕ) (k : ℕ) (hpos : ∀ p ∈ P, 0 < p) (hp : 0 < maximum P k) :
    ∃ A ⊆ P, A.card = k ∧ maximum P k = A.prod id ∧ ∀ a ∈ A, ∀ b ∈ P \ A, b < a := by
  obtain ⟨A, hsub, hcard, hprod⟩ := attained P k hp
  refine ⟨A, hsub, hcard, hprod, ?_⟩
  intro a ha b hb
  have hbP := (mem_sdiff.mp hb).1
  have hbA := (mem_sdiff.mp hb).2
  have hle : b ≤ a := TopProductSelection.outside_le_selected P A id k hpos
    (mem_powersetCard.mpr ⟨hsub, hcard⟩) (by
      intro B hB
      obtain ⟨hBP, hBcard⟩ := mem_powersetCard.mp hB
      rw [← hprod]
      exact selected_le P B k hBP hBcard) hbP hbA ha
  apply lt_of_le_of_ne hle
  intro heq
  exact hbA (by simpa only [heq] using ha)

theorem mono (P Q : Finset ℕ) (k : ℕ) (hPQ : P ⊆ Q) : maximum P k ≤ maximum Q k := by
  apply Finset.sup_le
  intro A hA
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hA
  exact selected_le Q A k (hsub.trans hPQ) hcard

theorem drop_power (P : Finset ℕ) (k : ℕ) (hk : 2 ≤ k) :
    maximum P k ^ (k - 1) ≤ maximum P (k - 1) ^ k := by
  by_cases hp : 0 < maximum P k
  · obtain ⟨A, hsub, hcard, hprod⟩ := attained P k hp
    obtain ⟨a, ha, hmin⟩ := exists_min_image A id (card_pos.mp (by omega))
    let Q := (A.erase a).prod id
    have hcard' : (A.erase a).card = k - 1 := by rw [card_erase_of_mem ha, hcard]
    have hsmall : a ^ (k - 1) ≤ Q := by
      calc
        _ = ∏ _g ∈ A.erase a, a := by rw [prod_const, hcard']
        _ ≤ _ := prod_le_prod (fun g hg ↦ hmin g (erase_subset a A hg))
    have hQ : Q ≤ maximum P (k - 1) := selected_le P (A.erase a) (k - 1) ((erase_subset a A).trans hsub) hcard'
    calc
      _ = (a * Q) ^ (k - 1) := by rw [hprod, ← mul_prod_erase A id ha]; rfl
      _ = a ^ (k - 1) * Q ^ (k - 1) := mul_pow _ _ _
      _ ≤ Q * Q ^ (k - 1) := Nat.mul_le_mul_right _ hsmall
      _ = Q ^ k := by rw [← pow_succ']; congr 1; omega
      _ ≤ _ := Nat.pow_le_pow_left hQ k
  · have hz : maximum P k = 0 := by omega
    rw [hz, zero_pow (by omega : k - 1 ≠ 0)]
    exact Nat.zero_le _

theorem threshold_drop (P : Finset ℕ) (k N : ℕ) (a : ℝ) (hk : 2 ≤ k)
    (hlarge : (N : ℝ) ^ a < (maximum P k : ℝ)) :
    (N : ℝ) ^ (a * (k - 1 : ℕ) / k) < (maximum P (k - 1) : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpower := pow_lt_pow_left₀ hlarge (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by omega : k - 1 ≠ 0)
  have hdrop : (maximum P k : ℝ) ^ (k - 1) ≤ (maximum P (k - 1) : ℝ) ^ k := by exact_mod_cast drop_power P k hk
  have hexp : (a * (k - 1 : ℕ) / k) * k = a * (k - 1 : ℕ) := by field_simp
  have heq : ((N : ℝ) ^ (a * (k - 1 : ℕ) / k)) ^ k = ((N : ℝ) ^ a) ^ (k - 1) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N), ← Real.rpow_mul_natCast (Nat.cast_nonneg N), hexp]
  exact lt_of_pow_lt_pow_left₀ k (Nat.cast_nonneg _) (heq.trans_lt (hpower.trans_le hdrop))

end PaperP1.FiniteFactorTopProducts
