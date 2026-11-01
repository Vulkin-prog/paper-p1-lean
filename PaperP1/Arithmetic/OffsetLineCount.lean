module

public import PaperP1.Arithmetic.OffsetLinePopulation
public import PaperP1.Arithmetic.PrimeProductBudget

/-! # Distinct offset counts without an additive one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetLineCount

open Finset PaperP1.OffsetLinePopulation PaperP1.OffsetLineData PaperP1.Arithmetic

def sourceMajorant (N L : ℕ) (Y : ℝ) : ℝ := 1 + Real.log (6 * (N : ℝ) * ((L + 1 : ℕ) : ℝ)) / Real.log Y

theorem prime_card_le_log_product (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (Y M : ℝ) (hY : 1 < Y) (habove : ∀ p ∈ P, Y < (p : ℝ)) (hprod : (↑(P.prod id) : ℝ) ≤ M) :
    (P.card : ℝ) ≤ Real.log M / Real.log Y := by
  have hYpos : 0 < Y := by linarith
  have hQpos : (0 : ℝ) < P.prod id := by exact_mod_cast prod_pos (fun p hp ↦ (hP p hp).pos)
  have hlogprod : Real.log (P.prod id : ℕ) = ∑ p ∈ P, Real.log p := by
    rw [Nat.cast_prod]
    exact Real.log_prod (fun p hp ↦ by exact_mod_cast (hP p hp).ne_zero)
  have hlower : (P.card : ℝ) * Real.log Y ≤ Real.log (P.prod id : ℕ) := by
    rw [hlogprod]
    calc
      _ = ∑ _p ∈ P, Real.log Y := by simp
      _ ≤ _ := sum_le_sum (fun p hp ↦ Real.log_le_log hYpos (habove p hp).le)
  exact (le_div_iff₀ (Real.log_pos hY)).mpr (hlower.trans (Real.log_le_log hQpos hprod))

theorem distinct_offsets_le (N L : ℕ) (Y : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hinj : Function.Injective (evenSquareClassMap (X 0) L))
    (hdirect : Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L))
    (hline : CollinearSet line) (hY : 1 < Y) :
    ((points (offsets N L Y X line)).card : ℝ) ≤
      Real.log (6 * (N : ℝ) * ((L + 1 : ℕ) : ℝ)) / Real.log Y := by
  have hprod := pool_product_le N L Y X line hN hLN hX hinj hdirect hline
  have hprodR : (↑((pool N L Y X line).prod id) : ℝ) ≤ 6 * (N : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast hprod
  have hcard : ((points (offsets N L Y X line)).card : ℝ) ≤ (pool N L Y X line).card := by
    have hNat : (points (offsets N L Y X line)).card ≤ (pool N L Y X line).card := by
      calc
        _ ≤ (univ : Finset (pool N L Y X line)).card := card_image_le
        _ = _ := by rw [card_univ, Fintype.card_coe]
    exact_mod_cast hNat
  apply hcard.trans
  apply prime_card_le_log_product (pool N L Y X line)
  · exact fun p hp ↦ ((mem_pool N L Y X line p).mp hp).2.1
  · exact hY
  · exact fun p hp ↦ ((mem_pool N L Y X line p).mp hp).2.2.1
  · exact hprodR

theorem distinct_offsets_le_sourceMajorant (N L : ℕ) (Y : ℝ) (X : Fin 3 → ℕ) (line : Set (Fin 3 → ℤ))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hinj : Function.Injective (evenSquareClassMap (X 0) L))
    (hdirect : Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L))
    (hline : CollinearSet line) (hY : 1 < Y) :
    ((points (offsets N L Y X line)).card : ℝ) ≤ sourceMajorant N L Y := by
  have h := distinct_offsets_le N L Y X line hN hLN hX hinj hdirect hline hY
  unfold sourceMajorant
  linarith

end PaperP1.OffsetLineCount
