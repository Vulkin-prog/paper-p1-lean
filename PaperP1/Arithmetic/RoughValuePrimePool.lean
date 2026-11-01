module

public import PaperP1.Arithmetic.ShortPrimePassage
public import PaperP1.Arithmetic.TruncatedKernelProducts

/-! # Exact logarithmic cardinal budgets for actual large-prime pools -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RoughValuePrimePool

open Finset

def roughPrimes (Y : ℝ) (n : ℕ) : Finset ℕ := n.primeFactors.filter fun p ↦ Y < (p : ℝ)

theorem roughPrimes_data (Y : ℝ) (n p : ℕ) (hp : p ∈ roughPrimes Y n) :
    p.Prime ∧ p ∣ n ∧ Y < (p : ℝ) := by
  obtain ⟨hp, hY⟩ := mem_filter.mp hp
  exact ⟨(Nat.mem_primeFactors.mp hp).1, Nat.dvd_of_mem_primeFactors hp, hY⟩

theorem roughPrimes_log (Y : ℝ) (hY : 1 < Y) (n : ℕ) (hn : 0 < n) :
    ((roughPrimes Y n).card : ℝ) * Real.log Y ≤ Real.log n := by
  let P := roughPrimes Y n
  have hP : ∀ p ∈ P, p.Prime ∧ p ∣ n ∧ Y < (p : ℝ) := fun p hp ↦ roughPrimes_data Y n p hp
  have hprod : P.prod id ∣ n := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (hP p hp).1.prime
    · intro p hp
      exact (hP p hp).2.1
  have hpos : (0 : ℝ) < (P.prod id : ℕ) := by
    exact_mod_cast (prod_pos (fun p hp ↦ (hP p hp).1.pos) : 0 < P.prod id)
  calc
    _ = ∑ _p ∈ P, Real.log Y := by simp only [P, sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ P, Real.log p := sum_le_sum (fun p hp ↦
      Real.log_le_log (by linarith : 0 < Y) (hP p hp).2.2.le)
    _ = Real.log (P.prod id : ℕ) := by
      simp only [Nat.cast_prod, id_eq]
      rw [Real.log_prod (fun p hp ↦ by exact_mod_cast (hP p hp).1.ne_zero)]
    _ ≤ _ := Real.log_le_log hpos (by exact_mod_cast Nat.le_of_dvd hn hprod)

variable {ι : Type*} [Fintype ι]

def pool (Y : ℝ) (v : ι → ℕ) : Finset ℕ := univ.biUnion fun i ↦ roughPrimes Y (v i)

theorem pool_data (Y : ℝ) (v : ι → ℕ) (p : ℕ) (hp : p ∈ pool Y v) :
    p.Prime ∧ Y < (p : ℝ) ∧ ∃ i, p ∣ v i := by
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
  have hd := roughPrimes_data Y (v i) p hi
  exact ⟨hd.1, hd.2.2, i, hd.2.1⟩

theorem pool_log_bound (Y X : ℝ) (v : ι → ℕ) (hY : 1 < Y)
    (hv : ∀ i, 0 < v i ∧ (v i : ℝ) ≤ X) :
    ((pool Y v).card : ℝ) * Real.log Y ≤ (Fintype.card ι : ℝ) * Real.log X := by
  have hcard : (pool Y v).card ≤ ∑ i, (roughPrimes Y (v i)).card := card_biUnion_le
  calc
    _ ≤ (∑ i, ((roughPrimes Y (v i)).card : ℝ)) * Real.log Y :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.log_pos hY).le
    _ = ∑ i, ((roughPrimes Y (v i)).card : ℝ) * Real.log Y := by rw [sum_mul]
    _ ≤ ∑ _i : ι, Real.log X := sum_le_sum (fun i _ ↦
      (roughPrimes_log Y hY (v i) (hv i).1).trans
        (Real.log_le_log (by exact_mod_cast (hv i).1) (hv i).2))
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]

theorem pool_order_bound (Y X : ℝ) (v : ι → ℕ) (hY : 1 < Y)
    (hv : ∀ i, 0 < v i ∧ (v i : ℝ) ≤ X) :
    (pool Y v).card ≤ Fintype.card ι * PaperP1.ShortPrimePassage.order X Y := by
  have hlog := pool_log_bound Y X v hY hv
  have horder : Real.log X / Real.log Y ≤ (PaperP1.ShortPrimePassage.order X Y : ℝ) := by
    dsimp [PaperP1.ShortPrimePassage.order]
    push_cast
    exact (Nat.lt_floor_add_one _).le
  have htop := (div_le_iff₀ (Real.log_pos hY)).mp horder
  have hmul := mul_le_mul_of_nonneg_left htop (Nat.cast_nonneg (Fintype.card ι))
  have hreal : ((pool Y v).card : ℝ) ≤ (Fintype.card ι : ℝ) * PaperP1.ShortPrimePassage.order X Y := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos hY)).mp
    nlinarith only [hlog, hmul]
  exact_mod_cast hreal

end PaperP1.RoughValuePrimePool
