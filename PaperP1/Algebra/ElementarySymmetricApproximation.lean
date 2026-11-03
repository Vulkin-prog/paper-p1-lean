module

public import PaperP1.Algebra.ElementarySymmetricBound
public import PaperP1.Algebra.NonnegativePowerDifference
public import PaperP1.Combinatorics.TriplePairIncidence
public import Mathlib.Tactic.FieldSimp

/-! # Explicit all-order collision and deletion errors for exact heterogeneous elementary weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ElementarySymmetricApproximation

open Finset PaperP1.SubsetPowerSums

variable {ι : Type*} [DecidableEq ι]

theorem pointed_identity (p : ι → ℝ) (G : Finset ι) (r : ℕ) :
    ((r + 1 : ℕ) : ℝ) * elementary p G (r + 1) =
      ∑ D ∈ G.powersetCard r, (∏ x ∈ D, p x) * ((∑ x ∈ G, p x) - ∑ x ∈ D, p x) := by
  classical
  calc
    _ = ∑ T ∈ G.powersetCard (r + 1), ∑ x ∈ T, p x * ∏ y ∈ T.erase x, p y := by
      rw [elementary, mul_sum]
      apply sum_congr rfl
      intro T hT
      have hcard := (mem_powersetCard.mp hT).2
      calc
        _ = ∑ _x ∈ T, ∏ y ∈ T, p y := by rw [sum_const, nsmul_eq_mul, hcard]
        _ = _ := sum_congr rfl (fun x hx ↦ (mul_prod_erase T p hx).symm)
    _ = ∑ D ∈ G.powersetCard r, ∑ x ∈ G \ D, p x * ∏ y ∈ D, p y :=
      TriplePairIncidence.erased_sum G r (fun D x ↦ p x * ∏ y ∈ D, p y)
    _ = _ := by
      apply sum_congr rfl
      intro D hD
      rw [← sum_mul, sum_sdiff_eq_sub (mem_powersetCard.mp hD).1, mul_comm]

theorem factorial_increment_bound (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x) (G : Finset ι)
    (κ : ℝ) (hκ : 0 ≤ κ) (hcap : ∀ x ∈ G, p x ≤ κ) (r : ℕ) :
    (∑ x ∈ G, p x) * ((r.factorial : ℝ) * elementary p G r) -
      ((r + 1).factorial : ℝ) * elementary p G (r + 1) ≤
      (r : ℝ) * κ * (∑ x ∈ G, p x) ^ r := by
  have hid : (∑ x ∈ G, p x) * elementary p G r - ((r + 1 : ℕ) : ℝ) * elementary p G (r + 1) =
      ∑ D ∈ G.powersetCard r, (∏ x ∈ D, p x) * ∑ x ∈ D, p x := by
    rw [pointed_identity, elementary, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro D _hD
    ring
  have hsum : (∑ D ∈ G.powersetCard r, (∏ x ∈ D, p x) * ∑ x ∈ D, p x) ≤
      (r : ℝ) * κ * elementary p G r := by
    rw [elementary, mul_sum]
    apply sum_le_sum
    intro D hD
    have hdata := mem_powersetCard.mp hD
    have hmean : (∑ x ∈ D, p x) ≤ (r : ℝ) * κ := by
      calc
        _ ≤ ∑ _x ∈ D, κ := sum_le_sum fun x hx ↦ hcap x (hdata.1 hx)
        _ = _ := by rw [sum_const, nsmul_eq_mul, hdata.2]
    exact (mul_le_mul_of_nonneg_left hmean (prod_nonneg fun x _ ↦ hp x)).trans_eq (mul_comm _ _)
  calc
    _ = (r.factorial : ℝ) * ((∑ x ∈ G, p x) * elementary p G r -
        ((r + 1 : ℕ) : ℝ) * elementary p G (r + 1)) := by rw [Nat.factorial_succ, Nat.cast_mul]; ring
    _ ≤ (r.factorial : ℝ) * ((r : ℝ) * κ * elementary p G r) := by
      rw [hid]
      exact mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = (r : ℝ) * κ * ((r.factorial : ℝ) * elementary p G r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (ElementarySymmetricBound.factorial_elementary_le p hp G r) (mul_nonneg (Nat.cast_nonneg _) hκ)

theorem factorial_error_bound (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x) (G : Finset ι)
    (κ M : ℝ) (hκ : 0 ≤ κ) (hM : 1 ≤ M) (hcap : ∀ x ∈ G, p x ≤ κ)
    (hmean : (∑ x ∈ G, p x) ≤ M) (r : ℕ) :
    (∑ x ∈ G, p x) ^ r - (r.factorial : ℝ) * elementary p G r ≤ (r : ℝ) ^ 2 * κ * M ^ r := by
  let μ := ∑ x ∈ G, p x
  have hμ : 0 ≤ μ := sum_nonneg fun x _ ↦ hp x
  have hMzero : 0 ≤ M := by linarith only [hM]
  induction r with
  | zero => simp only [pow_zero, Nat.factorial_zero, Nat.cast_zero, Nat.cast_one, elementary_zero, mul_one, sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul, le_refl]
  | succ r ih =>
    have hinc := factorial_increment_bound p hp G κ hκ hcap r
    have hpower : μ ^ r ≤ M ^ r := pow_le_pow_left₀ hμ hmean r
    have hscaled := mul_le_mul_of_nonneg_right hmean (sq_nonneg (r : ℝ))
    have hlinear : (r : ℝ) ≤ (2 * r + 1) * M := by
      have h := mul_le_mul_of_nonneg_left hM (show (0 : ℝ) ≤ 2 * r + 1 by positivity)
      nlinarith only [h, Nat.cast_nonneg (α := ℝ) r]
    have hcoef : μ * (r : ℝ) ^ 2 + r ≤ ((r : ℝ) + 1) ^ 2 * M := by
      change μ * (r : ℝ) ^ 2 ≤ M * (r : ℝ) ^ 2 at hscaled
      nlinarith only [hscaled, hlinear]
    calc
      _ = μ * (μ ^ r - (r.factorial : ℝ) * elementary p G r) +
          (μ * ((r.factorial : ℝ) * elementary p G r) - ((r + 1).factorial : ℝ) * elementary p G (r + 1)) := by rw [pow_succ]; ring
      _ ≤ μ * ((r : ℝ) ^ 2 * κ * M ^ r) + (r : ℝ) * κ * μ ^ r :=
        add_le_add (mul_le_mul_of_nonneg_left ih hμ) hinc
      _ ≤ μ * ((r : ℝ) ^ 2 * κ * M ^ r) + (r : ℝ) * κ * M ^ r :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hpower (mul_nonneg (Nat.cast_nonneg _) hκ))
      _ = (μ * (r : ℝ) ^ 2 + r) * (κ * M ^ r) := by ring
      _ ≤ (((r : ℝ) + 1) ^ 2 * M) * (κ * M ^ r) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hκ (pow_nonneg hMzero _))
      _ = _ := by rw [pow_succ]; push_cast; ring

theorem elementary_error_bound (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x) (G : Finset ι)
    (κ M : ℝ) (hκ : 0 ≤ κ) (hM : 1 ≤ M) (hcap : ∀ x ∈ G, p x ≤ κ)
    (hmean : (∑ x ∈ G, p x) ≤ M) (r : ℕ) :
    |elementary p G r - (∑ x ∈ G, p x) ^ r / (r.factorial : ℝ)| ≤ (r : ℝ) ^ 2 * κ * M ^ r := by
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hfacone : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hnonneg := sub_nonneg.mpr (ElementarySymmetricBound.factorial_elementary_le p hp G r)
  have heq : elementary p G r - (∑ x ∈ G, p x) ^ r / (r.factorial : ℝ) =
      ((r.factorial : ℝ) * elementary p G r - (∑ x ∈ G, p x) ^ r) / (r.factorial : ℝ) := by field_simp
  rw [heq, abs_div, abs_of_pos hfac, abs_sub_comm, abs_of_nonneg hnonneg]
  exact (div_le_self hnonneg hfacone).trans (factorial_error_bound p hp G κ M hκ hM hcap hmean r)

theorem deletion_error_bound (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x) (G D : Finset ι)
    (hDG : D ⊆ G) (s : ℕ) (hsize : D.card ≤ s) (κ M : ℝ) (hκ : 0 ≤ κ) (hM : 1 ≤ M)
    (hcap : ∀ x ∈ G, p x ≤ κ) (hmean : (∑ x ∈ G, p x) ≤ M) (r : ℕ) :
    |elementary p (G \ D) r - (∑ x ∈ G, p x) ^ r / (r.factorial : ℝ)| ≤
      ((r : ℝ) ^ 2 + s * r) * κ * M ^ r := by
  let μ := ∑ x ∈ G, p x
  let ν := ∑ x ∈ G \ D, p x
  have hμ : 0 ≤ μ := sum_nonneg fun x _ ↦ hp x
  have hν : 0 ≤ ν := sum_nonneg fun x _ ↦ hp x
  have hνμ : ν ≤ μ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x _ _ ↦ hp x)
  have hνM : ν ≤ M := hνμ.trans hmean
  have hsumD : (∑ x ∈ D, p x) ≤ (s : ℝ) * κ := by
    calc
      _ ≤ ∑ _x ∈ D, κ := sum_le_sum fun x hx ↦ hcap x (hDG hx)
      _ = (D.card : ℝ) * κ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) hκ
  have hdiff : |ν - μ| ≤ (s : ℝ) * κ := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hνμ)]
    have hsplit := sum_sdiff (f := p) hDG
    change ν + (∑ x ∈ D, p x) = μ at hsplit
    linarith only [hsplit, hsumD]
  have hpowers : |ν ^ r - μ ^ r| ≤ (s : ℝ) * κ * r * M ^ r := by
    calc
      _ ≤ |ν - μ| * r * M ^ (r - 1) := NonnegativePowerDifference.bound ν μ M hν hμ hνM hmean r
      _ ≤ ((s : ℝ) * κ) * r * M ^ (r - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdiff (Nat.cast_nonneg _))
          (pow_nonneg (by linarith only [hM]) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (Nat.sub_le r 1)) (by positivity)
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hfacone : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hdiv : |ν ^ r / (r.factorial : ℝ) - μ ^ r / (r.factorial : ℝ)| ≤
      (s : ℝ) * κ * r * M ^ r := by
    rw [← sub_div, abs_div, abs_of_pos hfac]
    exact (div_le_self (abs_nonneg _) hfacone).trans hpowers
  have helem := elementary_error_bound p hp (G \ D) κ M hκ hM
    (fun x hx ↦ hcap x (mem_sdiff.mp hx).1) hνM r
  calc
    _ ≤ |elementary p (G \ D) r - ν ^ r / (r.factorial : ℝ)| +
        |ν ^ r / (r.factorial : ℝ) - μ ^ r / (r.factorial : ℝ)| := abs_sub_le _ _ _
    _ ≤ (r : ℝ) ^ 2 * κ * M ^ r + (s : ℝ) * κ * r * M ^ r := add_le_add helem hdiv
    _ = _ := by ring

end PaperP1.ElementarySymmetricApproximation
