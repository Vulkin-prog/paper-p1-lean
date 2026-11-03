module

public import PaperP1.Algebra.CenteredCardConvolution
public import PaperP1.Algebra.ElementarySymmetricApproximation
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Intervals

/-! # A fixed-order quadratic moment correction from exact heterogeneous centering and the full higher centered activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticMomentApproximation

open Finset PaperP1.SubsetPowerSums

variable {ι : Type*} [DecidableEq ι]

theorem decomposition (G : Finset ι) (p : ι → ℝ) (q c : Finset ι → ℝ)
    (hq : ∀ I ⊆ G, q I = ∑ D ∈ I.powerset, c D * ∏ x ∈ I \ D, p x)
    (h0 : c ∅ = 1) (h1 : ∀ x, c {x} = 0) (r : ℕ) (hr : 2 ≤ r) :
    (∑ I ∈ G.powersetCard r, q I) = elementary p G r +
      (∑ e ∈ G.powersetCard 2, c e * elementary p (G \ e) (r - 2)) +
      ∑ s ∈ Icc 3 r, ∑ D ∈ G.powersetCard s, c D * elementary p (G \ D) (r - s) := by
  classical
  let f := fun s ↦ ∑ D ∈ G.powersetCard s, c D * elementary p (G \ D) (r - s)
  have h := CenteredCardConvolution.convolution G p q c hq r
  have hsplit := sum_range_add_sum_Ico f (show 3 ≤ r + 1 by omega)
  have hinterval : Ico 3 (r + 1) = Icc 3 r := by ext s; simp only [mem_Ico, mem_Icc]; omega
  rw [← hsplit, hinterval] at h
  have hf0 : f 0 = elementary p G r := by
    simpa only [f, Nat.sub_zero] using CenteredCardConvolution.zero_layer G p c h0 r
  have hf1 : f 1 = 0 := CenteredCardConvolution.one_layer G p c h1 (r - 1)
  have hfirst : (∑ s ∈ range 3, f s) = f 0 + f 1 + f 2 := by simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [hfirst, hf0, hf1, add_zero] at h
  exact h

theorem elementary_bound (G : Finset ι) (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x)
    (M : ℝ) (hM : 1 ≤ M) (hmean : (∑ x ∈ G, p x) ≤ M)
    (D : Finset ι) (s r : ℕ) (hs : s ≤ r) :
    0 ≤ elementary p (G \ D) s ∧ elementary p (G \ D) s ≤ M ^ r := by
  have hnonneg : 0 ≤ elementary p (G \ D) s := sum_nonneg fun I _ ↦ prod_nonneg fun x _ ↦ hp x
  have hμ : 0 ≤ ∑ x ∈ G \ D, p x := sum_nonneg fun x _ ↦ hp x
  have hμM : (∑ x ∈ G \ D, p x) ≤ M :=
    (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x _ _ ↦ hp x)).trans hmean
  have hfac : (1 : ℝ) ≤ s.factorial := by exact_mod_cast Nat.factorial_pos s
  refine ⟨hnonneg, ?_⟩
  calc
    _ ≤ (∑ x ∈ G \ D, p x) ^ s / (s.factorial : ℝ) := ElementarySymmetricBound.elementary_le_power_div p hp _ s
    _ ≤ (∑ x ∈ G \ D, p x) ^ s := div_le_self (pow_nonneg hμ _) hfac
    _ ≤ M ^ s := pow_le_pow_left₀ hμ hμM s
    _ ≤ M ^ r := pow_le_pow_right₀ hM hs

theorem higher_bound (G : Finset ι) (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x)
    (c : Finset ι → ℝ) (M : ℝ) (hM : 1 ≤ M) (hmean : (∑ x ∈ G, p x) ≤ M) (r : ℕ) :
    |∑ s ∈ Icc 3 r, ∑ D ∈ G.powersetCard s, c D * elementary p (G \ D) (r - s)| ≤
      M ^ r * ∑ s ∈ Icc 3 r, ∑ D ∈ G.powersetCard s, |c D| := by
  apply (abs_sum_le_sum_abs _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro s _hs
  apply (abs_sum_le_sum_abs _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro D _hD
  obtain ⟨hzero, hbound⟩ := elementary_bound G p hp M hM hmean D (r - s) r (Nat.sub_le _ _)
  rw [abs_mul, abs_of_nonneg hzero]
  exact (mul_le_mul_of_nonneg_left hbound (abs_nonneg _)).trans_eq (mul_comm _ _)

theorem subset_error_bound (G : Finset ι) (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x)
    (q c : Finset ι → ℝ)
    (hq : ∀ I ⊆ G, q I = ∑ D ∈ I.powerset, c D * ∏ x ∈ I \ D, p x)
    (h0 : c ∅ = 1) (h1 : ∀ x, c {x} = 0) (r : ℕ) (hr : 2 ≤ r)
    (κ M : ℝ) (hκ : 0 ≤ κ) (hM : 1 ≤ M) (hcap : ∀ x ∈ G, p x ≤ κ)
    (hmean : (∑ x ∈ G, p x) ≤ M) :
    |(∑ I ∈ G.powersetCard r, q I) - (∑ x ∈ G, p x) ^ r / (r.factorial : ℝ) -
      ((∑ x ∈ G, p x) ^ (r - 2) / ((r - 2).factorial : ℝ)) * (∑ e ∈ G.powersetCard 2, c e)| ≤
      (r : ℝ) ^ 2 * κ * M ^ r +
        (((r - 2 : ℕ) : ℝ) ^ 2 + 2 * (r - 2 : ℕ)) * κ * M ^ (r - 2) *
          (∑ e ∈ G.powersetCard 2, |c e|) +
        M ^ r * ∑ s ∈ Icc 3 r, ∑ D ∈ G.powersetCard s, |c D| := by
  classical
  let μ := ∑ x ∈ G, p x
  let b := μ ^ (r - 2) / ((r - 2).factorial : ℝ)
  let E := elementary p G r - μ ^ r / (r.factorial : ℝ)
  let P := ∑ e ∈ G.powersetCard 2, c e * (elementary p (G \ e) (r - 2) - b)
  let H := ∑ s ∈ Icc 3 r, ∑ D ∈ G.powersetCard s, c D * elementary p (G \ D) (r - s)
  have hid : (∑ I ∈ G.powersetCard r, q I) - μ ^ r / (r.factorial : ℝ) -
      b * (∑ e ∈ G.powersetCard 2, c e) = E + P + H := by
    rw [decomposition G p q c hq h0 h1 r hr]
    have hP : P = (∑ e ∈ G.powersetCard 2, c e * elementary p (G \ e) (r - 2)) -
        b * (∑ e ∈ G.powersetCard 2, c e) := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun e _ ↦ by ring
    rw [hP]
    dsimp only [E, H]
    ring
  have hE := ElementarySymmetricApproximation.elementary_error_bound p hp G κ M hκ hM hcap hmean r
  have hP : |P| ≤ ((((r - 2 : ℕ) : ℝ) ^ 2 + 2 * (r - 2 : ℕ)) * κ * M ^ (r - 2)) *
      (∑ e ∈ G.powersetCard 2, |c e|) := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro e he
    have hdata := mem_powersetCard.mp he
    have h := ElementarySymmetricApproximation.deletion_error_bound p hp G e hdata.1 2 (by omega)
      κ M hκ hM hcap hmean (r - 2)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left h (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hH := higher_bound G p hp c M hM hmean r
  rw [hid]
  exact (abs_add_le (E + P) H).trans
    (add_le_add ((abs_add_le E P).trans (add_le_add hE hP)) hH)

theorem factorial_pair_coefficient (r : ℕ) (hr : 2 ≤ r) :
    (r.factorial : ℝ) / ((r - 2).factorial : ℝ) = 2 * (r.choose 2 : ℝ) := by
  have hf := Nat.factorial_mul_descFactorial hr
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hf
  have hfR : ((r - 2).factorial : ℝ) * (2 * (r.choose 2 : ℝ)) = (r.factorial : ℝ) := by
    exact_mod_cast hf
  have hpos : (0 : ℝ) < (r - 2).factorial := by exact_mod_cast Nat.factorial_pos (r - 2)
  apply (div_eq_iff hpos.ne').mpr
  nlinarith only [hfR]

theorem factorial_error_bound (G : Finset ι) (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x)
    (q c : Finset ι → ℝ)
    (hq : ∀ I ⊆ G, q I = ∑ D ∈ I.powerset, c D * ∏ x ∈ I \ D, p x)
    (h0 : c ∅ = 1) (h1 : ∀ x, c {x} = 0) (r : ℕ) (hr : 2 ≤ r)
    (κ M : ℝ) (hκ : 0 ≤ κ) (hM : 1 ≤ M) (hcap : ∀ x ∈ G, p x ≤ κ)
    (hmean : (∑ x ∈ G, p x) ≤ M) :
    |(r.factorial : ℝ) * (∑ I ∈ G.powersetCard r, q I) - (∑ x ∈ G, p x) ^ r -
      (r.choose 2 : ℝ) * (∑ x ∈ G, p x) ^ (r - 2) *
        (2 * (∑ e ∈ G.powersetCard 2, c e) - ∑ x ∈ G, p x ^ 2)| ≤
      (r.factorial : ℝ) * ((r : ℝ) ^ 2 * κ * M ^ r +
        (((r - 2 : ℕ) : ℝ) ^ 2 + 2 * (r - 2 : ℕ)) * κ * M ^ (r - 2) *
          (∑ e ∈ G.powersetCard 2, |c e|) +
        M ^ r * ∑ s ∈ Icc 3 r, ∑ D ∈ G.powersetCard s, |c D|) +
      (r.choose 2 : ℝ) * κ * M ^ (r + 1) := by
  let μ := ∑ x ∈ G, p x
  let S := ∑ e ∈ G.powersetCard 2, c e
  let Δ := ∑ x ∈ G, p x ^ 2
  let E := (∑ I ∈ G.powersetCard r, q I) - μ ^ r / (r.factorial : ℝ) -
    (μ ^ (r - 2) / ((r - 2).factorial : ℝ)) * S
  have hμ : 0 ≤ μ := sum_nonneg fun x _ ↦ hp x
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hpair : (r.factorial : ℝ) * (μ ^ (r - 2) / ((r - 2).factorial : ℝ)) =
      2 * (r.choose 2 : ℝ) * μ ^ (r - 2) := by
    calc
      _ = ((r.factorial : ℝ) / ((r - 2).factorial : ℝ)) * μ ^ (r - 2) := by ring
      _ = _ := by rw [factorial_pair_coefficient r hr]
  have hid : (r.factorial : ℝ) * (∑ I ∈ G.powersetCard r, q I) - μ ^ r -
      (r.choose 2 : ℝ) * μ ^ (r - 2) * (2 * S - Δ) =
      (r.factorial : ℝ) * E + (r.choose 2 : ℝ) * μ ^ (r - 2) * Δ := by
    dsimp only [E]
    simp only [mul_sub]
    rw [mul_div_cancel₀ _ hfac, ← mul_assoc (r.factorial : ℝ) (μ ^ (r - 2) / ((r - 2).factorial : ℝ)) S, hpair]
    ring
  have hΔ : Δ ≤ κ * M := by
    calc
      _ ≤ ∑ x ∈ G, κ * p x := sum_le_sum fun x hx ↦ by
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (hcap x hx) (hp x)
      _ = κ * μ := by rw [← mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean hκ
  have hΔzero : 0 ≤ Δ := sum_nonneg fun x _ ↦ sq_nonneg _
  have hpow : μ ^ (r - 2) ≤ M ^ r :=
    (pow_le_pow_left₀ hμ hmean _).trans (pow_le_pow_right₀ hM (Nat.sub_le _ _))
  have hdiag : (r.choose 2 : ℝ) * μ ^ (r - 2) * Δ ≤ (r.choose 2 : ℝ) * κ * M ^ (r + 1) := by
    calc
      _ ≤ (r.choose 2 : ℝ) * M ^ r * (κ * M) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) hΔ hΔzero (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have herr := subset_error_bound G p hp q c hq h0 h1 r hr κ M hκ hM hcap hmean
  rw [hid]
  have hdiagzero : 0 ≤ (r.choose 2 : ℝ) * μ ^ (r - 2) * Δ := by positivity
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg r.factorial), abs_of_nonneg hdiagzero]
  exact add_le_add (mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg _)) hdiag

end PaperP1.QuadraticMomentApproximation
