module

public import PaperP1.Algebra.FourthFactorialCumulant
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # A finite bound for every repeated-index correction in the fourth cumulant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthRepeatedIndexCost

open Finset

variable {ι : Type*} [DecidableEq ι]

def tripleTerm (p : ι → ℝ) (c : Finset ι → ℝ) (G : Finset ι) : ℝ :=
  ∑ T ∈ G.powersetCard 3, c T * ∑ x ∈ T, p x

def pairTerm (p : ι → ℝ) (c : Finset ι → ℝ) (G : Finset ι) : ℝ :=
  ∑ e ∈ G.powersetCard 2, ((∑ x ∈ e, (p x) ^ 2) + ∏ x ∈ e, p x) * c e

def cost (p : ι → ℝ) (c : Finset ι → ℝ) (G : Finset ι) : ℝ :=
  -24 * tripleTerm p c G + 24 * pairTerm p c G - 6 * ∑ x ∈ G, (p x) ^ 4

omit [DecidableEq ι] in
theorem triple_bound (p : ι → ℝ) (c : Finset ι → ℝ) (G : Finset ι) (P : ℝ)
    (hp : ∀ x ∈ G, 0 ≤ p x) (hcap : ∀ x ∈ G, p x ≤ P) :
    |tripleTerm p c G| ≤ 3 * P * ∑ T ∈ G.powersetCard 3, |c T| := by
  apply (abs_sum_le_sum_abs _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro T hT
  obtain ⟨hTG, hcard⟩ := mem_powersetCard.mp hT
  have hnon : 0 ≤ ∑ x ∈ T, p x := sum_nonneg fun x hx ↦ hp x (hTG hx)
  have hsum : (∑ x ∈ T, p x) ≤ 3 * P := by
    calc
      _ ≤ ∑ _x ∈ T, P := sum_le_sum fun x hx ↦ hcap x (hTG hx)
      _ = _ := by rw [sum_const, hcard, nsmul_eq_mul]; norm_num
  rw [abs_mul, abs_of_nonneg hnon, mul_comm]
  exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _)

theorem pair_weight_bound (p : ι → ℝ) (e : Finset ι) (he : e.card = 2) (P : ℝ) (hP : 0 ≤ P)
    (hp : ∀ x ∈ e, 0 ≤ p x) (hcap : ∀ x ∈ e, p x ≤ P) :
    0 ≤ (∑ x ∈ e, (p x) ^ 2) + ∏ x ∈ e, p x ∧
      (∑ x ∈ e, (p x) ^ 2) + ∏ x ∈ e, p x ≤ 3 * P ^ 2 := by
  obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp he
  have hi := mem_insert_self i {j}
  have hj : j ∈ ({i, j} : Finset ι) := mem_insert_of_mem (mem_singleton_self j)
  have hpi := hp i hi
  have hpj := hp j hj
  have hci := hcap i hi
  have hcj := hcap j hj
  rw [sum_pair hij, prod_pair hij]
  have hsqI := pow_le_pow_left₀ hpi hci 2
  have hsqJ := pow_le_pow_left₀ hpj hcj 2
  have hprod := mul_le_mul hci hcj hpj hP
  constructor
  · positivity
  · nlinarith only [hsqI, hsqJ, hprod]

theorem pair_bound (p : ι → ℝ) (c : Finset ι → ℝ) (G : Finset ι) (P : ℝ) (hP : 0 ≤ P)
    (hp : ∀ x ∈ G, 0 ≤ p x) (hcap : ∀ x ∈ G, p x ≤ P) :
    |pairTerm p c G| ≤ 3 * P ^ 2 * ∑ e ∈ G.powersetCard 2, |c e| := by
  apply (abs_sum_le_sum_abs _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro e he
  obtain ⟨heG, hcard⟩ := mem_powersetCard.mp he
  have hw := pair_weight_bound p e hcard P hP (fun x hx ↦ hp x (heG hx)) (fun x hx ↦ hcap x (heG hx))
  rw [abs_mul, abs_of_nonneg hw.1]
  exact mul_le_mul_of_nonneg_right hw.2 (abs_nonneg _)

omit [DecidableEq ι] in
theorem diagonal_bound (p : ι → ℝ) (G : Finset ι) (P : ℝ)
    (hp : ∀ x ∈ G, 0 ≤ p x) (hcap : ∀ x ∈ G, p x ≤ P) :
    (∑ x ∈ G, (p x) ^ 4) ≤ P ^ 3 * ∑ x ∈ G, p x := by
  rw [mul_sum]
  apply sum_le_sum
  intro x hx
  have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hp x hx) (hcap x hx) 3) (hp x hx)
  simpa only [show (4 : ℕ) = 3 + 1 by rfl, pow_succ] using h

theorem bound (p : ι → ℝ) (c : Finset ι → ℝ) (G : Finset ι) (P : ℝ) (hP : 0 ≤ P)
    (hp : ∀ x ∈ G, 0 ≤ p x) (hcap : ∀ x ∈ G, p x ≤ P) :
    |cost p c G| ≤ 72 * P * (∑ T ∈ G.powersetCard 3, |c T|) +
      72 * P ^ 2 * (∑ e ∈ G.powersetCard 2, |c e|) + 6 * P ^ 3 * ∑ x ∈ G, p x := by
  have ht := triple_bound p c G P hp hcap
  have he := pair_bound p c G P hP hp hcap
  have hd := diagonal_bound p G P hp hcap
  have hd0' : 0 ≤ ∑ x ∈ G, (p x) ^ 4 := sum_nonneg fun x hx ↦ pow_nonneg (hp x hx) 4
  unfold cost
  have h1 := abs_sub (-24 * tripleTerm p c G + 24 * pairTerm p c G) (6 * ∑ x ∈ G, (p x) ^ 4)
  have h2 := abs_add_le (-24 * tripleTerm p c G) (24 * pairTerm p c G)
  rw [abs_mul, abs_mul] at h2
  norm_num at h2
  rw [abs_of_nonneg (mul_nonneg (by norm_num) hd0')] at h1
  rw [neg_mul] at h1 ⊢
  nlinarith only [h1, h2, ht, he, hd]

end PaperP1.FourthRepeatedIndexCost
