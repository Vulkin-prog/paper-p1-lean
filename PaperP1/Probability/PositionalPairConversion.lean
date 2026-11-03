module

public import PaperP1.Probability.PositionalBernoulliProducts

/-! # Deleting a designated pair from a full positional Bernoulli product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalPairConversion

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalBernoulliProducts

variable {ι : Type*}

local instance positionalPairConversionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def reference (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ) : Space ι :=
  base G p + ∑ e ∈ E, q e • (ofFinite (difference e) * base (G \ e) p)

def correction (E : Finset (Finset ι)) (q : Finset ι → ℝ) : Space ι :=
  ∑ e ∈ E, q e • ofFinite (difference e)

theorem norm_one_sub_pair (e : Finset ι) (p : ι → ℝ) (he : e.card = 2)
    (hp : ∀ x ∈ e, 0 ≤ p x ∧ p x ≤ 1) : ‖1 - base e p‖ ≤ 2 * ∑ x ∈ e, p x := by
  classical
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp he
  have hpx := hp x (mem_insert_self _ _)
  have hpy := hp y (mem_insert_of_mem (mem_singleton_self _))
  have hx := norm_one_sub_site x (p x) hpx.1
  have hy := norm_one_sub_site y (p y) hpy.1
  have hnorm := site_norm_le_one x (p x) hpx.1 hpx.2
  simp only [base, prod_pair hxy, sum_pair hxy]
  rw [show (1 : Space ι) - site x (p x) * site y (p y) =
    (1 - site x (p x)) + site x (p x) * (1 - site y (p y)) by ring]
  calc
    _ ≤ ‖1 - site x (p x)‖ + ‖site x (p x)‖ * ‖1 - site y (p y)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
    _ ≤ 2 * p x + 1 * (2 * p y) := add_le_add hx (mul_le_mul hnorm hy (norm_nonneg _) (by norm_num))
    _ = _ := by ring

theorem deletion_error (G e : Finset ι) (p : ι → ℝ) (heG : e ⊆ G) (he : e.card = 2)
    (hp : ∀ x ∈ G, 0 ≤ p x ∧ p x ≤ 1) (P : ℝ) (hcap : ∀ x ∈ G, p x ≤ P) :
    ‖base (G \ e) p - base G p‖ ≤ 4 * P := by
  have hout := norm_base_le_one (G \ e) p (fun x hx ↦ hp x (sdiff_subset hx))
  have hpair := norm_one_sub_pair e p he (fun x hx ↦ hp x (heG hx))
  have hsum : (∑ x ∈ e, p x) ≤ 2 * P := by
    calc
      _ ≤ ∑ _x ∈ e, P := sum_le_sum fun x hx ↦ hcap x (heG hx)
      _ = _ := by simp only [sum_const, he, nsmul_eq_mul, Nat.cast_ofNat]
  rw [← base_factorization G e p heG,
    show base (G \ e) p - base (G \ e) p * base e p = base (G \ e) p * (1 - base e p) by ring]
  have hh := (norm_mul_le _ _).trans (mul_le_mul hout hpair (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
  nlinarith only [hh, hsum]

theorem norm_pair_difference (e : Finset ι) (he : e.card = 2) : ‖ofFinite (difference e)‖ ≤ 4 := by
  rw [norm_ofFinite]
  simpa only [he, show (2 : ℝ) ^ 2 = 4 by norm_num] using difference_l1Norm e

theorem norm_correction (E : Finset (Finset ι)) (q : Finset ι → ℝ)
    (he : ∀ e ∈ E, e.card = 2) (hq : ∀ e ∈ E, 0 ≤ q e) :
    ‖correction E q‖ ≤ 4 * ∑ e ∈ E, q e := by
  calc
    _ ≤ ∑ e ∈ E, ‖q e • ofFinite (difference e)‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ E, 4 * q e := by
      apply sum_le_sum
      intro e heE
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hq e heE)]
      exact (mul_le_mul_of_nonneg_left (norm_pair_difference e (he e heE)) (hq e heE)).trans_eq (mul_comm _ _)
    _ = _ := (mul_sum _ _ _).symm

theorem reference_linear_error (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) (hp : ∀ x ∈ G, 0 ≤ p x ∧ p x ≤ 1)
    (hq : ∀ e ∈ E, 0 ≤ q e) (P M : ℝ) (hcap : ∀ x ∈ G, p x ≤ P) (hmean : ∑ x ∈ G, p x ≤ M) :
    ‖reference G E p q - (poisson G p + correction E q * poisson G p)‖ ≤
      (1 + 4 * ∑ e ∈ E, q e) * (4 * (∑ x ∈ G, (p x) ^ 2) * Real.exp (2 * M)) +
        16 * P * ∑ e ∈ E, q e := by
  let F := 4 * (∑ x ∈ G, (p x) ^ 2) * Real.exp (2 * M)
  have hbase : ‖base G p - poisson G p‖ ≤ F := first_order_error G p (fun x hx ↦ (hp x hx).1) M hmean
  have hlocal (e : Finset ι) (he : e ∈ E) : ‖base (G \ e) p - poisson G p‖ ≤ 4 * P + F := by
    have hh := norm_add_le (base (G \ e) p - base G p) (base G p - poisson G p)
    rw [sub_add_sub_cancel] at hh
    exact hh.trans (add_le_add (deletion_error G e p (hE e he).1 (hE e he).2 hp P hcap) hbase)
  have hterm (e : Finset ι) (he : e ∈ E) :
      ‖q e • (ofFinite (difference e) * (base (G \ e) p - poisson G p))‖ ≤ q e * (4 * (4 * P + F)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hq e he)]
    apply mul_le_mul_of_nonneg_left _ (hq e he)
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_pair_difference e (hE e he).2) (hlocal e he)
      (norm_nonneg _) (by norm_num))
  have hid : reference G E p q - (poisson G p + correction E q * poisson G p) =
      (base G p - poisson G p) +
        ∑ e ∈ E, q e • (ofFinite (difference e) * (base (G \ e) p - poisson G p)) := by
    simp only [reference, correction, sum_mul, mul_sub, smul_sub, smul_mul_assoc, sum_sub_distrib]
    abel
  rw [hid]
  have hs := (norm_sum_le _ _).trans (sum_le_sum hterm)
  have heq : (∑ e ∈ E, q e * (4 * (4 * P + F))) = (∑ e ∈ E, q e) * (4 * (4 * P + F)) := (sum_mul _ _ _).symm
  rw [heq] at hs
  have hh := (norm_add_le _ _).trans (add_le_add hbase hs)
  exact hh.trans_eq (by dsimp only [F]; ring)

theorem linear_exponential_error (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) (hp : ∀ x ∈ G, 0 ≤ p x)
    (hq : ∀ e ∈ E, 0 ≤ q e) :
    ‖poisson G p + correction E q * poisson G p - PositionalCompoundPoisson.target G E p q‖ ≤
      16 * (∑ e ∈ E, q e) ^ 2 * Real.exp (4 * ∑ e ∈ E, q e) := by
  let A := correction E q
  let β := ∑ e ∈ E, q e
  have hA : ‖A‖ ≤ 4 * β := norm_correction E q (fun e he ↦ (hE e he).2) hq
  have he : PositionalCompoundPoisson.target G E p q = poisson G p * NormedSpace.exp A := by
    rw [PositionalCompoundPoisson.target_exponential G E p q hE]
    exact NormedSpace.exp_add
  have hid : poisson G p + correction E q * poisson G p - PositionalCompoundPoisson.target G E p q =
      poisson G p * (1 + A - NormedSpace.exp A) := by rw [he]; dsimp only [A]; ring
  have hlocal : ‖1 + A - NormedSpace.exp A‖ ≤ ‖A‖ ^ 2 * Real.exp ‖A‖ := by
    rw [norm_sub_rev]
    exact BanachExponentialRemainder.norm_exp_sub_linear_le A
  rw [hid]
  calc
    _ ≤ ‖poisson G p‖ * ‖1 + A - NormedSpace.exp A‖ := norm_mul_le _ _
    _ ≤ 1 * (‖A‖ ^ 2 * Real.exp ‖A‖) := mul_le_mul (norm_poisson_le_one G p hp) hlocal
      (norm_nonneg _) (by norm_num)
    _ ≤ (4 * β) ^ 2 * Real.exp (4 * β) := by
      rw [one_mul]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg A) hA 2) (Real.exp_le_exp.mpr hA)
        (Real.exp_nonneg _) (sq_nonneg _)
    _ = _ := by dsimp only [β]; ring

theorem conversion_bound (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) (hp : ∀ x ∈ G, 0 ≤ p x ∧ p x ≤ 1)
    (hq : ∀ e ∈ E, 0 ≤ q e) (P M : ℝ) (hcap : ∀ x ∈ G, p x ≤ P) (hmean : ∑ x ∈ G, p x ≤ M) :
    ‖reference G E p q - PositionalCompoundPoisson.target G E p q‖ ≤
      (1 + 4 * ∑ e ∈ E, q e) * (4 * (∑ x ∈ G, (p x) ^ 2) * Real.exp (2 * M)) +
        16 * P * ∑ e ∈ E, q e + 16 * (∑ e ∈ E, q e) ^ 2 * Real.exp (4 * ∑ e ∈ E, q e) := by
  have hh := norm_add_le (reference G E p q - (poisson G p + correction E q * poisson G p))
    ((poisson G p + correction E q * poisson G p) - PositionalCompoundPoisson.target G E p q)
  rw [sub_add_sub_cancel] at hh
  exact hh.trans (add_le_add (reference_linear_error G E p q hE hp hq P M hcap hmean)
    (linear_exponential_error G E p q hE (fun x hx ↦ (hp x hx).1) hq))

end PaperP1.PositionalPairConversion
