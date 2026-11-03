module

public import PaperP1.Model.TouchardCountMoments
public import PaperP1.Probability.QuadraticPoisson

/-! # Uniform polynomial moments for the absolute quadratic signed reference -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonPolynomialMoments

open Finset PaperP1.PoissonSequence PaperP1.PoissonFactorialMoments

theorem shifted_power_summable (μ : ℝ) (hμ : 0 ≤ μ) (a r : ℕ) :
    Summable (fun k : ℕ ↦ mass μ k * (k + (a : ℝ)) ^ r) := by
  have hper (j : ℕ) (_hj : j ∈ range (r + 1)) :=
    ((TouchardCountMoments.poisson_hasSum j μ hμ).mul_right
      ((a : ℝ) ^ (r - j) * (r.choose j : ℝ))).summable
  have h := summable_sum hper
  apply h.congr
  intro k
  rw [add_pow, mul_sum]
  exact sum_congr rfl fun j _ ↦ by ring

theorem shift_power_summable {f : ℕ → ℝ} (s r : ℕ)
    (h : Summable (fun k : ℕ ↦ f k * (k + (s + 1 : ℕ) : ℝ) ^ r)) :
    Summable (fun k : ℕ ↦ shift f k * (k + (s : ℝ)) ^ r) := by
  have h' := hasSum_shift_weighted (fun k : ℕ ↦ (k + (s : ℝ)) ^ r)
    (s := ∑' k : ℕ, f k * (k + (s + 1 : ℕ) : ℝ) ^ r)
    (by convert h.hasSum using 1; funext k; push_cast; congr 2; ring)
  exact h'.summable

theorem envelope_summable (M : ℝ) (hM : 0 ≤ M) (r : ℕ) :
    Summable (fun k : ℕ ↦ Real.exp M *
      (mass M k + (shift (shift (mass M)) k + 2 * shift (mass M) k + mass M k) / 2) *
        (1 + (k : ℝ)) ^ r) := by
  have h0 := shifted_power_summable M hM 1 r
  have h1 := shift_power_summable (f := mass M) 1 r (shifted_power_summable M hM 2 r)
  have h2 := shift_power_summable (f := shift (mass M)) 1 r
    (shift_power_summable (f := mass M) 2 r (shifted_power_summable M hM 3 r))
  have h := (h0.add (((h2.add (h1.mul_left 2)).add h0).div_const 2)).mul_left (Real.exp M)
  apply h.congr
  intro k
  rw [add_comm 1 (k : ℝ)]
  ring

theorem mass_domination {μ M : ℝ} (hμ : 0 ≤ μ) (hμM : μ ≤ M) (k : ℕ) :
    mass μ k ≤ Real.exp M * mass M k := by
  have hM := hμ.trans hμM
  have he : Real.exp (-μ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp := pow_le_pow_left₀ hμ hμM k
  have hnonneg : (0 : ℝ) ≤ μ ^ k := pow_nonneg hμ _
  have hfactor : Real.exp M * mass M k = M ^ k / (k.factorial : ℝ) := by
    rw [mass, ← mul_div_assoc, ← mul_assoc, ← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero, one_mul]
  rw [hfactor]
  exact div_le_div_of_nonneg_right ((mul_le_of_le_one_left hnonneg he).trans hp) (Nat.cast_nonneg _)

theorem shift_nonneg {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) : ∀ k, 0 ≤ shift f k := by
  intro k
  cases k <;> simp only [shift_zero, shift_succ, le_refl, hf]

theorem shift_domination {f g : ℕ → ℝ} {A : ℝ} (h : ∀ k, f k ≤ A * g k) :
    ∀ k, shift f k ≤ A * shift g k := by
  intro k
  cases k <;> simp only [shift_zero, shift_succ, mul_zero, le_refl, h]

theorem quadratic_envelope {μ M α : ℝ} (hμ : 0 ≤ μ) (hμM : μ ≤ M)
    (hα : |α| ≤ 1) (k : ℕ) :
    |quadraticMass μ α k| ≤ Real.exp M *
      (mass M k + (shift (shift (mass M)) k + 2 * shift (mass M) k + mass M k) / 2) := by
  have hn (n : ℕ) : 0 ≤ mass μ n := by unfold mass; positivity
  have hnM (n : ℕ) : 0 ≤ mass M n := by have hM := hμ.trans hμM; unfold mass; positivity
  have hs := shift_nonneg hn
  have hss := shift_nonneg hs
  have hd := mass_domination hμ hμM
  have hds := shift_domination hd
  have hdss := shift_domination hds
  have hdiff : |secondDifference (mass μ) k| ≤
      shift (shift (mass μ)) k + 2 * shift (mass μ) k + mass μ k := by
    have h1 := abs_add_le (shift (shift (mass μ)) k - 2 * shift (mass μ) k) (mass μ k)
    have h2 := abs_sub (shift (shift (mass μ)) k) (2 * shift (mass μ) k)
    rw [abs_of_nonneg (hn k)] at h1
    rw [abs_of_nonneg (hss k), abs_of_nonneg (mul_nonneg (by norm_num) (hs k))] at h2
    exact h1.trans (by linarith only [h2])
  have hbase := abs_add_le (mass μ k) ((α / 2) * secondDifference (mass μ) k)
  rw [abs_of_nonneg (hn k), abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hbase
  have ht := mul_le_mul hα hdiff (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  dsimp only [quadraticMass]
  nlinarith only [hbase, ht, hd k, hds k, hdss k]

theorem uniform_absolute_moment (M : ℝ) (hM : 0 ≤ M) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ μ α : ℝ, 0 ≤ μ → μ ≤ M → |α| ≤ 1 →
      Summable (fun k : ℕ ↦ |quadraticMass μ α k| * (1 + (k : ℝ)) ^ r) ∧
      (∑' k : ℕ, |quadraticMass μ α k| * (1 + (k : ℝ)) ^ r) ≤ B := by
  let E := fun k : ℕ ↦ Real.exp M *
    (mass M k + (shift (shift (mass M)) k + 2 * shift (mass M) k + mass M k) / 2) *
      (1 + (k : ℝ)) ^ r
  have hE : Summable E := envelope_summable M hM r
  have hn (k : ℕ) : 0 ≤ mass M k := by unfold mass; positivity
  have hs := shift_nonneg hn
  have hss := shift_nonneg hs
  refine ⟨∑' k, E k, tsum_nonneg (fun k ↦ by have h0 := hn k; have h1 := hs k; have h2 := hss k; dsimp [E]; positivity), ?_⟩
  intro μ α hμ hμM hα
  have hle (k : ℕ) : |quadraticMass μ α k| * (1 + (k : ℝ)) ^ r ≤ E k :=
    mul_le_mul_of_nonneg_right (quadratic_envelope hμ hμM hα k) (by positivity)
  have hq := Summable.of_nonneg_of_le (fun k ↦ by positivity) hle hE
  exact ⟨hq, hq.tsum_le_tsum hle hE⟩

end PaperP1.PoissonPolynomialMoments
