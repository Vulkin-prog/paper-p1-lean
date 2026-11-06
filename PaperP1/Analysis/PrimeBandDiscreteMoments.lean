module

public import PaperP1.Analysis.CenteredLogarithmicSampling
public import PaperP1.Analysis.PrimeRangeHighMoments

/-! # All-order discrete prime-band moments and actual separated large-value counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeBandDiscreteMoments
open Finset PaperP1 GaussianExponentialSums BoundedProductFibres
  PrimePolynomialMoments FiniteFibreSquareBudget
open scoped Classical

theorem sampled_high_moment_bound {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T : ℝ) (hT : 0 < T) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r - τ s|)
    (Y : ℕ) (hY : 0 < Y) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hband : ∀ p ∈ P, Y ≤ p ∧ p ≤ 2*Y) (c : ℕ → ℂ) (k : ℕ) :
    (∑ r ∈ R, ‖polynomial P c (fun p ↦ -Real.log p) (τ r)‖^(2*k)) ≤
      Real.exp 1 * (Real.sqrt Real.pi*(T+1) + 2*Real.pi*(((2*Y)^k : ℕ) : ℝ)) *
        (2+((k : ℝ)*Real.log 2)^2) * (k.factorial : ℝ) * (∑ p ∈ P, ‖c p‖^2)^k := by
  let S := (tuples k P).image BoundedProductFibres.value
  let b : ℕ → ℂ := aggregate (tuples k P) BoundedProductFibres.value (fun x ↦ ∏ i, c (x i))
  have hS : ∀ n ∈ S, Y^k ≤ n ∧ n ≤ (2*Y)^k := by
    intro n hn
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
    constructor
    · calc
        Y^k = ∏ _i : Fin k, Y := by simp
        _ ≤ BoundedProductFibres.value x := prod_le_prod
          (fun i hi ↦ (hband _ (Fintype.mem_piFinset.mp hx i)).1)
    · calc
        BoundedProductFibres.value x ≤ ∏ _i : Fin k, 2*Y := prod_le_prod
          (fun i hi ↦ (hband _ (Fintype.mem_piFinset.mp hx i)).2)
        _ = (2*Y)^k := by simp
  have hpower (t : ℝ) : (polynomial P c (fun p ↦ -Real.log p) t)^k =
      polynomial S b (fun n ↦ -Real.log n) t := by
    rw [power_expansion k P (fun p hp ↦ (hP p hp).pos) c t]
    exact aggregate_polynomial (tuples k P) BoundedProductFibres.value (fun x ↦ ∏ i, c (x i)) t
  have hnorm (t : ℝ) : ‖polynomial P c (fun p ↦ -Real.log p) t‖^(2*k) =
      ‖polynomial S b (fun n ↦ -Real.log n) t‖^2 := by
    rw [Nat.mul_comm 2 k,pow_mul,← norm_pow,hpower t]
  have hh := CenteredLogarithmicSampling.integer_band_sampled_mean_square R τ T hT htau hsep
    S b (Y^k) ((2*Y)^k) (pow_pos hY k) (pow_pos (by omega) k) hS
  have hlog : Real.log (((2*Y)^k : ℕ) : ℝ)-Real.log ((Y^k : ℕ) : ℝ) = (k : ℝ)*Real.log 2 := by
    rw [Nat.cast_pow,Nat.cast_pow,Real.log_pow,Real.log_pow,Nat.cast_mul,Nat.cast_ofNat,
      Real.log_mul (by norm_num) (by exact_mod_cast Nat.ne_of_gt hY)]
    ring
  have hc := coefficient_square_budget k P hP c
  change (∑ n ∈ S, ‖b n‖^2) ≤ (k.factorial : ℝ)*(∑ p ∈ P, ‖c p‖^2)^k at hc
  have hb := hh.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  calc
    _ = ∑ r ∈ R, ‖polynomial S b (fun n ↦ -Real.log n) (τ r)‖^2 :=
      sum_congr rfl (fun r hr ↦ hnorm (τ r))
    _ ≤ _ := by simpa only [hlog,mul_assoc] using hb

theorem large_values_card {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T : ℝ) (hT : 0 < T) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r - τ s|)
    (Y : ℕ) (hY : 0 < Y) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hband : ∀ p ∈ P, Y ≤ p ∧ p ≤ 2*Y) (c : ℕ → ℂ) (k : ℕ)
    (V : ℝ) (hV : 0 < V) (hbig : ∀ r ∈ R, V ≤ ‖polynomial P c (fun p ↦ -Real.log p) (τ r)‖) :
    (R.card : ℝ) ≤
      (Real.exp 1 * (Real.sqrt Real.pi*(T+1) + 2*Real.pi*(((2*Y)^k : ℕ) : ℝ)) *
        (2+((k : ℝ)*Real.log 2)^2) * (k.factorial : ℝ) * (∑ p ∈ P, ‖c p‖^2)^k) / V^(2*k) := by
  have hl := sum_le_sum (s := R) (fun r hr ↦ pow_le_pow_left₀ hV.le (hbig r hr) (2*k))
  simp only [sum_const,nsmul_eq_mul] at hl
  apply (le_div_iff₀ (pow_pos hV (2*k))).mpr
  exact hl.trans (sampled_high_moment_bound R τ T hT htau hsep Y hY P hP hband c k)
theorem reciprocal_sampled_estimates_eventually {ι : Type*} :
    ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Y ≤ p ∧ p ≤ 2*Y) →
      ∀ a : ℕ → ℂ, (∀ p ∈ P, ‖a p‖ ≤ 1) → ∀ k : ℕ,
      ∀ R : Finset ι, ∀ τ : ι → ℝ, ∀ T : ℝ, 0 < T →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r - τ s|) →
      ((∑ r ∈ R, ‖DirichletPolynomialMeanValue.value P a (τ r)‖^(2*k)) ≤
        Real.exp 1 * (Real.sqrt Real.pi*(T+1) + 2*Real.pi*(((2*Y)^k : ℕ) : ℝ)) *
          (2+((k : ℝ)*Real.log 2)^2) * (k.factorial : ℝ) * (4/((Y : ℝ)*Real.log Y))^k) ∧
      ∀ V : ℝ, 0 < V →
        (∀ r ∈ R, V ≤ ‖DirichletPolynomialMeanValue.value P a (τ r)‖) →
        (R.card : ℝ) ≤
          (Real.exp 1 * (Real.sqrt Real.pi*(T+1) + 2*Real.pi*(((2*Y)^k : ℕ) : ℝ)) *
            (2+((k : ℝ)*Real.log 2)^2) * (k.factorial : ℝ) *
              (4/((Y : ℝ)*Real.log Y))^k) / V^(2*k) := by
  obtain ⟨Y₀,hY₀,hsquare⟩ := PrimeRangeSquareBudget.reciprocal_square_budget_eventually
  refine ⟨Y₀,hY₀,?_⟩
  intro Y hY P hP hband a ha k R τ T hT htau hsep
  have hs := hsquare Y hY P hP hband a ha
  have hp := pow_le_pow_left₀ (sum_nonneg (fun p hp ↦ sq_nonneg ‖a p/(p : ℂ)‖)) hs k
  have hm := sampled_high_moment_bound R τ T hT htau hsep Y (by omega) P hP hband
    (fun p ↦ a p/(p : ℂ)) k
  have hb := hm.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  change (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value P a (τ r)‖^(2*k)) ≤ _ at hb
  refine ⟨hb,?_⟩
  intro V hV hbig
  have hl := sum_le_sum (s := R) (fun r hr ↦ pow_le_pow_left₀ hV.le (hbig r hr) (2*k))
  simp only [sum_const,nsmul_eq_mul] at hl
  exact (le_div_iff₀ (pow_pos hV (2*k))).mpr (hl.trans hb)
end PrimeBandDiscreteMoments
