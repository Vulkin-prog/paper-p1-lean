module

public import PaperP1.Model.OneNegativePrime
public import PaperP1.Arithmetic.PrimeRunStarts
public import PaperP1.Model.PrimeCylinderSize
public import PaperP1.Model.PositiveStarts
public import PaperP1.Probability.FactorialTuples

/-! # A concrete finite prime cylinder lower bounds the original exponential moments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeRunCylinder

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.Algebra PaperP1.Probability PaperP1.CountObservables
  PaperP1.LocalDefectBound

def totalExponentialMoment (N L : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, Real.exp (t * (infiniteStartCount (dyadicBlock N) L ω : ℝ)) ∂infiniteRademacherMeasure

theorem positive_count_on_sample {M N : ℕ} (q : PrimeUpTo M) (hqN : q.val.val ≤ N) :
    (PrimeRunStarts.starts N q.val.val).card ≤
      indicatorCount (dyadicBlock N) (fun x ↦ PositiveStarts.indicator x (q.val.val - 1)) (OneNegativePrime.sample q) := by
  rw [← card_activeSites]
  apply card_le_card
  intro x hx
  have hbox := PrimeRunStarts.starts_subset_interval q.property.two_le hqN hx
  obtain ⟨u, _, hu, hu1, hxu⟩ := (PrimeRunStarts.mem_starts N q.val.val x).mp hx
  have hpattern := OneNegativePrime.positive_exact_run q u hu hu1
  apply mem_filter.mpr
  refine ⟨hbox, ?_⟩
  rw [← hxu]
  simp only [PositiveStarts.indicator, Bool.and_eq_true, decide_eq_true_eq, startIndicator_eq_true_iff]
  exact ⟨hpattern.1, hpattern.2.1⟩

theorem finiteExpectation_ge_atom {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω)
    (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) (σ : Ω) : P.weight σ * X σ ≤ finiteExpectation P.weight X := by
  exact single_le_sum (fun ω _ ↦ mul_nonneg (P.weight_nonneg ω) (hX ω)) (mem_univ σ)

theorem totalExponentialMoment_eq_finite (N L : ℕ) (t : ℝ) :
    totalExponentialMoment N L t = finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
      (fun σ ↦ Real.exp (t * (indicatorCount (dyadicBlock N) (fun x ↦ startIndicator x L) σ : ℝ))) :=
  count_observable_integral_eq_finite (subset_refl _) (fun k ↦ Real.exp (t * (k : ℝ)))

theorem positive_le_total (N L : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    PositiveStarts.exponentialMoment (dyadicBlock N) L t ≤ totalExponentialMoment N L t := by
  rw [PositiveStarts.exponentialMoment_eq_finite (subset_refl _), totalExponentialMoment_eq_finite]
  unfold finiteExpectation
  apply sum_le_sum
  intro σ _
  apply mul_le_mul_of_nonneg_left _ ((cylinderProbability (dyadicCutoff N L)).weight_nonneg σ)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ ht
  exact_mod_cast PositiveStarts.finiteCount_le_total (dyadicBlock N) L σ

theorem positive_exponential_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (t * ((PrimeRunStarts.starts N q).card : ℝ) -
      (primeCount (dyadicCutoff N (q - 1)) : ℝ) * Real.log 2) ≤
        PositiveStarts.exponentialMoment (dyadicBlock N) (q - 1) t := by
  let M := dyadicCutoff N (q - 1)
  let p : PrimeUpTo M := ⟨⟨q, by dsimp [M, dyadicCutoff]; omega⟩, hq⟩
  let σ := OneNegativePrime.sample p
  have hcount := positive_count_on_sample p hqN
  have hcountR : ((PrimeRunStarts.starts N q).card : ℝ) ≤
      (indicatorCount (dyadicBlock N) (fun x ↦ PositiveStarts.indicator x (q - 1)) σ : ℝ) := by exact_mod_cast hcount
  have hatom := finiteExpectation_ge_atom (cylinderProbability M)
    (fun σ ↦ Real.exp (t * (indicatorCount (dyadicBlock N) (fun x ↦ PositiveStarts.indicator x (q - 1)) σ : ℝ)))
    (fun _ ↦ (Real.exp_pos _).le) σ
  rw [PositiveStarts.exponentialMoment_eq_finite (subset_refl _)]
  calc
    _ = (cylinderProbability M).weight σ * Real.exp (t * ((PrimeRunStarts.starts N q).card : ℝ)) := by
      rw [PrimeCylinderSize.atom_weight, Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ (cylinderProbability M).weight σ * Real.exp
        (t * (indicatorCount (dyadicBlock N) (fun x ↦ PositiveStarts.indicator x (q - 1)) σ : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcountR ht))
        ((cylinderProbability M).weight_nonneg σ)
    _ ≤ _ := hatom

theorem positive_log_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    t * ((PrimeRunStarts.starts N q).card : ℝ) - (primeCount (dyadicCutoff N (q - 1)) : ℝ) * Real.log 2 ≤
      Real.log (PositiveStarts.exponentialMoment (dyadicBlock N) (q - 1) t) := by
  have h := Real.log_le_log (Real.exp_pos _) (positive_exponential_lower hq hqN t ht)
  simpa only [Real.log_exp] using h

theorem total_log_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    t * ((PrimeRunStarts.starts N q).card : ℝ) - (primeCount (dyadicCutoff N (q - 1)) : ℝ) * Real.log 2 ≤
      Real.log (totalExponentialMoment N (q - 1) t) := by
  have hexp := (positive_exponential_lower hq hqN t ht).trans (positive_le_total N (q - 1) t ht)
  have h := Real.log_le_log (Real.exp_pos _) hexp
  simpa only [Real.log_exp] using h

end PaperP1.PrimeRunCylinder
