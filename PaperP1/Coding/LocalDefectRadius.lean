module

public import PaperP1.Coding.LocalDefectRate
public import PaperP1.Arithmetic.LogarithmicPrimeCount
public import PaperP1.Analysis.ElementaryLogGrowth

@[expose] public section

/-! # A proved uniform prime budget for the direct coding radius -/

namespace PaperP1.LocalDefectRadius

open LocalDefectBound LocalDefectRate

theorem codingRadius_lower
    {U R : ℕ} {s : ℝ} (hs : 4096 ≤ s)
    (hlogU : s / 2 ≤ Real.log (U : ℝ))
    (hlogRpos : 0 < Real.log (64 * (R : ℝ)))
    (hlogR : Real.log (64 * (R : ℝ)) ≤ 2 * Real.log s) :
    1 ≤ codingRadius U R ∧
      s / (32 * Real.log s) ≤ (codingRadius U R : ℝ) := by
  have hspos : 0 < s := by linarith
  have hlogs : 0 < Real.log s := Real.log_pos (by linarith)
  let q : ℝ := Real.log U / (4 * Real.log (64 * (R : ℝ)))
  have hqbound : s / (16 * Real.log s) ≤ q := by
    dsimp [q]
    apply (div_le_div_iff₀ (by positivity : 0 < 16 * Real.log s)
      (by positivity : 0 < 4 * Real.log (64 * (R : ℝ)))).mpr
    calc
      s * (4 * Real.log (64 * (R : ℝ))) ≤ s * (8 * Real.log s) :=
        mul_le_mul_of_nonneg_left (by linarith) hspos.le
      _ = (s / 2) * (16 * Real.log s) := by ring
      _ ≤ Real.log U * (16 * Real.log s) :=
        mul_le_mul_of_nonneg_right hlogU (by positivity)
  have hq2 : 2 ≤ q := by
    have htwo : (2 : ℝ) ≤ s / (16 * Real.log s) := by
      apply (le_div_iff₀ (by positivity : 0 < 16 * Real.log s)).mpr
      nlinarith [ElementaryLogGrowth.thirtyTwo_mul_log_le hs]
    exact htwo.trans hqbound
  have hfloorloss : q < (codingRadius U R : ℝ) + 1 := Nat.lt_floor_add_one q
  have hhalf : q / 2 ≤ (codingRadius U R : ℝ) := by linarith
  constructor
  · exact (Nat.one_le_floor_iff q).mpr (by linarith)
  · calc
      s / (32 * Real.log s) = (s / (16 * Real.log s)) / 2 := by ring
      _ ≤ q / 2 := div_le_div_of_nonneg_right hqbound (by norm_num)
      _ ≤ _ := hhalf

noncomputable def budgetConstant (D : ℝ) : ℕ :=
  ⌈32 * (14 * Real.log 2 * (D + 2) + 1)⌉₊

/-- The actual prime count, including the extra parity row, fits one fixed
multiple of the radius. All terms are proved from logarithmic comparisons. -/
theorem prime_count_radius_budget
    {N H U R : ℕ} (D : ℝ) (hD : 0 ≤ D)
    (hlogN : 4096 ≤ Real.log (N : ℝ))
    (hH : (H : ℝ) ≤ D * Real.log N)
    (hlogU : Real.log N / 2 ≤ Real.log (U : ℝ))
    (hlogRpos : 0 < Real.log (64 * (R : ℝ)))
    (hlogR : Real.log (64 * (R : ℝ)) ≤ 2 * Real.log (Real.log N)) :
    primeCount H + 1 ≤ budgetConstant D * codingRadius U R := by
  let s : ℝ := Real.log N
  let K : ℝ := 14 * Real.log 2 * (D + 2)
  have hs : 4096 ≤ s := hlogN
  have hs0 : 0 ≤ s := by linarith
  have hlogs : 0 < Real.log s := Real.log_pos (by linarith)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hprime : (primeCount H : ℝ) ≤ K * s / Real.log s :=
    LogarithmicPrimeCount.primeCount_le_log_div_loglog D hD (by linarith) hH
  have hone : (1 : ℝ) ≤ s / Real.log s := by
    apply (le_div_iff₀ hlogs).mpr
    simpa only [one_mul] using Real.log_le_self hs0
  have hpcplus : ((primeCount H + 1 : ℕ) : ℝ) ≤ (K + 1) * s / Real.log s := by
    push_cast
    calc
      (primeCount H : ℝ) + 1 ≤ K * s / Real.log s + s / Real.log s :=
        add_le_add hprime hone
      _ = (K + 1) * s / Real.log s := by ring
  have hA : 32 * (K + 1) ≤ (budgetConstant D : ℝ) := Nat.le_ceil _
  have ht := (codingRadius_lower hs hlogU hlogRpos hlogR).2
  have hratio : (K + 1) * s / Real.log s ≤
      (budgetConstant D : ℝ) * (codingRadius U R : ℝ) := by
    calc
      (K + 1) * s / Real.log s =
          (32 * (K + 1)) * (s / (32 * Real.log s)) := by ring
      _ ≤ (budgetConstant D : ℝ) * (s / (32 * Real.log s)) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
  exact_mod_cast hpcplus.trans hratio

end PaperP1.LocalDefectRadius

