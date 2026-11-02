module

public import PaperP1.Probability.FinitePoissonCharlierConversion
public import PaperP1.Model.RegularSetAsymptotic
public import PaperP1.Model.RetainedReferenceTheorem

/-! # A uniform critical-band analytic conversion with an explicit covariance parameter -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonCharlierConversion

open PaperP1.Probability PaperP1.FinitePoissonCharlierConversion

def errorConstant (C : ℝ) : ℝ :=
  16 * Real.exp (2 * (2 : ℝ) ^ C + 4) * (((2 : ℝ) ^ C) ^ 3 + ((2 : ℝ) ^ C) ^ 4) +
  16 * Real.exp (2 * (2 : ℝ) ^ C + 2) * ((2 : ℝ) ^ C + ((2 : ℝ) ^ C) ^ 2)

theorem errorConstant_pos (C : ℝ) : 0 < errorConstant C := by
  unfold errorConstant
  positivity

theorem critical_bound {N L n : ℕ} {C : ℝ} (hN : 2 ≤ N) (hn : 2 ≤ n) (hnN : n ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) (β c₂ : ℝ) :
    (∑' k : ℕ, |(FiniteLawEmbedding.embed (finiteReference n ((2 ^ L : ℝ)⁻¹) β) -
      QuadraticPoisson.reference ((n : ℝ) * (2 ^ L : ℝ)⁻¹)
        (2 * c₂ - (n : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2)) {k}|) ≤
      4 * |β - c₂| + errorConstant C * (1 / (N : ℝ) ^ 2 + |c₂| / N) := by
  let p : ℝ := (2 ^ L : ℝ)⁻¹
  let A : ℝ := (2 : ℝ) ^ C
  let K₁ := 16 * Real.exp (2 * A + 4) * (A ^ 3 + A ^ 4)
  let K₂ := 16 * Real.exp (2 * A + 2) * (A + A ^ 2)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNzero : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hp₁ : p ≤ 1 := by
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hA : 0 ≤ A := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) C).le
  have hnom : p ≤ A / N := LocalRigidityConsequences.nominal_marginal_bound hN hband
  have hnreal : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hmean : (n : ℝ) * p ≤ A := by
    have h := (le_div_iff₀ hNpos).mp hnom
    nlinarith only [mul_le_mul_of_nonneg_right hnreal hp, h]
  have hp2 : (n : ℝ) * p ^ 2 ≤ A ^ 2 / N := by
    calc
      _ ≤ (N : ℝ) * (A / N) ^ 2 :=
        mul_le_mul hnreal (pow_le_pow_left₀ hp hnom 2) (by positivity) hNpos.le
      _ = _ := by field_simp
  have hp3 : (n : ℝ) * p ^ 3 ≤ A ^ 3 / (N : ℝ) ^ 2 := by
    calc
      _ ≤ (N : ℝ) * (A / N) ^ 3 :=
        mul_le_mul hnreal (pow_le_pow_left₀ hp hnom 3) (by positivity) hNpos.le
      _ = _ := by field_simp
  have hp4 : ((n : ℝ) * p ^ 2) ^ 2 ≤ A ^ 4 / (N : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) * p ^ 2) hp2 2
    convert h using 1; ring
  have hsum : (n : ℝ) * p ^ 3 + ((n : ℝ) * p ^ 2) ^ 2 ≤
      (A ^ 3 + A ^ 4) / (N : ℝ) ^ 2 := by rw [add_div]; exact add_le_add hp3 hp4
  have hlinear : p + (n : ℝ) * p ^ 2 ≤ (A + A ^ 2) / N := by
    rw [add_div]; exact add_le_add hnom hp2
  have herror₁ : 16 * Real.exp (2 * A + 4) *
      ((n : ℝ) * p ^ 3 + ((n : ℝ) * p ^ 2) ^ 2) ≤ K₁ / (N : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 16 * Real.exp (2 * A + 4))
    convert h using 1; dsimp only [K₁]; ring
  have herror₂ : 16 * Real.exp (2 * A + 2) * |c₂| * (p + (n : ℝ) * p ^ 2) ≤
      K₂ * |c₂| / N := by
    have h := mul_le_mul_of_nonneg_left hlinear
      (by positivity : 0 ≤ 16 * Real.exp (2 * A + 2) * |c₂|)
    convert h using 1; dsimp only [K₂]; ring
  have hconv := actual_signed_measure_conversion hn hp hp₁ hmean β c₂
  have hK₁ : 0 ≤ K₁ := by dsimp only [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp only [K₂]; positivity
  have hcross₁ : 0 ≤ K₁ * (|c₂| / N) := by positivity
  have hcross₂ : 0 ≤ K₂ / (N : ℝ) ^ 2 := by positivity
  change (∑' k : ℕ, |(FiniteLawEmbedding.embed (finiteReference n p β) -
    QuadraticPoisson.reference ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2)) {k}|) ≤
      4 * |β - c₂| + (K₁ + K₂) * (1 / (N : ℝ) ^ 2 + |c₂| / N)
  simp only [div_eq_mul_inv] at herror₁ herror₂ hcross₁ hcross₂ ⊢
  nlinarith only [hconv, herror₁, herror₂, hcross₁, hcross₂]

theorem regular_card_eventually (C : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        2 ≤ (RegularStarts.regularStarts N L).card := by
  obtain ⟨NI, hirregular⟩ := RegularSetAsymptotic.irregular_count_critical C (1 / 2) (by norm_num)
  refine ⟨max 4 NI, by omega, ?_⟩
  intro N hN L hband
  have hi := hirregular N (by omega) L hband
  rw [← Real.sqrt_eq_rpow] at hi
  have hNfour : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
  have hsqrt : Real.sqrt N ≤ (N : ℝ) / 2 := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hcard : ((RegularStarts.irregularStarts N L).card : ℝ) +
      (RegularStarts.regularStarts N L).card = N := by
    exact_mod_cast RegularSetFinite.card_irregular_add_regular N L
  have hr : (2 : ℝ) ≤ (RegularStarts.regularStarts N L).card := by linarith
  exact_mod_cast hr

/-- The actual regular-set reference, with an explicit error in the actual
covariance parameter. Its arithmetic scale is not an input to this theorem. -/
theorem actual_regular_bound (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H c₂ : ℝ,
      let n := (RegularStarts.regularStarts N L).card
      let p : ℝ := (2 ^ L : ℝ)⁻¹
      (∑' k : ℕ, |(FiniteLawEmbedding.embed (RetainedReferenceTheorem.binomialReference H N L) -
        QuadraticPoisson.reference ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2)) {k}|) ≤
        4 * |RetainedReferenceTheorem.beta H N L - c₂| +
          errorConstant C * (1 / (N : ℝ) ^ 2 + |c₂| / N) := by
  obtain ⟨N₀, hN₀, hcard⟩ := regular_card_eventually C
  refine ⟨N₀, ?_⟩
  intro N hN L hband H c₂
  have hnN : (RegularStarts.regularStarts N L).card ≤ N := by
    exact (Finset.card_le_card (RegularStarts.regularStarts_subset N L)).trans_eq
      (RegularSetFinite.card_dyadicBlock N)
  simpa only [finiteReference, RetainedReferenceTheorem.binomialReference] using
    critical_bound (by omega : 2 ≤ N) (hcard N hN L hband) hnN hband
      (RetainedReferenceTheorem.beta H N L) c₂

end PaperP1.PoissonCharlierConversion
