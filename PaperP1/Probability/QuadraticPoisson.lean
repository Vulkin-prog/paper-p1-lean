module

public import PaperP1.Probability.PoissonSequence
public import PaperP1.Algebra.CharlierQuadratic

/-! # The actual quadratic Poisson signed reference and its positivity domain

Translation by one is convolution by δ₁; subtracting the identity is
convolution by Δ=δ₁-δ₀. The reference identity below is an equality of
actual signed measures, not just a formal coefficient expression.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticPoisson

open MeasureTheory ProbabilityTheory AtomicSignedLaw PoissonSequence CharlierQuadratic

def shiftMap : SignedMeasure ℕ →ₗ[ℝ] SignedMeasure ℕ := VectorMeasure.mapₗ Nat.succ

def differenceMap : SignedMeasure ℕ →ₗ[ℝ] SignedMeasure ℕ := shiftMap - LinearMap.id

def poissonSigned (μ : ℝ) : SignedMeasure ℕ := ofSequence (mass μ)

def poissonLaw (μ : ℝ) (hμ : 0 ≤ μ) : ProbabilityMeasure ℕ :=
  ⟨poissonMeasure ⟨μ, hμ⟩, ProbabilityTheory.instIsProbabilityMeasureNatPoissonMeasure _⟩

def reference (μ α : ℝ) : SignedMeasure ℕ := ofSequence (quadraticMass μ α)

theorem ofSequence_shift {a : ℕ → ℝ} (ha : Summable a) :
    ofSequence (shift a) = shiftMap (ofSequence a) := by
  apply signedMeasure_ext_singleton
  intro k
  rw [ofSequence_singleton (hasSum_shift ha.hasSum).summable]
  change shift a k = (ofSequence a).map Nat.succ {k}
  rw [VectorMeasure.map_apply _ (measurable_of_countable Nat.succ) (measurableSet_singleton k)]
  cases k with
  | zero =>
    have hpre : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by ext n; simp
    rw [hpre]
    simp
  | succ k =>
    have hpre : Nat.succ ⁻¹' ({k + 1} : Set ℕ) = {k} := by ext n; simp
    rw [hpre, ofSequence_singleton ha k, shift_succ]

theorem ofSequence_secondDifference {a : ℕ → ℝ} (ha : Summable a) :
    ofSequence (secondDifference a) = differenceMap (differenceMap (ofSequence a)) := by
  have hs := (hasSum_shift ha.hasSum).summable
  have hss := (hasSum_shift hs.hasSum).summable
  have hid : secondDifference a = shift (shift a) - (2 : ℝ) • shift a + a := by
    funext k
    simp only [secondDifference, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hc : Summable ((2 : ℝ) • shift a) := hs.mul_left 2
  rw [hid, ofSequence_add (a := shift (shift a) - (2 : ℝ) • shift a) (b := a) (hss.sub hc) ha,
    ofSequence_sub (a := shift (shift a)) (b := (2 : ℝ) • shift a) hss hc, ofSequence_smul,
    ofSequence_shift hs, ofSequence_shift ha]
  simp only [differenceMap, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  module

theorem poissonSigned_eq_poissonMeasure (μ : ℝ) (hμ : 0 ≤ μ) :
    poissonSigned μ = (poissonLaw μ hμ : Measure ℕ).toSignedMeasure := by
  apply signedMeasure_ext_singleton
  intro k
  rw [poissonSigned, ofSequence_singleton (hasSum_mass μ hμ).summable,
    Measure.toSignedMeasure_apply_measurable (measurableSet_singleton k)]
  exact (poissonMeasure_real_singleton ⟨μ, hμ⟩ k).symm

theorem reference_eq_poisson_plus_secondDifference (μ α : ℝ) (hμ : 0 ≤ μ) :
    reference μ α = poissonSigned μ +
      (α / 2) • differenceMap (differenceMap (poissonSigned μ)) := by
  have hm := (hasSum_mass μ hμ).summable
  have hd := (hasSum_secondDifference (hasSum_mass μ hμ)).summable
  have hid : quadraticMass μ α = mass μ + (α / 2) • secondDifference (mass μ) := by
    funext k
    rfl
  have hc : Summable ((α / 2) • secondDifference (mass μ)) := hd.mul_left (α / 2)
  rw [reference, hid, ofSequence_add hm hc, ofSequence_smul,
    ofSequence_secondDifference hm]
  rfl

theorem reference_total_mass (μ α : ℝ) (hμ : 0 ≤ μ) : reference μ α Set.univ = 1 := by
  rw [reference, ofSequence_univ (hasSum_quadraticMass μ α hμ).summable]
  exact (hasSum_quadraticMass μ α hμ).tsum_eq

theorem reference_singleton (μ α : ℝ) (hμ : 0 < μ) (k : ℕ) :
    reference μ α {k} = Real.exp (-μ) * μ ^ k / (k.factorial : ℝ) *
      (1 + α / (2 * μ ^ 2) * (((k : ℝ) - μ) ^ 2 - k)) := by
  rw [reference, ofSequence_singleton (hasSum_quadraticMass μ α hμ.le).summable,
    quadraticMass_formula μ α hμ.ne']
  rfl

/-- Full article Lemma 8.1: an actual probability measure exists exactly
in the stated parameter interval. The endpoint values are included. -/
theorem main_8_1 (μ α : ℝ) (hμ : 0 < μ) :
    AtomicSignedLaw.IsProbability (reference μ α) ↔
      0 ≤ α ∧ α ≤ 2 * μ ^ 2 / (μ + theta μ * (1 - theta μ)) := by
  rw [reference, isProbability_ofSequence_iff (hasSum_quadraticMass μ α hμ.le)]
  have hid : (∀ k : ℕ, 0 ≤ quadraticMass μ α k) ↔
      ∀ k : ℕ, 0 ≤ 1 + α / (2 * μ ^ 2) * quadratic μ k := by
    apply forall_congr'
    intro k
    rw [quadraticMass_formula μ α hμ.ne']
    exact mul_nonneg_iff_of_pos_left (mass_pos μ hμ k)
  rw [hid]
  exact bracket_nonnegative_iff μ α hμ

theorem main_8_1_fract (μ α : ℝ) (hμ : 0 < μ) :
    AtomicSignedLaw.IsProbability (reference μ α) ↔
      0 ≤ α ∧ α ≤ 2 * μ ^ 2 / (μ + Int.fract μ * (1 - Int.fract μ)) := by
  simpa only [theta_eq_fract μ hμ.le] using main_8_1 μ α hμ

end PaperP1.QuadraticPoisson
