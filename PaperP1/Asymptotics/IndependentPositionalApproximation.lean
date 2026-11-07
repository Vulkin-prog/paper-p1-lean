module

public import PaperP1.Asymptotics.PositionalWeightedApproximation
public import PaperP1.Probability.PositionalPoissonRealization

/-! # The original weighted grid comparison for literal independent Poisson arrivals

Every fixed degree precedes the threshold. The threshold also precedes the
probability space and variables. The canonical finite product law supplies an
actual realization, and every weighted error series is proved summable.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentPositionalApproximation

open Finset MeasureTheory ProbabilityTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalPoissonRealization

open scoped NNReal

local instance configurationMeasurableSpace : MeasurableSpace (Configuration ℕ) := ⊤

/-- The original weighted grid comparison for any independent Poisson realization.
The threshold precedes the probability space and all Poisson variables. -/
theorem main_20_1 (C ε : ℝ) (hε : 0 < ε) :
    ∀ j : ℕ, ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let G := dyadicBlock N
      let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
      let p : ℕ → ℝ := fun _ ↦ (2 ^ L : ℝ)⁻¹
      let q := infiniteJointMoment L
      ∃ hp : ∀ x ∈ G, 0 ≤ p x - PositionalCompoundPoisson.incidence E q x,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : (↥G ⊕ ↥E) → Ω → ℕ),
        (∀ a, HasLaw (X a)
          (poissonMeasure (channelRate G E p q hp (fun e _ ↦ infiniteJointMoment_nonneg L e) a)) P) →
        iIndepFun X P →
        let error := fun z : G → ℕ ↦ (1 + ∑ x : G, (z x : ℝ)) ^ j *
          |infiniteRademacherMeasure.real
              {ω | ∀ x : G, (infiniteStartIndicator x.val L ω).toNat = z x} -
            P.real {ω | ∀ x : G, (∑ a : ↥G ⊕ ↥E, X a ω • channelJump G E a) x.val = z x}|
        Summable error ∧ (∑' z : G → ℕ, error z) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NP, _hNP, hpos⟩ := WeakPairIncidence.full_single_rates_positive C
  intro j
  obtain ⟨NA, _hNA, happrox⟩ := PositionalWeightedApproximation.uniform_coefficient_bound C ε hε j
  refine ⟨10 + NP + NA, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let G := dyadicBlock N
  let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
  let p : ℕ → ℝ := fun _ ↦ (2 ^ L : ℝ)⁻¹
  let q := infiniteJointMoment L
  let hp : ∀ x ∈ G, 0 ≤ p x - PositionalCompoundPoisson.incidence E q x :=
    fun x _ ↦ (hpos N (by omega) L hband (8 * (L + 1) : ℕ) x).le
  refine ⟨hp, ?_⟩
  intro Ω _ P _ X hX hInd
  let hq : ∀ e ∈ E, 0 ≤ q e := fun e _ ↦ infiniteJointMoment_nonneg L e
  let T := PositionalCompoundPoisson.target G E p q
  let A := ofFinite (PositionalStoppedLaw.actualLaw G L)
  have hT : PositivePositionalConvolution.IsProbability T :=
    PositionalCompoundPoisson.target_isProbability G E p q hp hq
  have hG : PositionalGroundSupport.Supported G T :=
    PositionalGroundSupport.supported_target G E p q (fun e he ↦
      (RetainedGoodEdges.good_pair_regular (by omega) e he).trans
        (RegularStarts.regularStarts_subset N L))
  have hA : PositionalGroundSupport.Supported G A := PositionalGroundSupport.supported_law G _ _
  have hLaw := hasLaw_single_pair_field G E p q hp hq P X hX hInd
  have hmass (z : G → ℕ) :
      P.real {ω | ∀ x : G, (∑ a : ↥G ⊕ ↥E, X a ω • channelJump G E a) x.val = z x} =
        coeff (PositionalGrid.encode G z) T :=
    grid_probability_of_hasLaw G T hT hG P _ hLaw z
  have hactual (z : G → ℕ) : coeff (PositionalGrid.encode G z) A =
      infiniteRademacherMeasure.real
        {ω | ∀ x : G, (infiniteStartIndicator x.val L ω).toNat = z x} := by
    have hevent :
        {ω | configuration G (fun x ↦ infiniteStartIndicator x L) ω = PositionalGrid.encode G z} =
          {ω | ∀ x : G, (infiniteStartIndicator x.val L ω).toNat = z x} := by
      ext ω
      exact PositionalGrid.configuration_eq_encode G _ ω z
    rw [show A = ofFinite (PositionalStoppedLaw.actualLaw G L) from rfl,
      coeff_ofFinite, PositionalStoppedLaw.actualLaw_coeff, hevent]
  have hcoeff :
      Summable (fun v : Configuration ℕ ↦ (1 + (PositionalCountProjection.totalCount v : ℝ)) ^ j *
        |coeff v A - coeff v T|) ∧
      (∑' v : Configuration ℕ, (1 + (PositionalCountProjection.totalCount v : ℝ)) ^ j *
        |coeff v A - coeff v T|) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    simpa only [A, G, T, E, p, q, coeff_ofFinite] using happrox N (by omega) L hband
  have hpoint (z : G → ℕ) :
      (1 + ∑ x : G, (z x : ℝ)) ^ j *
        |infiniteRademacherMeasure.real
            {ω | ∀ x : G, (infiniteStartIndicator x.val L ω).toNat = z x} -
          P.real {ω | ∀ x : G, (∑ a : ↥G ⊕ ↥E, X a ω • channelJump G E a) x.val = z x}| =
      (1 + (PositionalCountProjection.totalCount (PositionalGrid.encode G z) : ℝ)) ^ j *
        |coeff (PositionalGrid.encode G z) A - coeff (PositionalGrid.encode G z) T| := by
    rw [hmass z, hactual z, PositionalGrid.totalCount_encode, Nat.cast_sum]
  constructor
  · exact (hcoeff.1.comp_injective (PositionalGrid.encode_injective G)).congr
      (fun z ↦ (hpoint z).symm)
  · calc
      _ = ∑' z : G → ℕ,
          (1 + (PositionalCountProjection.totalCount (PositionalGrid.encode G z) : ℝ)) ^ j *
            |coeff (PositionalGrid.encode G z) A - coeff (PositionalGrid.encode G z) T| :=
        tsum_congr hpoint
      _ = ∑' z : G → ℕ, (1 + ∑ x : G, (z x : ℝ)) ^ j *
          |coeff (PositionalGrid.encode G z) A - coeff (PositionalGrid.encode G z) T| := by
        simp only [PositionalGrid.totalCount_encode, Nat.cast_sum]
      _ = _ := PositionalGrid.weighted_difference_eq G A T hA hG j
      _ ≤ _ := hcoeff.2

/-- A concrete product probability space realizes the same convergent comparison. -/
theorem main_20_1_canonical (C ε : ℝ) (hε : 0 < ε) :
    ∀ j : ℕ, ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let G := dyadicBlock N
      let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
      let p : ℕ → ℝ := fun _ ↦ (2 ^ L : ℝ)⁻¹
      let q := infiniteJointMoment L
      ∃ hp : ∀ x ∈ G, 0 ≤ p x - PositionalCompoundPoisson.incidence E q x,
      let error := fun z : G → ℕ ↦ (1 + ∑ x : G, (z x : ℝ)) ^ j *
        |infiniteRademacherMeasure.real
            {ω | ∀ x : G, (infiniteStartIndicator x.val L ω).toNat = z x} -
          (poissonProduct (channelRate G E p q hp (fun e _ ↦ infiniteJointMoment_nonneg L e))).val.real
            {ω | ∀ x : G, (∑ a : ↥G ⊕ ↥E, ω a • channelJump G E a) x.val = z x}|
      Summable error ∧ (∑' z : G → ℕ, error z) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  intro j
  obtain ⟨N₀, hN₀, h⟩ := main_20_1.{0} C ε hε j
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  obtain ⟨hp, hh⟩ := h N hN L hband
  refine ⟨hp, ?_⟩
  let G := dyadicBlock N
  let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
  let μ : (↥G ⊕ ↥E) → ℝ≥0 := channelRate G E (fun _ ↦ (2 ^ L : ℝ)⁻¹)
    (infiniteJointMoment L) hp (fun e _ ↦ infiniteJointMoment_nonneg L e)
  let P : Measure ((↥G ⊕ ↥E) → ℕ) := (poissonProduct μ).val
  have : IsProbabilityMeasure P := (poissonProduct μ).property
  have hX (a : ↥G ⊕ ↥E) : HasLaw (fun ω : (↥G ⊕ ↥E) → ℕ ↦ ω a)
      (poissonMeasure (μ a)) P := poissonProduct_hasLaw_eval μ a
  have hInd : iIndepFun (fun a (ω : (↥G ⊕ ↥E) → ℕ) ↦ ω a) P :=
    poissonProduct_independent μ
  exact hh ((↥G ⊕ ↥E) → ℕ) P (fun a ω ↦ ω a) hX hInd

end PaperP1.IndependentPositionalApproximation
