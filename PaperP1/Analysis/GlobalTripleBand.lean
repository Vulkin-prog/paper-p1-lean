module

public import PaperP1.Analysis.PrimeUnitMean
public import PaperP1.Arithmetic.PrimeTruncation
public import PaperP1.Analysis.ActualEulerBand
public import PaperP1.Analysis.ComplexEuler
public import PaperP1.Analysis.DyadicLogBands
public import PaperP1.Analysis.GeometricBandSplit
public import PaperP1.Analysis.QuantitativeEulerBand
public import PaperP1.Analysis.TrivialTripleBand
public import PaperP1.Analysis.WeightedPerronError

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GlobalTripleBand
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def budget (X : ℕ) (g : ℕ →* ℂ) : ℝ := PrimeUnitMean.frequencyBudget
  (FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) g) (ActualEulerBand.frequencyCutoff X)

theorem budget_nonneg (X : ℕ) (g : ℕ →* ℂ) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) : 0 ≤ budget X g :=
  PrimeUnitMean.frequency_budget_nonneg _ (ComplexEuler.total_continuous _ (FixedEulerTruncation.primes_prime X) g hg) _

theorem global_triple_bound :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ g : ℕ →* ℂ, (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → ∀ m : ℕ,
      ‖RealTripleConvolution.triple g X (PrimeTruncation.retained X (PrimeTruncation.cutoff 20 X))‖ ≤
        TrivialTripleBand.constant*(X : ℝ)*(4*Real.log (X : ℝ)/(2 : ℝ)^m)+
        (m : ℝ)*(ActualEulerBand.constant*(X : ℝ)*Real.sqrt (budget X g)+WeightedPerronError.combinedError X) := by
  obtain ⟨X₀,hX₀,hh⟩ := QuantitativeEulerBand.retained_band_bound
  refine ⟨X₀,hX₀,?_⟩
  intro X hX g hg m
  have hX2 := hX₀.trans hX
  let P := PrimeTruncation.retained X (PrimeTruncation.cutoff 20 X)
  let K := DyadicLogBands.count X
  let J := K-m
  let Z := ActualEulerBand.constant*(X : ℝ)*Real.sqrt (budget X g)+WeightedPerronError.combinedError X
  have hP : ∀ p ∈ P, p.Prime ∧ 2*p ≤ X := by
    intro p hp
    have hm := (mem_filter.mp hp).2
    exact ⟨hm.1,hm.2.2⟩
  have hband (j : ℕ) := DyadicLogBands.band_bounds X hX2 P hP j
  have hsmall (j : ℕ) : ‖RealTripleConvolution.triple g X (DyadicLogBands.band X P j)‖ ≤
      TrivialTripleBand.constant*(X : ℝ)*DyadicLogBands.scale j := by
    apply TrivialTripleBand.band_norm_bound X hX2 g hg _ (DyadicLogBands.scale_ge_log_two j) _
    intro p hp
    have hm := hP p (DyadicLogBands.band_subset X P j hp)
    exact ⟨hm.1,hm.2,hband j p hp⟩
  have hbig (j : ℕ) : ‖RealTripleConvolution.triple g X (DyadicLogBands.band X P j)‖ ≤ Z :=
    hh X hX g hg _ (DyadicLogBands.scale_ge_log_two j) _ (DyadicLogBands.band_subset X P j) (hband j)
  have hZ : 0 ≤ Z := by
    have hc := ActualEulerBand.constant_pos
    have he := WeightedPerronError.combinedError_nonneg X
    dsimp only [Z]
    positivity
  have hearly : (∑ j ∈ range J, ‖RealTripleConvolution.triple g X (DyadicLogBands.band X P j)‖) ≤
      TrivialTripleBand.constant*(X : ℝ)*(4*Real.log (X : ℝ)/(2 : ℝ)^m) := by
    calc
      _ ≤ ∑ j ∈ range J, TrivialTripleBand.constant*(X : ℝ)*DyadicLogBands.scale j := sum_le_sum (fun j hj ↦ hsmall j)
      _ = (TrivialTripleBand.constant*(X : ℝ))*(∑ j ∈ range J, DyadicLogBands.scale j) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (GeometricBandSplit.early_sum_bound X hX2 m)
        (mul_nonneg TrivialTripleBand.constant_pos.le (Nat.cast_nonneg X))
  have hlate : (∑ j ∈ range (K-J), ‖RealTripleConvolution.triple g X (DyadicLogBands.band X P (J+j))‖) ≤ (m : ℝ)*Z := by
    calc
      _ ≤ ∑ j ∈ range (K-J), Z := sum_le_sum (fun j hj ↦ hbig (J+j))
      _ = ((K-J : ℕ) : ℝ)*Z := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast GeometricBandSplit.late_count X m) hZ
  calc
    _ ≤ ∑ j ∈ range K, ‖RealTripleConvolution.triple g X (DyadicLogBands.band X P j)‖ := by
      rw [DyadicLogBands.triple_partition X hX2 g P hP]
      exact norm_sum_le _ _
    _ = (∑ j ∈ range J, ‖RealTripleConvolution.triple g X (DyadicLogBands.band X P j)‖)+
        ∑ j ∈ range (K-J), ‖RealTripleConvolution.triple g X (DyadicLogBands.band X P (J+j))‖ :=
      GeometricBandSplit.range_split X m _
    _ ≤ _ := add_le_add hearly hlate
end PaperP1.GlobalTripleBand
