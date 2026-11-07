module

public import PaperP1.Model.RunReplicaSums

/-! # Nominal replica probabilities with the full formal-coordinate kernel

The nominal factor p^r uses the kernel of the actual colored row-relation
map, including internal row relations. No regularity or injectivity of
the occurrence centers is required. The effective relative-kernel formula
instead retains the actual heterogeneous marginals. Formal occurrence
coordinates stay distinct even when their natural-valued centers repeat.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.NominalRunReplicaFormula

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.Model.InfiniteRademacher PaperP1.RelativeSignIndependence

local instance nominalRunPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance nominalRunMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance nominalRunDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def rawKernelDimension {ι κ : Type*} [Fintype ι] (M Y L : ℕ)
    (x : ι → ℕ) (color : ι → κ) : ℕ :=
  Module.finrank F₂ (LinearMap.ker (relationMap (ColoredReplicaMass.jointSystem M Y L x color)))

theorem conditional_nominal_formula {ι κ : Type*} [Fintype ι] [Fintype κ]
    {M Y L : ℕ} (hYM : Y ≤ M) (x : ι → ℕ) (color : ι → κ)
    (b : ι → Fin L → F₂) (hcut : ∀ i, x i + L ≤ M) :
    (∫ ω, (∏ k, InfiniteReplicaFormula.conditionalBlock Y L x color b k ω)
      ∂infiniteRademacherMeasure) =
      ((2^L : ℝ)⁻¹)^Fintype.card ι *
      (if Compatible (ColoredReplicaMass.jointSystem M Y L x color)
        (ColoredReplicaMass.jointRhs b) then (1 : ℝ) else 0) *
      (2^rawKernelDimension M Y L x color : ℝ) := by
  rw [InfiniteReplicaFormula.integral_eq_finite hYM x color b hcut,
    ColoredReplicaMass.exact_nominal_formula]
  have hid : (2^(Fintype.card ι*L) : ℝ)⁻¹ = ((2^L : ℝ)⁻¹)^Fintype.card ι := by
    rw [inv_pow, ← pow_mul, Nat.mul_comm L (Fintype.card ι)]
  rw [div_eq_mul_inv, hid]
  unfold rawKernelDimension
  ring

theorem run_formula {ι κ : Type*} [Fintype ι] [Fintype κ]
    {M Y L : ℕ} (hYM : Y ≤ M) (hL : 0 < L) (x : ι → ℕ) (color : ι → κ)
    (hcut : ∀ i, x i + L ≤ M) :
    (∫ ω, (∏ k, RunReplicaSums.block Y L x color k ω) ∂infiniteRademacherMeasure) =
      ((2^L : ℝ)⁻¹)^Fintype.card ι *
      (if Compatible (ColoredReplicaMass.jointSystem M Y L x color)
        (ColoredReplicaMass.jointRhs (fun _ ↦ startRhs L)) then (1 : ℝ) else 0) *
      (2^rawKernelDimension M Y L x color : ℝ) := by
  simpa only [RunReplicaSums.conditionalBlock_eq Y L hL x color] using
    conditional_nominal_formula hYM x color (fun _ ↦ startRhs L) hcut

theorem heterogeneous_run_formula {ι κ : Type*} [Fintype ι] [Fintype κ]
    {M Y L : ℕ} (hYM : Y ≤ M) (hL : 0 < L) (x : ι → ℕ) (color : ι → κ)
    (hcut : ∀ i, x i + L ≤ M) :
    (∫ ω, (∏ k, RunReplicaSums.block Y L x color k ω) ∂infiniteRademacherMeasure) =
      (if Compatible (ColoredReplicaMass.jointSystem M Y L x color)
        (ColoredReplicaMass.jointRhs (fun _ ↦ startRhs L)) then (1 : ℝ) else 0) *
      (∏ i, InfiniteStarts.infiniteMarginal (x i) L) *
      (2^relativeNullity (ColoredRelativeFormula.rows M Y L x color) : ℝ) := by
  have hmass (i : ι) :
      infiniteRademacherMeasure.real {ω | infiniteStartBits (x i) L ω = startRhs L} =
        InfiniteStarts.infiniteMarginal (x i) L := by
    have hevent : {ω | infiniteStartBits (x i) L ω = startRhs L} =
        {ω | InfiniteStarts.infiniteStartIndicator (x i) L ω = true} := by
      ext ω
      exact RunReplicaSums.bits_iff_run hL ω
    rw [hevent]
    have hset : MeasurableSet {ω | InfiniteStarts.infiniteStartIndicator (x i) L ω = true} :=
      (measurableSet_singleton true).preimage (InfiniteStarts.measurable_infiniteStartIndicator (x i) L)
    symm
    simpa only [InfiniteStarts.infiniteMarginal, PaperP1.Probability.indicatorValue,
      Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using
      integral_indicator_one (μ:=infiniteRademacherMeasure) hset
  simpa only [RunReplicaSums.conditionalBlock_eq Y L hL x color, hmass] using
    InfiniteReplicaFormula.exact_relative_formula hYM x color (fun _ ↦ startRhs L) hcut

theorem companion_T22_7 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N Y L : ℕ) (hL : 0 < L) (x : ι → ℕ)
    (hx : ∀ i, x i ∈ dyadicBlock N) (color : ι → κ) :
    (∫ ω, (∏ k, RunReplicaSums.block Y L x color k ω) ∂infiniteRademacherMeasure) =
      ((2^L : ℝ)⁻¹)^Fintype.card ι *
      (if Compatible (ColoredReplicaMass.jointSystem (max Y (2*N+L)) Y L x color)
        (ColoredReplicaMass.jointRhs (fun _ ↦ startRhs L)) then (1 : ℝ) else 0) *
      (2^rawKernelDimension (max Y (2*N+L)) Y L x color : ℝ) := by
  apply run_formula (le_max_left _ _) hL x color
  intro i
  have hi := (mem_Ico.mp (hx i)).2
  have hmax := le_max_right Y (2*N+L)
  omega

end PaperP1.NominalRunReplicaFormula
