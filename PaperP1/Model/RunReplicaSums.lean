module

public import PaperP1.Model.InfiniteReplicaPositiveSum
public import PaperP1.Model.InfiniteStarts

/-! # Replica blocks and positive sums specialize exactly to the original run-start events -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RunReplicaSums

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteRademacher
  PaperP1.Model.InfiniteStarts PaperP1.InfiniteReplicaFormula PaperP1.SmallPrimeFiltration
  PaperP1.RelativeSignIndependence PaperP1.Probability.InfiniteCylinderTransfer

local instance runReplicaSumsMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance runReplicaSumsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem bits_iff_run {x L : ℕ} (hL : 0 < L) (ω : InfiniteSample) :
    infiniteStartBits x L ω = startRhs L ↔ infiniteStartIndicator x L ω = true := by
  rw [← startSystem_restrict_eq (M := x + L) le_rfl ω,
    ← startIndicator_restrict_eq (M := x + L) ω le_rfl, startIndicator_eq_true_iff]
  exact startSystem_eq_startRhs_iff _ hL

def block {ι κ : Type*} (Y L : ℕ) (x : ι → ℕ) (color : ι → κ) (k : κ) : InfiniteSample → ℝ :=
  condExp (primeFiltration Y) infiniteRademacherMeasure
    (fun ω ↦ if ∀ i, color i = k → infiniteStartIndicator (x i) L ω = true then (1 : ℝ) else 0)

theorem conditionalBlock_eq {ι κ : Type*} (Y L : ℕ) (hL : 0 < L) (x : ι → ℕ)
    (color : ι → κ) (k : κ) : conditionalBlock Y L x color (fun _ ↦ startRhs L) k = block Y L x color k := by
  unfold conditionalBlock block
  congr 1
  funext ω
  simp_rw [bits_iff_run hL]

def randomSum {κ : Type*} [Fintype κ] {r : ℕ} (Y L : ℕ) (color : Fin r → κ)
    (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ) (ω : InfiniteSample) : ℝ :=
  ∑ x ∈ A, w x * ∏ k, block Y L x color k ω

theorem sum_eq {κ : Type*} [Fintype κ] {r : ℕ} (Y L : ℕ) (hL : 0 < L) (color : Fin r → κ)
    (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ) :
    InfiniteReplicaPositiveSum.randomSum Y L color (fun _ ↦ startRhs L) A w = randomSum Y L color A w := by
  funext ω
  unfold InfiniteReplicaPositiveSum.randomSum randomSum
  simp_rw [conditionalBlock_eq Y L hL]

theorem regular_formula {ι κ : Type*} [Fintype ι] [Fintype κ] {M Y L : ℕ}
    (hYM : Y ≤ M) (hL : 0 < L) (x : ι → ℕ) (color : ι → κ) (hcut : ∀ i, x i + L ≤ M)
    (hregular : ∀ i, Module.finrank F₂ (effectiveRowSpace (startSystem M (x i) L)) = L) :
    (∫ ω, (∏ k, block Y L x color k ω) ∂infiniteRademacherMeasure) =
      ((2 ^ L : ℝ)⁻¹) ^ Fintype.card ι *
      (if Compatible (ColoredReplicaMass.jointSystem M Y L x color)
        (ColoredReplicaMass.jointRhs (fun _ ↦ startRhs L)) then (1 : ℝ) else 0) *
      (2 ^ relativeNullity (ColoredRelativeFormula.rows M Y L x color) : ℝ) := by
  classical
  have h := InfiniteReplicaFormula.regular_formula hYM x color (fun _ ↦ startRhs L) hcut hregular
  simpa only [conditionalBlock_eq Y L hL x color] using h

end PaperP1.RunReplicaSums
