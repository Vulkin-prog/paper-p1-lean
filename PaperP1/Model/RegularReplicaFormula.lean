module

public import PaperP1.Model.RunReplicaSums
public import PaperP1.Model.RegularStarts

/-! # The printed p^r replica formula for actual regular run windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularReplicaFormula

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteRademacher

local instance regularReplicaFormulaTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance regularReplicaFormulaMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance regularReplicaFormulaDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem companion_T22_7 {ι κ : Type*} [Fintype ι] [Fintype κ] (N Y L : ℕ) (hL : 0 < L)
    (x : ι → ℕ) (hx : ∀ i, x i ∈ RegularStarts.regularStarts N L) (color : ι → κ) :
    (∫ ω, (∏ k, RunReplicaSums.block Y L x color k ω) ∂infiniteRademacherMeasure) =
      ((2 ^ L : ℝ)⁻¹) ^ Fintype.card ι *
      (if Compatible (ColoredReplicaMass.jointSystem (max Y (2 * N + L)) Y L x color)
        (ColoredReplicaMass.jointRhs (fun _ ↦ startRhs L)) then (1 : ℝ) else 0) *
      (2 ^ relativeNullity (ColoredRelativeFormula.rows (max Y (2 * N + L)) Y L x color) : ℝ) := by
  have hcut : ∀ i, x i + L ≤ max Y (2 * N + L) := by
    intro i
    have hi := (mem_Ico.mp (RegularStarts.mem_regularStarts.mp (hx i)).1).2
    have hb := le_max_right Y (2 * N + L)
    omega
  have hregular (i : ι) : Module.finrank F₂ (effectiveRowSpace (startSystem (max Y (2 * N + L)) (x i) L)) = L := by
    rw [← finrank_squareClassSpace_eq_effectiveRows (hcut i)]
    exact (RegularStarts.mem_regularStarts.mp (hx i)).2
  exact RunReplicaSums.regular_formula (le_max_left _ _) hL x color hcut hregular

end PaperP1.RegularReplicaFormula
