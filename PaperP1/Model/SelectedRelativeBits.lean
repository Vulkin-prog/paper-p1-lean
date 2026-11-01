module

public import PaperP1.Algebra.SelectedBoundary
public import PaperP1.Probability.FairBinaryCube
public import PaperP1.Model.ConditionalRelativeBits

/-! # Actual relative signs on every injective subset of an independent window -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedRelativeBits

open MeasureTheory ProbabilityTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.DotTranspose PaperP1.SelectedBoundary PaperP1.RelativeSignIndependence
  PaperP1.ConditionalWindowRank PaperP1.ConditionalRelativeBits
  PaperP1.Model.InfiniteRademacher PaperP1.Probability.InfiniteCylinderTransfer

local instance selectedRelativeDecidable (P : Prop) : Decidable P := Classical.propDecidable P
local instance selectedRelativeMeasurableF2 : MeasurableSpace F₂ := ⊤

def rawWindowBits (x L : ℕ) (ω : InfiniteSample) : Fin (L + 1) → F₂ :=
  fun v ↦ infiniteValueBit ω (startCompleteVertexLabel x L v)

def selectedBits (x L : ℕ) {k : ℕ} (g : Fin (k + 1) → Fin (L + 1)) (ω : InfiniteSample) : Fin k → F₂ :=
  transpose (startCompleteBoundary k) (rawWindowBits x L ω ∘ g)

theorem boundary_single (L : ℕ) (i : Fin L) :
    startCompleteBoundary L (Pi.single i 1) = startIncidenceColumn i := by
  funext v
  simp [startCompleteBoundary_apply, Pi.single_apply]

theorem selectedBits_apply (x L : ℕ) {k : ℕ} (g : Fin (k + 1) → Fin (L + 1))
    (ω : InfiniteSample) (i : Fin k) :
    selectedBits x L g ω i =
      infiniteValueBit ω (startCompleteVertexLabel x L (g (startBaseVertex i))) +
        infiniteValueBit ω (startCompleteVertexLabel x L (g (startTipVertex i))) := by
  simp [selectedBits, transpose_apply, dotProduct, startCompleteBoundary_apply, Pi.single_apply,
    startIncidenceColumn, rawWindowBits, add_mul, Finset.sum_add_distrib, ite_mul]

theorem full_relative_identity (x L : ℕ) (ω : InfiniteSample) :
    transpose (startCompleteBoundary L) (rawWindowBits x L ω) = infiniteStartBits x L ω := by
  let σ := restrictToFinite (x + L) ω
  have hfull : transpose (startCompleteBoundary L) (rawWindowBits x L ω) = startSystem (x + L) x L σ := by
    funext i
    rw [transpose_apply, startSystem_apply_eq_sum_incidence]
    simp only [dotProduct, startCompleteBoundary_apply, Pi.single_apply, ite_mul, one_mul,
      zero_mul, sum_ite_eq', mem_univ, ite_true]
    change (∑ v, startIncidenceColumn i v * infiniteValueBit ω (startCompleteVertexLabel x L v)) = _
    apply sum_congr rfl
    intro v _
    rw [valueBit_restrictToFinite_eq_infiniteValueBit ω (startCompleteVertexLabel_le_cutoff le_rfl v)]
  rw [hfull]
  exact startSystem_restrict_eq le_rfl ω

theorem selectedBits_eq_postprocess (x L : ℕ) {k : ℕ} (g : Fin (k + 1) → Fin (L + 1)) (ω : InfiniteSample) :
    selectedBits x L g ω = transpose (rowEmbed g) (infiniteStartBits x L ω) := by
  rw [← full_relative_identity x L ω, selected_relative_identity]
  rfl

theorem measurable_selectedBits (x L : ℕ) {k : ℕ} (g : Fin (k + 1) → Fin (L + 1)) :
    Measurable (selectedBits x L g) := by
  have heq : selectedBits x L g = (transpose (rowEmbed g)) ∘ infiniteStartBits x L :=
    funext (selectedBits_eq_postprocess x L g)
  rw [heq]
  exact Measurable.of_discrete.comp (measurable_infiniteStartBits x L)

theorem map_selected_eq_fair {M x L k : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M)
    (hcard : (supportedIndices R (x - 1) (L + 1)).card ≤ 1)
    (g : Fin (k + 1) → Fin (L + 1)) (hg : Function.Injective g) :
    infiniteRademacherMeasure.map (selectedBits x L g) = Measure.pi (fun _ : Fin k ↦ coordinateMeasure) := by
  have heq : selectedBits x L g = (transpose (rowEmbed g)) ∘ infiniteStartBits x L :=
    funext (selectedBits_eq_postprocess x L g)
  rw [heq, ← Measure.map_map Measurable.of_discrete (measurable_infiniteStartBits x L),
    map_new_eq_fair hx hcut hR hcard]
  exact FairBinaryCube.map_transpose_eq (rowEmbed g) (rowEmbed_injective g hg)

theorem selected_independent_of_old {M x L k : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M)
    (hcard : (supportedIndices R (x - 1) (L + 1)).card ≤ 1)
    (g : Fin (k + 1) → Fin (L + 1)) :
    IndepFun (selectedBits x L g) (infiniteOldBits R) infiniteRademacherMeasure := by
  have heq : selectedBits x L g = (transpose (rowEmbed g)) ∘ infiniteStartBits x L :=
    funext (selectedBits_eq_postprocess x L g)
  rw [heq]
  exact (independent_of_old hx hcut hR hcard).comp (φ := transpose (rowEmbed g)) (ψ := id)
    Measurable.of_discrete measurable_id

theorem selected_independent_of_old_subset {M x L k : ℕ} {R Q : Finset ℕ}
    (hx : 0 < x) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M)
    (hcard : (supportedIndices R (x - 1) (L + 1)).card ≤ 1)
    (g : Fin (k + 1) → Fin (L + 1)) (hQ : Q ⊆ R) :
    IndepFun (selectedBits x L g) (infiniteOldBits Q) infiniteRademacherMeasure := by
  let restrict : (R → F₂) → (Q → F₂) := fun b n ↦ b ⟨n.val, hQ n.property⟩
  have h := (selected_independent_of_old hx hcut hR hcard g).comp (φ := id) (ψ := restrict)
    measurable_id Measurable.of_discrete
  exact h

end PaperP1.SelectedRelativeBits
