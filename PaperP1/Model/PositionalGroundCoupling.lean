module

public import PaperP1.Model.PositionalStoppedLaw
public import PaperP1.Probability.PositionalFiniteCoupling

/-! # Actual original-field coupling across nested finite grounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalGroundCoupling

open Finset MeasureTheory PaperP1.Algebra PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.FiniteConvolutionAlgebra PaperP1.PositionalFiniteLaw
  PaperP1.PositionalStoppedLaw PaperP1.Probability.CylinderExpectations
  PaperP1.Probability.InfiniteCylinderTransfer

local instance positionalGroundCouplingDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_law (G : Finset ℕ) (L M : ℕ) (hcut : ∀ x ∈ G, x + L ≤ M) :
    actualLaw G L = law G (cylinderProbability M).weight (fun x ↦ startIndicator x L) := by
  ext v
  rw [actualLaw_coeff]
  symm
  have he : (law G (cylinderProbability M).weight (fun x ↦ startIndicator x L)).coeff v =
      finiteExpectation (cylinderProbability M).weight
        (fun ω ↦ if configuration G (fun x ↦ startIndicator x L) ω = v then 1 else 0) := by
    unfold law
    simp_rw [scalar_mul_atom]
    simp [AddMonoidAlgebra.coeff_sum, Finsupp.single_apply, finiteExpectation]
  rw [he, ← infiniteCylinder_event]
  congr 1
  ext ω
  change configuration G (fun x ↦ startIndicator x L) (restrictToFinite M ω) = v ↔
    configuration G (fun x ↦ infiniteStartIndicator x L) ω = v
  rw [configuration_restrict G L M hcut ω]

theorem restoration_bound (G H : Finset ℕ) (hGH : G ⊆ H) (L : ℕ) :
    l1Norm (actualLaw H L - actualLaw G L) ≤ 2 * ∑ x ∈ H \ G, infiniteMarginal x L := by
  let M := H.sup fun x ↦ x + L
  have hcutH (x : ℕ) (hx : x ∈ H) : x + L ≤ M := le_sup (f := fun x ↦ x + L) hx
  have hcutG (x : ℕ) (hx : x ∈ G) : x + L ≤ M := hcutH x (hGH hx)
  rw [finite_law H L M hcutH, finite_law G L M hcutG]
  apply (PositionalFiniteCoupling.restoration_bound (cylinderProbability M) G H hGH
    (fun x ↦ startIndicator x L)).trans_eq
  congr 1
  apply sum_congr (by congr!)
  intro x hx
  exact (infiniteMarginal_eq_finite (hcutH x (sdiff_subset hx))).symm

theorem dyadic_disagreement_bound {N L : ℕ} (G H : Finset ℕ) (hGH : G ⊆ H)
    (hH : H ⊆ dyadicBlock N) :
    l1Norm (actualLaw H L - actualLaw G L) ≤ 2 * CountObservables.countDisagreement H G L := by
  have hG := hGH.trans hH
  rw [finite_law H L (dyadicCutoff N L) (CountObservables.dyadic_subset_cutoff hH),
    finite_law G L (dyadicCutoff N L) (CountObservables.dyadic_subset_cutoff hG),
    CountObservables.countDisagreement_eq_finite hH hG]
  exact PositionalFiniteCoupling.coupling (cylinderProbability (dyadicCutoff N L)) G H hGH
    (fun x ↦ startIndicator x L)

end PaperP1.PositionalGroundCoupling
