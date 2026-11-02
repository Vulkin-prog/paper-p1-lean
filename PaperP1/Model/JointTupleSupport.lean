module

public import PaperP1.Model.PrescribedRunMass
public import PaperP1.Combinatorics.FiniteFamilyEnumeration
public import PaperP1.Probability.StoppedFiniteLaw

/-! # Actual Boolean joint moments depend only on tuple support, including repetitions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.JointTupleSupport

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Probability
  PaperP1.FiniteFamilyEnumeration

theorem product_image {α β Ω : Type*} [DecidableEq β] (G : Finset α) (g : α → β)
    (J : β → Ω → Bool) (ω : Ω) :
    (∏ i ∈ G, (indicatorValue (J (g i) ω) : ℝ)) =
      ∏ x ∈ G.image g, (indicatorValue (J x ω) : ℝ) := by
  classical
  rw [indicator_product_eq_indicator (fun i ↦ J (g i)) G ω,
    indicator_product_eq_indicator J (G.image g) ω]
  have h : (∀ x ∈ G.image g, J x ω = true) ↔ ∀ i ∈ G, J (g i) ω = true := by simp
  by_cases ha : ∀ i ∈ G, J (g i) ω = true
  · simp only [ite_eq_left ha, ite_eq_left (h.mpr ha)]
  · have hb : ¬ ∀ x ∈ G.image g, J x ω = true := fun hb ↦ ha (h.mp hb)
    simp only [ite_eq_right ha, ite_eq_right hb]

theorem family_eq_support {s : ℕ} (L : ℕ) (x : Fin s → ℕ) :
    infiniteFamilyJointMoment L x = infiniteJointMoment L (tupleSet x) := by
  unfold infiniteFamilyJointMoment infiniteJointMoment
  congr 1
  funext ω
  exact product_image univ x (fun y ↦ infiniteStartIndicator y L) ω

theorem prescribed_eq_support {s L : ℕ} (x : Fin s → ℕ) (hL : 0 < L) :
    PrescribedTupleMass.joint L (fun _ ↦ Affine.startRhs L) x = infiniteJointMoment L (tupleSet x) := by
  rw [PrescribedRunMass.joint_eq_infinite _ hL, family_eq_support]

theorem constant_one_support (x : ℕ) : tupleSet (fun _ : Fin 1 ↦ x) = {x} := by
  simp [tupleSet]

theorem snoc_one_support (x z : ℕ) : tupleSet (PrescribedTupleMass.append (fun _ : Fin 1 ↦ x) z) = {x, z} := by
  simp [tupleSet, Finset.univ_fin2, PrescribedTupleMass.append, Fin.snoc]

end PaperP1.JointTupleSupport
