module

public import PaperP1.Model.PrescribedTupleMass
public import PaperP1.Model.RegularAffineBounds

/-! # Literal one-coordinate seed families and their exact affine masses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SingletonSeedMass

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.PrescribedTupleMass PaperP1.RegularAffineBounds
  PaperP1.WindowFamilyConditional PaperP1.RelativeSignIndependence

local instance singletonSeedMassMeasurableF2 : MeasurableSpace F₂ := ⊤

abbrev singletonTuple (x : ℕ) : Fin 1 → ℕ := fun _ ↦ x

def seeds (S : Finset ℕ) : Finset (Fin 1 → ℕ) := S.image singletonTuple

theorem singleton_injective : Function.Injective singletonTuple := by
  intro x y hxy
  exact congrFun hxy 0

theorem joint_singleton {L : ℕ} (c : ℕ → Fin L → F₂) (x : ℕ) :
    joint L c (singletonTuple x) = affineWindowMass x L (c x) := by
  unfold joint affineWindowMass
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, sourceEvent, singletonTuple]
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

theorem sum_seeds {L : ℕ} (c : ℕ → Fin L → F₂) (S : Finset ℕ) :
    (∑ x ∈ seeds S, joint L c x) = ∑ x ∈ S, affineWindowMass x L (c x) := by
  rw [seeds, sum_image (fun _ _ _ _ h ↦ singleton_injective h)]
  apply sum_congr rfl
  intro x _
  exact joint_singleton c x

theorem seeds_coordinates (G S : Finset ℕ) (hS : S ⊆ G) : ∀ x ∈ seeds S, ∀ i, x i ∈ G := by
  intro x hx i
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
  exact hS hz

end PaperP1.SingletonSeedMass
