module

public import PaperP1.Combinatorics.FiniteFamilyEnumeration
public import PaperP1.Model.PrescribedRunMass
public import PaperP1.Combinatorics.TuplePositions

/-! # Canonical tuple representatives of actual unordered run families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RunFamilyEnumeration

open Finset PaperP1.FiniteFamilyEnumeration PaperP1.Model.InfiniteStarts

local instance runFamilyEnumerationDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def canonical (r : ℕ) (I : Finset ℕ) : Fin r → ℕ :=
  if h : I.card = r then centres I h else fun _ ↦ 0

def tuples (F : Finset (Finset ℕ)) (r : ℕ) : Finset (Fin r → ℕ) := F.image (canonical r)

theorem canonical_eq {r : ℕ} {I : Finset ℕ} (hI : I.card = r) :
    canonical r I = centres I hI := by rw [canonical, dite_eq_left hI]

theorem canonical_values {r : ℕ} {I : Finset ℕ} (hI : I.card = r) :
    tupleSet (canonical r I) = I := by rw [canonical_eq hI, centres_tupleSet]

theorem canonical_injective {r : ℕ} {I : Finset ℕ} (hI : I.card = r) :
    Function.Injective (canonical r I) := by rw [canonical_eq hI]; exact centres_injective I hI

theorem familyJoint_eq_values {r : ℕ} (L : ℕ) (x : Fin r → ℕ) (hx : Function.Injective x) :
    infiniteFamilyJointMoment L x = infiniteJointMoment L (tupleSet x) := by
  unfold infiniteFamilyJointMoment infiniteJointMoment
  congr 1
  funext ω
  rw [tupleSet, prod_image hx.injOn]

theorem canonical_joint {r : ℕ} (L : ℕ) {I : Finset ℕ} (hI : I.card = r) :
    infiniteFamilyJointMoment L (canonical r I) = infiniteJointMoment L I := by
  rw [familyJoint_eq_values L _ (canonical_injective hI), canonical_values hI]

theorem prescribed_canonical_joint {r L : ℕ} (hL : 0 < L) {I : Finset ℕ} (hI : I.card = r) :
    PrescribedTupleMass.joint L (fun _ ↦ Affine.startRhs L) (canonical r I) = infiniteJointMoment L I := by
  rw [PrescribedRunMass.joint_eq_infinite _ hL, canonical_joint L hI]

theorem tuples_coordinates {r : ℕ} (G : Finset ℕ) (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ G ∧ I.card = r) : ∀ x ∈ tuples F r, ∀ i, x i ∈ G := by
  intro x hx i
  obtain ⟨I, hI, rfl⟩ := mem_image.mp hx
  rw [canonical_eq (hF I hI).2]
  exact centres_mem G I (hF I hI).2 (hF I hI).1 i

theorem sum_tuples_joint {r L : ℕ} (hL : 0 < L) (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I.card = r) :
    (∑ x ∈ tuples F r, PrescribedTupleMass.joint L (fun _ ↦ Affine.startRhs L) x) =
      ∑ I ∈ F, infiniteJointMoment L I := by
  unfold tuples
  rw [sum_image]
  · exact sum_congr rfl (fun I hI ↦ prescribed_canonical_joint hL (hF I hI))
  · intro I hI J hJ h
    have hv := congrArg tupleSet h
    simpa only [canonical_values (hF I hI), canonical_values (hF J hJ)] using hv

theorem seeded_tuple_mem {s k : ℕ} (G : Finset ℕ) (F : Finset (Finset ℕ))
    (hF : ∀ D ∈ F, D ⊆ G ∧ D.card = s) (I : Finset ℕ)
    (hIG : I ⊆ G) (hI : I.card = s + k) {D : Finset ℕ} (hD : D ∈ F) (hDI : D ⊆ I) :
    canonical (s + k) I ∈ TuplePositions.allPositions G (tuples F s) k := by
  let eD := enumeration D (hF D hD).2
  let eI := enumeration I hI
  let f : Fin s → Fin (s + k) := fun i ↦ eI.symm ⟨(eD i).val, hDI (eD i).property⟩
  have he (i : Fin s) : centres I hI (f i) = centres D (hF D hD).2 i := by
    exact congrArg Subtype.val (eI.apply_symm_apply ⟨(eD i).val, hDI (eD i).property⟩)
  have hf : Function.Injective f := by
    intro i j hij
    apply eD.injective
    apply Subtype.ext
    have h := congrArg (centres I hI) hij
    change centres D (hF D hD).2 i = centres D (hF D hD).2 j
    simpa only [he] using h
  apply TuplePositions.of_injected_seed G (tuples F s) (tuples_coordinates G F hF)
    (canonical (s + k) I)
    (by rw [canonical_eq hI]; exact centres_mem G I hI hIG)
    (canonical_injective hI) f hf
  have hseed : (fun i ↦ canonical (s + k) I (f i)) = canonical s D := by
    funext i
    rw [canonical_eq hI, canonical_eq (hF D hD).2]
    exact he i
  rw [hseed]
  exact mem_image.mpr ⟨D, hD, rfl⟩

end PaperP1.RunFamilyEnumeration
