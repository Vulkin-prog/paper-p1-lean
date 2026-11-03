module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-! # A generic algebra generator identifies the actual field of fractions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FractionFieldFromGenericGenerator

theorem closure_eq_top {R K A E : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [CommRing A] [Algebra R A] [Field E] [Algebra K E]
    (φ : A →+* E) (hcomm : ∀ r, φ (algebraMap R A r) = algebraMap K E (algebraMap R K r))
    (a : A) (hgen : Algebra.adjoin K {φ a} = ⊤) : Subfield.closure (Set.range φ) = ⊤ := by
  let F := Subfield.closure (Set.range φ)
  have hbase : ∀ k : K, algebraMap K E k ∈ F := by
    intro k
    obtain ⟨r, t, _ht, hrt⟩ := IsFractionRing.div_surjective R k
    rw [← hrt, map_div₀, ← hcomm r, ← hcomm t]
    exact F.div_mem (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)
  let B : Subalgebra K E := {
    carrier := F
    zero_mem' := F.zero_mem
    one_mem' := F.one_mem
    add_mem' := F.add_mem
    mul_mem' := F.mul_mem
    algebraMap_mem' := hbase }
  have ha : φ a ∈ B := Subfield.subset_closure ⟨a, rfl⟩
  have hle : Algebra.adjoin K {φ a} ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr ha)
  rw [hgen] at hle
  exact top_unique (fun z _ ↦ hle (show z ∈ (⊤ : Subalgebra K E) from trivial))

theorem isFractionRing {R K A E : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [CommRing A] [Algebra R A] [Field E] [Algebra K E]
    (φ : A →+* E) (hφ : Function.Injective φ)
    (hcomm : ∀ r, φ (algebraMap R A r) = algebraMap K E (algebraMap R K r))
    (a : A) (hgen : Algebra.adjoin K {φ a} = ⊤) :
    let : Algebra A E := φ.toAlgebra
    IsFractionRing A E := by
  let : Algebra A E := φ.toAlgebra
  have : IsDomain A := hφ.isDomain φ
  have : FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective A E).mpr hφ
  let f : FractionRing A →+* E := IsFractionRing.lift hφ
  have htop : f.fieldRange = ⊤ :=
    (IsFractionRing.lift_fieldRange hφ).trans (closure_eq_top φ hcomm a hgen)
  have hsurj : Function.Surjective f := RingHom.fieldRange_eq_top_iff.mp htop
  apply IsFractionRing.of_field
  intro z
  obtain ⟨w, rfl⟩ := hsurj z
  obtain ⟨x, y, _hy, hxy⟩ := IsFractionRing.div_surjective A w
  refine ⟨x, y, ?_⟩
  rw [← hxy, map_div₀]
  simp only [f, IsFractionRing.lift_algebraMap]
  rfl

end PaperP1.FractionFieldFromGenericGenerator
