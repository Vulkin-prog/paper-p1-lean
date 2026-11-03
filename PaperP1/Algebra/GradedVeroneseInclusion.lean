module

public import PaperP1.Algebra.GradedVeroneseGrading
public import PaperP1.Algebra.DegreeScalingAwayMap
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! # The literal Veronese inclusion is admissible and is an isomorphism on every homogeneous chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseInclusion

open HomogeneousLocalization

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (D : ℕ) (hD : 0 < D)

def inclusion : GradedVeroneseGrading.piece G D →+*ᵍ (fun n ↦ G (n * D)) where
  __ := (GradedVeroneseAlgebra.veronese G D).val.toRingHom
  map_mem hp := hp

theorem inclusion_apply (p : GradedVeroneseAlgebra.veronese G D) : inclusion G D p = (p : A) := rfl

theorem irrelevant_le_radical :
    letI := GradedVeroneseGrading.grading G D hD
    (HomogeneousIdeal.irrelevant G).toIdeal ≤
      ((HomogeneousIdeal.irrelevant (GradedVeroneseGrading.piece G D)).toIdeal.map
        (inclusion G D).toRingHom).radical := by
  let := GradedVeroneseGrading.grading G D hD
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn x hx
  change x ∈ G n at hx
  have hxD : x ^ D ∈ G (n * D) := by
    simpa only [smul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded D hx
  let p : GradedVeroneseAlgebra.veronese G D := ⟨x ^ D, GradedVeroneseAlgebra.piece_mem G D n hxD⟩
  have hp : p ∈ GradedVeroneseGrading.piece G D n := hxD
  have hi := HomogeneousIdeal.mem_irrelevant_of_mem (GradedVeroneseGrading.piece G D) hn hp
  exact ⟨D, Ideal.mem_map_of_mem (inclusion G D).toRingHom hi⟩

theorem chart_injective (b : GradedVeroneseAlgebra.veronese G D) :
    letI := GradedVeroneseGrading.grading G D hD
    Function.Injective (DegreeScalingAwayMap.map D (inclusion G D) b) := by
  let := GradedVeroneseGrading.grading G D hD
  apply (injective_iff_map_eq_zero (DegreeScalingAwayMap.map D (inclusion G D) b)).mpr
  intro z hz
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  change DegreeScalingHomogeneousMap.map D (inclusion G D) _ (HomogeneousLocalization.mk c) = 0 at hz
  rw [DegreeScalingHomogeneousMap.map_mk] at hz
  have hv := (congrArg HomogeneousLocalization.val hz).trans (HomogeneousLocalization.val_zero (𝒜 := G))
  simp only [val_mk, DegreeScalingHomogeneousMap.fraction,
    inclusion_apply, Localization.mk_eq_mk'] at hv
  obtain ⟨⟨u, t, rfl⟩, ht⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hv
  apply HomogeneousLocalization.val_injective
  rw [val_mk, val_zero, Localization.mk_eq_mk']
  apply (IsLocalization.mk'_eq_zero_iff _ _).mpr
  refine ⟨⟨b ^ t, t, rfl⟩, ?_⟩
  apply Subtype.ext
  exact ht

theorem chart_surjective {i : ℕ} (b : GradedVeroneseAlgebra.veronese G D)
    (hb : b ∈ GradedVeroneseGrading.piece G D i) :
    letI := GradedVeroneseGrading.grading G D hD
    Function.Surjective (DegreeScalingAwayMap.map D (inclusion G D) b) := by
  let := GradedVeroneseGrading.grading G D hD
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective G ((inclusion G D).map_mem hb) z
  have ha' : a ∈ G ((n * i) * D) := by simpa only [smul_eq_mul, mul_assoc] using ha
  let a' : GradedVeroneseAlgebra.veronese G D := ⟨a, GradedVeroneseAlgebra.piece_mem G D (n * i) ha'⟩
  have haV : a' ∈ GradedVeroneseGrading.piece G D (n • i) := by
    change a ∈ G ((n • i) * D)
    simpa only [smul_eq_mul] using ha'
  refine ⟨Away.mk (GradedVeroneseGrading.piece G D) hb n a' haV, ?_⟩
  rw [DegreeScalingAwayMap.map_mk]
  apply HomogeneousLocalization.val_injective
  rfl

def chartEquiv {i : ℕ} (b : GradedVeroneseAlgebra.veronese G D)
    (hb : b ∈ GradedVeroneseGrading.piece G D i) :
    letI := GradedVeroneseGrading.grading G D hD
    Away (GradedVeroneseGrading.piece G D) b ≃+* Away G (b : A) := by
  let := GradedVeroneseGrading.grading G D hD
  exact RingEquiv.ofBijective (DegreeScalingAwayMap.map D (inclusion G D) b)
    ⟨chart_injective G D hD b, chart_surjective G D hD b hb⟩

end PaperP1.GradedVeroneseInclusion
