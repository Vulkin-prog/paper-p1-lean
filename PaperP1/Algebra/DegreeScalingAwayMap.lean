module

public import PaperP1.Algebra.DegreeScalingHomogeneousMap

/-! # Actual coordinate-chart maps under a scaling of homogeneous degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DegreeScalingAwayMap

open HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (D : ℕ) (f : G →+*ᵍ (fun n ↦ H (n * D)))

def map (b : A) : Away G b →+* Away H (f b) :=
  DegreeScalingHomogeneousMap.map D f (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩)

theorem map_mk {i : ℕ} {b : A} (hb : b ∈ G i) (n : ℕ) (x : A) (hx : x ∈ G (n • i)) :
    map D f b (Away.mk G hb n x hx) =
      Away.mk H (f.map_mem hb) n (f x)
        (by
          have h : f x ∈ H ((n • i) * D) := f.map_mem hx
          simpa only [smul_eq_mul, mul_assoc] using h) := by
  apply HomogeneousLocalization.val_injective
  change (DegreeScalingHomogeneousMap.map D f _ (Away.mk G hb n x hx)).val = _
  rw [DegreeScalingHomogeneousMap.map_val]
  simp only [Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    map_pow, GradedRingHom.coe_toRingHom]

end PaperP1.DegreeScalingAwayMap
