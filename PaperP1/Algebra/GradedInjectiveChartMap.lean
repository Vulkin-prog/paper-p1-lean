module

public import PaperP1.Algebra.GradedDehomogenization

/-! # An injective graded ring map is injective on every actual homogeneous coordinate chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedInjectiveChartMap

open HomogeneousLocalization

variable {A B : Type*} [CommRing A] [CommRing B]

theorem localization_zero_of_power (f : A →+* B) (hf : Function.Injective f)
    (D : ℕ) (hD : 0 < D) (b : A) (z : B) (hfz : f b = z ^ D) (n : ℕ) (a : A)
    (h : (Localization.mk (f a) ⟨z ^ (n * D), n * D, rfl⟩ : Localization.Away z) = 0) :
    (Localization.mk a ⟨b ^ n, n, rfl⟩ : Localization.Away b) = 0 := by
  rw [Localization.mk_eq_mk'] at h ⊢
  obtain ⟨⟨u, t, rfl⟩, ht⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp h
  have htd : t ≤ D * t := by
    calc
      t = 1 * t := (one_mul t).symm
      _ ≤ D * t := Nat.mul_le_mul_right t hD
  have ha0 : b ^ t * a = 0 := by
    apply hf
    rw [map_zero, map_mul, map_pow, hfz, ← pow_mul]
    calc
      z ^ (D * t) * f a = z ^ (D * t - t) * (z ^ t * f a) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel htd]
      _ = 0 := by rw [ht, mul_zero]
  exact (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨_, t, rfl⟩, ha0⟩

variable {σ τ : Type*} [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]

theorem away_map_injective (f : G →+*ᵍ H) (hf : Function.Injective f)
    {b : A} (hb : b ∈ G 1) : Function.Injective (Away.map f b) := by
  apply (injective_iff_map_eq_zero (Away.map f b)).mpr
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective G hb z
  rw [Away.map_mk] at hz
  have hzv := congrArg HomogeneousLocalization.val hz
  simp only [Away.val_mk, val_zero, Localization.mk_eq_mk'] at hzv
  obtain ⟨⟨u, t, rfl⟩, ht⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hzv
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, val_zero, Localization.mk_eq_mk']
  apply (IsLocalization.mk'_eq_zero_iff _ _).mpr
  refine ⟨⟨b ^ t, t, rfl⟩, ?_⟩
  apply hf
  simpa only [map_mul, map_pow, map_zero] using ht

end PaperP1.GradedInjectiveChartMap
