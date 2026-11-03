/-
Copyright (c) 2025-2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

The quotient-respect argument is adapted from
Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean,
Mathlib commit 9d581dfff2e41de989072ea63abf3daf69311520.
The map here multiplies homogeneous degrees by D; the original
Mathlib same-degree map and dependency remain unchanged.
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! # Homogeneous localization maps for ring maps multiplying all degrees by D -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DegreeScalingHomogeneousMap

open HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (D : ℕ) (f : G →+*ᵍ (fun n ↦ H (n * D)))
  {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f.toRingHom)

def fraction (c : NumDenSameDeg G P) : NumDenSameDeg H Q where
  deg := c.deg * D
  num := ⟨f c.num, f.map_mem c.num.property⟩
  den := ⟨f c.den, f.map_mem c.den.property⟩
  den_mem := hPQ c.den_mem

def mapFun : HomogeneousLocalization G P → HomogeneousLocalization H Q :=
  Quotient.map' (fraction D f hPQ) (fun x y (e : x.embedding = y.embedding) ↦ by
    change (fraction D f hPQ x).embedding = (fraction D f hPQ y).embedding
    apply_fun IsLocalization.map (Localization Q) f.toRingHom hPQ at e
    simpa only [fraction, NumDenSameDeg.embedding, Localization.mk_eq_mk',
      IsLocalization.map_mk', GradedRingHom.toRingHom_eq_toRingHom, GradedRingHom.coe_toRingHom] using e)

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing G] [GradedRing H] in
theorem mapFun_val (z : HomogeneousLocalization G P) :
    (mapFun D f hPQ z).val = IsLocalization.map (Localization Q) f.toRingHom hPQ z.val := by
  obtain ⟨c, rfl⟩ := z.mk_surjective
  change (fraction D f hPQ c).embedding =
    IsLocalization.map (Localization Q) f.toRingHom hPQ c.embedding
  simp only [fraction, NumDenSameDeg.embedding, Localization.mk_eq_mk', IsLocalization.map_mk',
    GradedRingHom.coe_toRingHom]

def map : HomogeneousLocalization G P →+* HomogeneousLocalization H Q where
  toFun := mapFun D f hPQ
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [mapFun_val, val_zero, map_zero]
  map_one' := by
    apply HomogeneousLocalization.val_injective
    simp only [mapFun_val, val_one, map_one]
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    simp only [mapFun_val, val_add, map_add]
  map_mul' x y := by
    apply HomogeneousLocalization.val_injective
    simp only [mapFun_val, val_mul, map_mul]

theorem map_mk (c : NumDenSameDeg G P) : map D f hPQ (HomogeneousLocalization.mk c) =
    HomogeneousLocalization.mk (fraction D f hPQ c) := rfl

theorem map_val (z : HomogeneousLocalization G P) :
    (map D f hPQ z).val = IsLocalization.map (Localization Q) f.toRingHom hPQ z.val :=
  mapFun_val D f hPQ z

variable (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f.toRingHom)

def localRingHom : AtPrime G I →+* AtPrime H J :=
  map D f (Localization.le_comap_primeCompl_iff.mpr (hIJ ▸ le_rfl))

theorem val_localRingHom (z : AtPrime G I) :
    (localRingHom D f I J hIJ z).val = Localization.localRingHom I J f.toRingHom hIJ z.val :=
  map_val D f _ z

instance : IsLocalHom (localRingHom D f I J hIJ) where
  map_nonunit z hz := by
    rw [← isUnit_iff_isUnit_val] at hz ⊢
    rw [val_localRingHom] at hz
    exact IsLocalHom.map_nonunit _ hz

end PaperP1.DegreeScalingHomogeneousMap
