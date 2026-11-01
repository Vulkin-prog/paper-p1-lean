module

public import PaperP1.Arithmetic.FixedSourceCertificate
public import PaperP1.Arithmetic.EvenSquareClasses

/-! # Source and target data of a finite physical coordinate class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PhysicalClassData

open Finset PaperP1.Arithmetic

variable {s L : ℕ}

def sources (C : Finset (Option (Fin s) × Fin (L + 1))) : Finset (Fin s × Fin (L + 1)) :=
  univ.filter fun v ↦ (some v.1, v.2) ∈ C

def targets (C : Finset (Option (Fin s) × Fin (L + 1))) : Finset (Fin (L + 1)) :=
  univ.filter fun u ↦ (none, u) ∈ C

def offsets (C : Finset (Option (Fin s) × Fin (L + 1))) : Finset ℤ :=
  (targets C).image fun u ↦ (u.val : ℤ) - 1

def sourceProduct (x : Fin s → ℕ) (C : Finset (Option (Fin s) × Fin (L + 1))) : ℕ :=
  ∏ v ∈ sources C, (x v.1 - 1 + v.2.val)

def targetProduct (z : ℕ) (C : Finset (Option (Fin s) × Fin (L + 1))) : ℕ :=
  ∏ u ∈ targets C, (z - 1 + u.val)

theorem source_image (C : Finset (Option (Fin s) × Fin (L + 1))) :
    (sources C).image (fun v ↦ (some v.1, v.2)) = C.filter (fun v ↦ v.1 ≠ none) := by
  ext v
  rcases v with ⟨_ | a, u⟩ <;> simp [sources]

theorem target_image (C : Finset (Option (Fin s) × Fin (L + 1))) :
    (targets C).image (fun u ↦ (none, u)) = C.filter (fun v ↦ v.1 = none) := by
  ext v
  rcases v with ⟨_ | a, u⟩ <;> simp [targets]

theorem sources_card (C : Finset (Option (Fin s) × Fin (L + 1))) : (sources C).card ≤ C.card := by
  have hinj : Function.Injective (fun v : Fin s × Fin (L + 1) ↦ (some v.1, v.2)) := by
    intro v w h
    simpa only [Prod.mk.injEq, Option.some.injEq, ← Prod.ext_iff] using h
  calc
    _ = ((sources C).image (fun v ↦ (some v.1, v.2))).card := (card_image_of_injective _ hinj).symm
    _ ≤ _ := by rw [source_image]; exact card_filter_le _ _

theorem targets_card (C : Finset (Option (Fin s) × Fin (L + 1))) : (targets C).card ≤ C.card := by
  calc
    _ = ((targets C).image (fun u ↦ (none, u))).card :=
      (card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj h).2)).symm
    _ ≤ _ := by rw [target_image]; exact card_filter_le _ _

theorem offset_injective : Function.Injective (fun u : Fin (L + 1) ↦ (u.val : ℤ) - 1) := by
  intro u v huv
  apply Fin.ext
  have hval : (u.val : ℤ) = v.val := sub_left_inj.mp huv
  exact_mod_cast hval

theorem offsets_card (C : Finset (Option (Fin s) × Fin (L + 1))) :
    (offsets C).card = (targets C).card := card_image_of_injective _ offset_injective

theorem offsets_nonempty (C : Finset (Option (Fin s) × Fin (L + 1))) :
    (offsets C).Nonempty ↔ (targets C).Nonempty := image_nonempty

theorem offset_bound (C : Finset (Option (Fin s) × Fin (L + 1)))
    {u : ℤ} (hu : u ∈ offsets C) : u.natAbs ≤ L + 1 := by
  obtain ⟨v, _, rfl⟩ := mem_image.mp hu
  have hv := v.isLt
  omega

theorem offsets_disjoint {C D : Finset (Option (Fin s) × Fin (L + 1))}
    (hCD : Disjoint C D) : Disjoint (offsets C) (offsets D) := by
  apply disjoint_left.mpr
  intro u huC huD
  obtain ⟨v, hv, hvu⟩ := mem_image.mp huC
  obtain ⟨w, hw, hwu⟩ := mem_image.mp huD
  have hvw := offset_injective (hvu.trans hwu.symm)
  have hvC : (none, v) ∈ C := (mem_filter.mp hv).2
  have hvD : (none, v) ∈ D := hvw ▸ (mem_filter.mp hw).2
  exact disjoint_left.mp hCD hvC hvD

theorem sourceProduct_pos (x : Fin s → ℕ) (hx : ∀ a, 2 ≤ x a)
    (C : Finset (Option (Fin s) × Fin (L + 1))) : 0 < sourceProduct x C := by
  apply prod_pos
  intro v _
  have h := hx v.1
  omega

theorem targetProduct_pos (z : ℕ) (hz : 2 ≤ z)
    (C : Finset (Option (Fin s) × Fin (L + 1))) : 0 < targetProduct z C := by
  apply prod_pos
  intro u _
  omega

theorem sourceProduct_le {N K : ℕ} (x : Fin s → ℕ) (hN : 3 ≤ N) (hL : L ≤ N)
    (hx : ∀ a, x a ∈ Ico N (2 * N))
    (C : Finset (Option (Fin s) × Fin (L + 1))) (hC : C.card ≤ K) :
    sourceProduct x C ≤ N ^ (2 * K) := by
  calc
    _ ≤ ∏ _v ∈ sources C, N ^ 2 := prod_le_prod fun v _ ↦
      FixedSourceCertificate.sourceValues_le_square x hN hL hx v
    _ = (N ^ 2) ^ (sources C).card := prod_const _
    _ ≤ (N ^ 2) ^ K := Nat.pow_le_pow_right (by have h := pow_pos (show 0 < N by omega) 2; omega)
      ((sources_card C).trans hC)
    _ = _ := (pow_mul N 2 K).symm

theorem targetProduct_cast (z : ℕ) (hz : 1 ≤ z)
    (C : Finset (Option (Fin s) × Fin (L + 1))) :
    (targetProduct z C : ℤ) = ∏ u ∈ offsets C, ((z : ℤ) + u) := by
  rw [offsets, prod_image (fun v _ w _ h ↦ offset_injective h)]
  simp only [targetProduct, Nat.cast_prod]
  apply prod_congr rfl
  intro u _
  omega

end PaperP1.PhysicalClassData
