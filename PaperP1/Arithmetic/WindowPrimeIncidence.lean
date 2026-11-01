module

public import PaperP1.Arithmetic.PhysicalWindowRelations
public import PaperP1.Affine.TwoWindowLabels
public import PaperP1.Coding.CoordinateRegularisation
public import PaperP1.Affine.PairFourierIntersection
public import PaperP1.Arithmetic.LargeOddKernel

/-! # Actual prime incidences in every physical window and their dual row equations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WindowPrimeIncidence

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations

local instance windowPrimeIncidenceTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {ι : Type*} [Fintype ι]

def value (X : ι → ℕ) (L : ℕ) (v : ι × Fin (L + 1)) : ℕ :=
  startCompleteVertexLabel (X v.1) L v.2

def occurrences (X : ι → ℕ) (L p : ℕ) : Finset (ι × Fin (L + 1)) :=
  univ.filter fun v ↦ parityVec (value X L v) p = 1

theorem mem_occurrences (X : ι → ℕ) (L p : ℕ) (v : ι × Fin (L + 1)) :
    v ∈ occurrences X L p ↔ parityVec (value X L v) p = 1 := by
  simp only [occurrences, mem_filter, mem_univ, true_and]

theorem value_ne_zero_of_mem {X : ι → ℕ} {L p : ℕ} {v : ι × Fin (L + 1)}
    (hv : v ∈ occurrences X L p) : value X L v ≠ 0 := by
  intro hz
  have h := (mem_occurrences X L p v).mp hv
  simp [parityVec, hz] at h

theorem prime_of_mem {X : ι → ℕ} {L p : ℕ} {v : ι × Fin (L + 1)}
    (hv : v ∈ occurrences X L p) : Nat.Prime p := by
  apply LargeOddKernel.prime_of_mem_oddPrimeSupport
  apply LargeOddKernel.mem_oddPrimeSupport_iff_parityVec_ne_zero.mpr
  rw [(mem_occurrences X L p v).mp hv]
  exact one_ne_zero

theorem dvd_of_mem {X : ι → ℕ} {L p : ℕ} {v : ι × Fin (L + 1)}
    (hv : v ∈ occurrences X L p) : p ∣ value X L v := by
  by_contra hnot
  have h := (mem_occurrences X L p v).mp hv
  simp [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hnot] at h

theorem block_injective (X : ι → ℕ) (L p : ℕ) (hX : ∀ i, 1 ≤ X i) (hp : L + 1 < p) :
    Set.InjOn Prod.fst (occurrences X L p : Set (ι × Fin (L + 1))) := by
  rintro ⟨i, v⟩ hv ⟨j, w⟩ hw hij
  change i = j at hij
  subst j
  apply Prod.ext
  · rfl
  · apply parityVec_ne_zero_unique_in_start (hX i) hp
    · change parityVec (value X L (i, v)) p ≠ 0
      rw [(mem_occurrences X L p (i, v)).mp hv]
      exact one_ne_zero
    · change parityVec (value X L (i, w)) p ≠ 0
      rw [(mem_occurrences X L p (i, w)).mp hw]
      exact one_ne_zero

variable [DecidableEq ι]

theorem occurrences_card (X : ι → ℕ) (L p : ℕ) (hX : ∀ i, 1 ≤ X i) (hp : L + 1 < p) :
    (occurrences X L p).card ≤ Fintype.card ι := by
  calc
    _ = ((occurrences X L p).image Prod.fst).card :=
      (card_image_of_injOn (block_injective X L p hX hp)).symm
    _ ≤ _ := card_le_univ _

theorem other_block {X : ι → ℕ} {L p : ℕ} (hX : ∀ i, 1 ≤ X i) (hp : L + 1 < p)
    {v w : ι × Fin (L + 1)} (hv : v ∈ occurrences X L p)
    (hw : w ∈ (occurrences X L p).erase v) : w.1 ≠ v.1 := by
  intro hblock
  exact (mem_erase.mp hw).1 (block_injective X L p hX hp (mem_erase.mp hw).2 hv hblock)

theorem others_card {X : ι → ℕ} {L p : ℕ} (hX : ∀ i, 1 ≤ X i) (hp : L + 1 < p)
    {v : ι × Fin (L + 1)} (hv : v ∈ occurrences X L p) :
    ((occurrences X L p).erase v).card ≤ Fintype.card ι - 1 := by
  rw [card_erase_of_mem hv]
  exact Nat.sub_le_sub_right (occurrences_card X L p hX hp) 1

omit [DecidableEq ι] in
theorem physical_row_sum (X : ι → ℕ) (L p : ℕ) (w : code X L) :
    (∑ v ∈ occurrences X L p, w.val v) = 0 := by
  have h := congrArg (fun a : ℕ →₀ F₂ ↦ a p) w.property.2
  simp only [vertexParityMap_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.zero_apply] at h
  have hfull : (∑ v : ι × Fin (L + 1), w.val v * parityVec (value X L v) p) = 0 := by
    simpa only [Fintype.sum_prod_type, value] using h
  calc
    _ = ∑ v : ι × Fin (L + 1), if parityVec (value X L v) p = 1 then w.val v else 0 := by
      rw [occurrences, sum_filter]
    _ = ∑ v : ι × Fin (L + 1), w.val v * parityVec (value X L v) p := by
      apply sum_congr rfl
      intro v _
      rcases binary_eq_zero_or_one (parityVec (value X L v) p) with hz | ho
      · simp [hz]
      · simp [ho]
    _ = 0 := hfull

omit [DecidableEq ι] in
theorem restricted_row_sum (X : ι → ℕ) (L p : ℕ) (M : Submodule F₂ (code X L)) :
    (∑ v ∈ occurrences X L p, (CoordinateForms.coordinateFamily (code X L) v).comp M.subtype) = 0 := by
  ext w
  simp only [LinearMap.sum_apply]
  exact physical_row_sum X L p w.val

theorem others_label_sum {X : ι → ℕ} {L p : ℕ} (M : Submodule F₂ (code X L))
    {v : ι × Fin (L + 1)} (hv : v ∈ occurrences X L p) :
    (∑ w ∈ (occurrences X L p).erase v,
      (CoordinateForms.coordinateFamily (code X L) w).comp M.subtype) =
        (CoordinateForms.coordinateFamily (code X L) v).comp M.subtype := by
  apply (PaperP1.PairFourierIntersection.add_zero_iff _ _).mp
  exact (sum_erase_add (occurrences X L p)
    (fun w ↦ (CoordinateForms.coordinateFamily (code X L) w).comp M.subtype) hv).trans
      (restricted_row_sum X L p M)

end PaperP1.WindowPrimeIncidence
