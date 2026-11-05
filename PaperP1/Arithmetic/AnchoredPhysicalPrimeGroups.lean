module

public import PaperP1.Arithmetic.PrimeGroupIncidence
public import PaperP1.Coding.CoordinateErasureRank
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Arbitrary fixed arity through prime supports anchored in one window

A prime chooses one minimal support through its unique active anchor position.
Only anchor positions of large groups are erased. No property of whole prime
rows, or recovery property after erasure, is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredPhysicalPrimeGroups

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.WindowPrimeIncidence PaperP1.PrimeCircuitSupports PaperP1.PrimeCircuitGroups
  PaperP1.PhysicalLabelSupportCount PaperP1.LargeOddKernel

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((Option (Fin s) × Fin (L + 1)) → F₂)) (code X L)
local instance physicalAddCommGroup {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ)
    (M : Submodule F₂ (code X L)) : AddCommGroup M := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) M

variable {s L H : ℕ}

def largeGroups (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (H : ℕ) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (Y : ℝ) :=
  (groups X M H hX hH).filter fun F ↦ Y < (groupValue X M H hX hH F : ℝ)

def badPositions (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (H : ℕ) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (Y : ℝ) :=
  (largeGroups X M H hX hH Y).biUnion fun F ↦ F.filter fun v ↦ v.1 = none

abbrev remaining (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (H : ℕ) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (Y : ℝ) :=
  CoordinateForms.zeroCoordinates (U := M) (label X L M) (badPositions X M H hX hH Y)

theorem throughPool_card_of_noRecovery (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (t : ℕ) (hs : 1 ≤ s) (ht : 2 ≤ t)
    (hno : DisjointRecoverySubspace.NoDisjointRecovery
      (CoordinateForms.coordinateFamily (code X L)) M s t)
    (v : Option (Fin s) × Fin (L + 1)) (hv : label X L M v ≠ 0) :
    (throughPool X L M v).card ≤ supportBound s t (t - 1) := by
  classical
  have hlabels := RecoveryLabelSupports.noDisjointSums_of_recovery_exclusion
    (CoordinateForms.coordinateFamily (code X L)) M s t (by omega) hno
  apply card_image_le.trans
  apply supportPool_card _ _ s t (t - 1) hlabels
  · intro a ha
    exact DisjointRecoverySubspace.coordinate_multiplicity_le
      (CoordinateForms.coordinateFamily (code X L)) M s t hs hno a
      ((RecoveryLabelSupports.mem_labels _ M a).mp ha).1
  · exact hv

theorem group_active (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    {F : Finset (Option (Fin s) × Fin (L + 1))} (hF : F ∈ groups X M H hX hH) :
    ∀ w ∈ F, label X L M w ≠ 0 := by
  classical
  obtain ⟨u, _hu, hactive, hpool, _hunique, _hother⟩ := group_target_source X M hX hH hF
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hpool
  intro w hw
  rcases mem_insert.mp hw with rfl | hw
  · exact hactive
  · obtain ⟨j, _hj, hDj⟩ := mem_biUnion.mp hD
    have hrep := (mem_filter.mp hDj).2
    have hl := (ZeroSumFreeRepresentations.mem_representations.mp hrep).1 (mem_image.mpr ⟨w, hw, rfl⟩)
    exact ((RecoveryLabelSupports.mem_labels _ M _).mp hl).1

theorem target_positions_singleton (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    {F : Finset (Option (Fin s) × Fin (L + 1))} (hF : F ∈ groups X M H hX hH) :
    ∃ u : Fin (L + 1), (F.filter fun v ↦ v.1 = none) = {(none, u)} := by
  classical
  obtain ⟨u, hu, _hactive, _hpool, hunique, _hother⟩ := group_target_source X M hX hH hF
  refine ⟨u, ?_⟩
  ext w
  constructor
  · intro hw
    exact mem_singleton.mpr (hunique w (mem_filter.mp hw).1 (mem_filter.mp hw).2)
  · intro hw
    rw [mem_singleton.mp hw]
    exact mem_filter.mpr ⟨hu, rfl⟩

theorem badPositions_card (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (Y : ℝ) :
    (badPositions X M H hX hH Y).card ≤ (largeGroups X M H hX hH Y).card := by
  classical
  calc
    _ ≤ ∑ F ∈ largeGroups X M H hX hH Y, (F.filter fun v ↦ v.1 = none).card := card_biUnion_le
    _ = _ := by
      have heq : ∀ F ∈ largeGroups X M H hX hH Y, (F.filter fun v ↦ v.1 = none).card = 1 := by
        intro F hF
        obtain ⟨u, hu⟩ := target_positions_singleton X M hX hH (mem_filter.mp hF).1
        rw [hu, card_singleton]
      simp only [sum_congr rfl heq, sum_const, smul_eq_mul, mul_one]

theorem incidence_bound (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (t : ℕ) (hs : 1 ≤ s) (ht : 2 ≤ t)
    (hno : DisjointRecoverySubspace.NoDisjointRecovery
      (CoordinateForms.coordinateFamily (code X L)) M s t)
    (u : Fin (L + 1)) (hu : label X L M (none, u) ≠ 0) :
    ((groups X M H hX hH).filter fun F ↦ (none, u) ∈ F).card ≤ supportBound s t (t - 1) := by
  classical
  apply (card_le_card (show (groups X M H hX hH).filter (fun F ↦ (none, u) ∈ F) ⊆
      throughPool X L M (none, u) from ?_)).trans
    (throughPool_card_of_noRecovery X M t hs ht hno (none, u) hu)
  intro F hF
  obtain ⟨v, _hv, _hactive, hpool, hunique, _hother⟩ := group_target_source X M hX hH (mem_filter.mp hF).1
  have he : u = v := congrArg Prod.snd (hunique (none, u) (mem_filter.mp hF).2 rfl)
  simpa only [he] using hpool

theorem kernel_le_incident_product (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (u : Fin (L + 1)) (hu : label X L M (none, u) ≠ 0) :
    largeOddKernel H (value X L (none, u)) ≤
      ∏ F ∈ (groups X M H hX hH).filter (fun F ↦ (none, u) ∈ F), groupValue X M H hX hH F := by
  classical
  let Q := (DefectivePredicate.oddPrimeSupport (value X L (none, u))).filter fun p ↦ H < p
  have hocc (p : ℕ) (hp : p ∈ Q) : (none, u) ∈ occurrences X L p := by
    have hn := mem_oddPrimeSupport_iff_parityVec_ne_zero.mp (mem_filter.mp hp).1
    apply (mem_occurrences X L p (none, u)).mpr
    rcases binary_eq_zero_or_one (parityVec (value X L (none, u)) p) with hz | ho
    · exact False.elim (hn hz)
    · exact ho
  have hQP : Q ⊆ activePrimes X L M H := by
    intro p hp
    exact (mem_activePrimes X L M H p).mpr ⟨(mem_filter.mp hp).2, u, hocc p hp, hu⟩
  change Q.prod id ≤ _
  apply AssignedPrimeGroups.covered_prime_product_le _ (fun _ hp ↦ active_prime hp)
    (support X M H hX hH) Q _ hQP
  intro p hp
  obtain ⟨v, hv, _hactive, _hpool, _hunique, _hother⟩ := group_target_source X M hX hH
    (show support X M H hX hH p ∈ groups X M H hX hH from mem_image.mpr ⟨p, hQP hp, rfl⟩)
  have hvalid := support_valid X M hX hH (hQP hp)
  obtain ⟨w, _hw, _hwtarget, _hwactive, _hwpool, hallocc, _⟩ := hvalid
  have he : (none, v) = (none, u) := block_injective X L p hX
    (hH.trans_lt (mem_filter.mp hp).2) (hallocc (none, v) hv) (hocc p hp) rfl
  exact mem_filter.mpr ⟨mem_image.mpr ⟨p, hQP hp, rfl⟩, he ▸ hv⟩

theorem kernel_cap_away_from_bad (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (t : ℕ) (hs : 1 ≤ s) (ht : 2 ≤ t)
    (hno : DisjointRecoverySubspace.NoDisjointRecovery
      (CoordinateForms.coordinateFamily (code X L)) M s t)
    (Y : ℝ) (hY : 1 ≤ Y) (u : Fin (L + 1)) (hu : label X L M (none, u) ≠ 0)
    (hbad : (none, u) ∉ badPositions X M H hX hH Y) :
    (largeOddKernel H (value X L (none, u)) : ℝ) ≤ Y ^ supportBound s t (t - 1) := by
  classical
  let I := (groups X M H hX hH).filter fun F ↦ (none, u) ∈ F
  have hcap (F : Finset (Option (Fin s) × Fin (L + 1))) (hF : F ∈ I) :
      (groupValue X M H hX hH F : ℝ) ≤ Y := by
    by_contra hh
    apply hbad
    exact mem_biUnion.mpr ⟨F, mem_filter.mpr ⟨(mem_filter.mp hF).1, lt_of_not_ge hh⟩,
      mem_filter.mpr ⟨(mem_filter.mp hF).2, rfl⟩⟩
  calc
    _ ≤ (((∏ F ∈ I, groupValue X M H hX hH F) : ℕ) : ℝ) := by
      exact_mod_cast kernel_le_incident_product X M hX hH u hu
    _ = ∏ F ∈ I, (groupValue X M H hX hH F : ℝ) := by rw [Nat.cast_prod]
    _ ≤ ∏ _F ∈ I, Y := prod_le_prod₀ (fun _ _ ↦ Nat.cast_nonneg _) hcap
    _ = Y ^ I.card := by rw [prod_const]
    _ ≤ _ := pow_le_pow_right₀ hY (incidence_bound X M hX hH t hs ht hno u hu)

theorem dimension_cost (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (Y : ℝ) :
    Module.finrank F₂ M ≤ (largeGroups X M H hX hH Y).card +
      Module.finrank F₂ (remaining X M H hX hH Y) := by
  have hd := CoordinateErasureRank.dimension_cost (U := M) (label X L M)
    (badPositions X M H hX hH Y)
  have hc := badPositions_card X M hX hH Y
  change Module.finrank F₂ M ≤ (badPositions X M H hX hH Y).card +
    Module.finrank F₂ (remaining X M H hX hH Y) at hd
  omega

theorem two_small (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (t : ℕ) (hs : 1 ≤ s) (ht : 2 ≤ t)
    (hno : DisjointRecoverySubspace.NoDisjointRecovery
      (CoordinateForms.coordinateFamily (code X L)) M s t)
    (hinj : Function.Injective ((projection X L none).comp M.subtype))
    (Y : ℝ) (hY : 1 ≤ Y)
    (hlarge : (largeGroups X M H hX hH Y).card < Module.finrank F₂ M) :
    ∃ a b : Fin (L + 1), a ≠ b ∧
      (largeOddKernel H (value X L (none, a)) : ℝ) ≤ Y ^ supportBound s t (t - 1) ∧
      (largeOddKernel H (value X L (none, b)) : ℝ) ≤ Y ^ supportBound s t (t - 1) := by
  classical
  let R := remaining X M H hX hH Y
  have hdim : 0 < Module.finrank F₂ R := by
    have hh := dimension_cost X M hX hH Y
    change Module.finrank F₂ M ≤ (largeGroups X M H hX hH Y).card + Module.finrank F₂ R at hh
    omega
  let f := ((projection X L none).comp M.subtype).comp R.subtype
  have hfinj : Function.Injective f := hinj.comp Subtype.val_injective
  have heven (u : R) : (∑ j, f u j) = 0 := by
    change (∑ j, u.val.val.val (none, j)) = 0
    simpa only [startVertexSum_apply] using u.val.val.property.1 none
  obtain ⟨a, b, hab, ha, hb⟩ := CoordinateErasureRank.two_active (U := R) f hfinj heven hdim
  have hcap (j : Fin (L + 1)) (hj : (LinearMap.proj j).comp f ≠ 0) :
      (largeOddKernel H (value X L (none, j)) : ℝ) ≤ Y ^ supportBound s t (t - 1) := by
    have hj' : (label X L M (none, j)).comp R.subtype ≠ 0 := hj
    obtain ⟨hactive, hnotbad⟩ := CoordinateErasureRank.surviving_active (U := M)
      (label X L M) (badPositions X M H hX hH Y) (none, j) hj'
    exact kernel_cap_away_from_bad X M hX hH t hs ht hno Y hY j hactive hnotbad
  exact ⟨a, b, hab, hcap a ha, hcap b hb⟩

end PaperP1.AnchoredPhysicalPrimeGroups
