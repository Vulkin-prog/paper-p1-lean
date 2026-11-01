module

public import PaperP1.Arithmetic.FiniteResidualRank
public import PaperP1.Arithmetic.TwoProgressionPrimeRows
public import PaperP1.Coding.LocalDefectWindowScale

/-! # A large-prime value kernel is supported on actual defective interval values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntervalResidualKernel

open Finset PaperP1.Arithmetic PaperP1.PrimeRowComponents PaperP1.DefectCounting
  PaperP1.DefectivePredicate PaperP1.FiniteResidualRank

local instance intervalResidualPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance intervalResidualDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def largeKernel (S : Finset ℕ) (H : ℕ) : Submodule F₂ (S → F₂) :=
  CoverGraphResolution.rowSolutions (rows S (smallPrimesUpTo H))

def selectedDefects (S : Finset ℕ) (H : ℕ) : Finset ℕ := S.filter (HDefective H)

theorem mem_largeKernel_iff (S : Finset ℕ) (H : ℕ) (w : S → F₂) :
    w ∈ largeKernel S H ↔ ∀ p : ℕ, p.Prime → H < p → ∑ n : S, w n * parityVec n.val p = 0 := by
  constructor
  · intro hw p hp hHp
    have hpP : p ∉ smallPrimesUpTo H := fun h ↦ (not_le_of_gt hHp) (mem_smallPrimesUpTo.mp h).2
    have hrow := hw p
    rwa [sum_row p hpP] at hrow
  · intro hw p
    by_cases hpP : p ∈ smallPrimesUpTo H
    · simp only [rows, ite_eq_left hpP, sum_empty]
    · rw [sum_row p hpP]
      by_cases hp : p.Prime
      · exact hw p hp (by by_contra h; exact hpP (mem_smallPrimesUpTo.mpr ⟨hp, by omega⟩))
      · simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_prime _ hp, Nat.cast_zero,
          mul_zero, sum_const_zero]

theorem coefficient_zero {S : Finset ℕ} {H U R : ℕ} (hR : R ≤ H)
    (hS : S ⊆ Icc U (U + R)) (w : S → F₂) (hw : w ∈ largeKernel S H)
    (n : S) (hn : ¬HDefective H n.val) : w n = 0 := by
  simp only [HDefective, not_forall] at hn
  obtain ⟨p, hp, hHp, hnpar⟩ := hn
  have hcoord := (mem_largeKernel_iff S H w).mp hw p hp hHp
  have hsum : (∑ m : S, w m * parityVec m.val p) = w n * parityVec n.val p := by
    apply sum_eq_single n
    · intro m _ hmn
      have hmzero : parityVec m.val p = 0 := by
        by_contra hmpar
        have heq := TwoProgressionPrimeRows.unique_interval_multiples (hS n.property) (hS m.property)
          (TwoProgressionPrimeRows.dvd_of_nonzero_parity hnpar)
          (TwoProgressionPrimeRows.dvd_of_nonzero_parity hmpar) (hR.trans_lt hHp)
        exact hmn (Subtype.ext heq.symm)
      rw [hmzero, mul_zero]
    · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  rw [hsum] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_right hnpar

def restriction (S : Finset ℕ) (H : ℕ) : largeKernel S H →ₗ[F₂] (selectedDefects S H → F₂) where
  toFun w n := w.val ⟨n.val, (mem_filter.mp n.property).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restriction_injective {S : Finset ℕ} {H U R : ℕ} (hR : R ≤ H) (hS : S ⊆ Icc U (U + R)) :
    Function.Injective (restriction S H) := by
  intro w z hwz
  apply Subtype.ext
  funext n
  by_cases hn : n.val ∈ selectedDefects S H
  · have h := congrFun hwz ⟨n.val, hn⟩
    change w.val n = z.val n at h
    exact h
  · have hnd : ¬HDefective H n.val := fun h ↦ hn (mem_filter.mpr ⟨n.property, h⟩)
    rw [coefficient_zero hR hS w.val w.property n hnd, coefficient_zero hR hS z.val z.property n hnd]

theorem rank_le_selected_defects {S : Finset ℕ} {H U R : ℕ} (hR : R ≤ H) (hS : S ⊆ Icc U (U + R)) :
    Module.finrank F₂ (largeKernel S H) ≤ (selectedDefects S H).card := by
  have h := LinearMap.finrank_le_finrank_of_injective (restriction_injective hR hS)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  exact h

theorem rank_le_interval_defects {S : Finset ℕ} {H U R : ℕ} (hR : R ≤ H) (hS : S ⊆ Icc U (U + R)) :
    Module.finrank F₂ (largeKernel S H) ≤ (LocalDefectBound.defectsInInterval H U R).card := by
  apply (rank_le_selected_defects hR hS).trans
  apply card_le_card
  intro n hn
  obtain ⟨hnS, hnd⟩ := mem_filter.mp hn
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp (hS hnS)
  exact LocalDefectBound.mem_defectsInInterval.mpr ⟨hlo, hhi, hnd⟩

theorem fullKernel_le_large (S : Finset ℕ) (H : ℕ) : valueKernel S ≤ largeKernel S H := by
  intro w hw
  apply (mem_largeKernel_iff S H w).mpr
  intro p _ _
  have hcoord := congrArg (fun z : ℕ →₀ F₂ ↦ z p) (LinearMap.mem_ker.mp hw)
  rw [EvenImage.combination_apply] at hcoord
  change (∑ n : S, w n • parityVec n.val) p = 0 at hcoord
  simpa only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] using hcoord

end PaperP1.IntervalResidualKernel
