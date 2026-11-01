module

public import PaperP1.Arithmetic.PrimePatternStates

/-! # Exposure states of actual split-product kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitKernelStates

open Finset PaperP1.EvenPrimePatterns PaperP1.PrimePatternStates PaperP1.SplitOffsetProducts
open PaperP1.PrescribedPatternDivisors PaperP1.ExposureAssignmentBudget

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def kernels (A : Finset ℤ) (n : ι → ℕ) : ι → ℕ := fun i ↦ kernel A (n i)

def state (A : Finset ℤ) (rank : ι → ℕ) (k : ℕ) (n : ι → ℕ) : State ι :=
  PaperP1.PrimePatternStates.state rank k n (part (kernels A n))

def stepRecord (A : Finset ℤ) (rank : ι → ℕ) (i : ι) (n : ι → ℕ) :
    ℕ × (freshPatterns rank i → ℕ) :=
  PaperP1.PrimePatternStates.stepRecord rank i n (part (kernels A n))

omit [Fintype ι] [DecidableEq ι] in
theorem kernels_squarefree (A : Finset ℤ) (n : ι → ℕ) : ∀ i, Squarefree (kernels A n i) :=
  fun i ↦ kernel_squarefree A (n i)

theorem prescribed_eq (A : Finset ℤ) (rank : ι → ℕ) (k : ℕ) (i : ι)
    (hki : rank i = k) (n m : ι → ℕ) (hstate : state A rank k n = state A rank k m) :
    prescribed (kernels A n) rank i = prescribed (kernels A m) rank i :=
  prescribed_eq_of_state_eq (kernels A n) (kernels A m) rank k i hki n m hstate

theorem fresh_product (A : Finset ℤ) (rank : ι → ℕ) (i : ι) (n : ι → ℕ)
    (hsq : IsSquare (∏ j, kernels A n j)) :
    (∏ S : freshPatterns rank i, (stepRecord A rank i n).2 S) =
      kernels A n i / prescribed (kernels A n) rank i := by
  have hprod : (∏ S : freshPatterns rank i, (stepRecord A rank i n).2 S) = newPart (kernels A n) rank i := by
    exact prod_coe_sort (freshPatterns rank i) (part (kernels A n))
  rw [hprod, newPart_eq_quotient _ (kernels_squarefree A n) hsq rank i]

theorem fresh_coprime (A : Finset ℤ) (rank : ι → ℕ) (i : ι) (n : ι → ℕ) :
    Pairwise fun S T : freshPatterns rank i ↦
      Nat.Coprime ((stepRecord A rank i n).2 S) ((stepRecord A rank i n).2 T) := by
  intro S T hST
  exact part_coprime (kernels A n) S.val T.val (fun hval ↦ hST (Subtype.ext hval))

theorem advance_determined (A : Finset ℤ) (rank : ι → ℕ) (hrank : Function.Injective rank)
    (k : ℕ) (i : ι) (hki : rank i = k) (n m : ι → ℕ)
    (hsqN : IsSquare (∏ j, kernels A n j)) (hsqM : IsSquare (∏ j, kernels A m j))
    (hstate : state A rank k n = state A rank k m)
    (hrecord : stepRecord A rank i n = stepRecord A rank i m) :
    state A rank (k + 1) n = state A rank (k + 1) m := by
  exact PaperP1.PrimePatternStates.advance_determined rank hrank k i hki n m _ _
    (part_eq_one_outside_patterns _ (kernels_squarefree A n) hsqN)
    (part_eq_one_outside_patterns _ (kernels_squarefree A m) hsqM) hstate hrecord

theorem fresh_last_empty (rank : ι → ℕ) (hrank : Function.Injective rank)
    (last : ι) (hlast : ∀ i, rank i ≤ rank last) : freshPatterns rank last = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨S, hS⟩
  obtain ⟨hSp, hnot⟩ := mem_filter.mp hS
  obtain ⟨hpat, hlastS⟩ := mem_filter.mp hSp
  have htwo := (mem_filter.mp hpat).2.1
  have hne := PaperP1.OrderedExposure.firstByRank_ne_last rank hrank last hlast S htwo
  exact hnot ((PaperP1.OrderedExposure.earlier_iff_ne_first rank hrank last S last hlastS).mpr hne)

theorem advance_last_determined (A : Finset ℤ) (rank : ι → ℕ) (hrank : Function.Injective rank)
    (k : ℕ) (last : ι) (hki : rank last = k) (hlast : ∀ i, rank i ≤ rank last) (n m : ι → ℕ)
    (hsqN : IsSquare (∏ j, kernels A n j)) (hsqM : IsSquare (∏ j, kernels A m j))
    (hstate : state A rank k n = state A rank k m) (hcentre : n last = m last) :
    state A rank (k + 1) n = state A rank (k + 1) m := by
  apply advance_determined A rank hrank k last hki n m hsqN hsqM hstate
  apply Prod.ext hcentre
  funext S
  have hnon : (freshPatterns rank last).Nonempty := ⟨S.val, S.property⟩
  rw [fresh_last_empty rank hrank last hlast] at hnon
  exact False.elim (not_nonempty_empty hnon)

theorem last_kernel_eq (A : Finset ℤ) (rank : ι → ℕ) (hrank : Function.Injective rank)
    (k : ℕ) (last : ι) (hki : rank last = k) (hlast : ∀ i, rank i ≤ rank last) (n m : ι → ℕ)
    (hsqN : IsSquare (∏ j, kernels A n j)) (hsqM : IsSquare (∏ j, kernels A m j))
    (hstate : state A rank k n = state A rank k m) : kernels A n last = kernels A m last := by
  have he := prescribed_eq A rank k last hki n m hstate
  rw [last_kernel_fixed _ (kernels_squarefree A n) hsqN rank hrank last hlast,
    last_kernel_fixed _ (kernels_squarefree A m) hsqM rank hrank last hlast] at he
  exact he

end PaperP1.SplitKernelStates
