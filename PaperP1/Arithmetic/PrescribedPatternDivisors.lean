module

public import PaperP1.Arithmetic.KernelExposureWeights

/-! # Actual prescribed divisors formed by previously exposed prime patterns -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrescribedPatternDivisors

open Finset PaperP1.EvenPrimePatterns PaperP1.KernelExposureWeights
open PaperP1.ExposureWeights PaperP1.ExposureOrder PaperP1.OrderedExposure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def knownPatterns (rank : ι → ℕ) (i : ι) : Finset (Finset ι) :=
  patterns.filter fun S ↦ i ∈ S ∧ ∃ j ∈ S, rank j < rank i

def prescribed (q : ι → ℕ) (rank : ι → ℕ) (i : ι) : ℕ :=
  ∏ S ∈ knownPatterns rank i, part q S

def newPart (q : ι → ℕ) (rank : ι → ℕ) (i : ι) : ℕ :=
  ∏ S ∈ (patterns.filter fun S ↦ i ∈ S).filter
    (fun S ↦ ¬ ∃ j ∈ S, rank j < rank i), part q S

theorem prescribed_pos (q : ι → ℕ) (rank : ι → ℕ) (i : ι) : 0 < prescribed q rank i :=
  prod_pos fun S _ ↦ part_pos q S

theorem newPart_pos (q : ι → ℕ) (rank : ι → ℕ) (i : ι) : 0 < newPart q rank i :=
  prod_pos fun S _ ↦ part_pos q S

theorem coordinate_split (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (rank : ι → ℕ) (i : ι) :
    prescribed q rank i * newPart q rank i = q i := by
  have hfilter : ((patterns.filter fun S : Finset ι ↦ i ∈ S).filter
      (fun S ↦ ∃ j ∈ S, rank j < rank i)) = knownPatterns rank i := by
    ext S
    simp [knownPatterns, and_assoc]
  have hsplit := prod_filter_mul_prod_filter_not
    (patterns.filter fun S : Finset ι ↦ i ∈ S)
    (fun S ↦ ∃ j ∈ S, rank j < rank i) (part q)
  rw [hfilter, even_reconstruction q hq hsq i] at hsplit
  exact hsplit

theorem prescribed_dvd_coordinate (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (rank : ι → ℕ) (i : ι) :
    prescribed q rank i ∣ q i := ⟨newPart q rank i, (coordinate_split q hq hsq rank i).symm⟩

theorem prescribed_squarefree (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (rank : ι → ℕ) (i : ι) :
    Squarefree (prescribed q rank i) :=
  (hq i).squarefree_of_dvd (prescribed_dvd_coordinate q hq hsq rank i)

theorem logarithmic_prescribed (q : ι → ℕ) (rank : ι → ℕ) (hrank : Function.Injective rank)
    (fallback : ι) (N : ℕ) (i : ι) :
    Real.log (prescribed q rank i) / Real.log N =
      prescribedWeight patterns (weight q N) (firstByRank rank fallback) i := by
  have hne : ∀ S ∈ (patterns : Finset (Finset ι)), S.Nonempty := by
    intro S hS
    apply card_pos.mp
    have htwo := (mem_filter.mp hS).2.1
    omega
  rw [prescribedWeight_earlier patterns (weight q N) rank hrank fallback hne]
  unfold prescribed
  rw [Nat.cast_prod, Real.log_prod]
  · unfold weight knownPatterns
    exact sum_div _ _ _
  · intro S _
    exact_mod_cast (part_pos q S).ne'

theorem last_kernel_fixed (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (rank : ι → ℕ) (hrank : Function.Injective rank)
    (last : ι) (hlast : ∀ i, rank i ≤ rank last) : prescribed q rank last = q last := by
  have heq : knownPatterns rank last = patterns.filter (fun S ↦ last ∈ S) := by
    ext S
    simp only [knownPatterns, mem_filter]
    constructor
    · rintro ⟨hS, hi, _⟩
      exact ⟨hS, hi⟩
    · rintro ⟨hS, hi⟩
      have htwo := (mem_filter.mp hS).2.1
      have hne := firstByRank_ne_last rank hrank last hlast S htwo
      have hearlier := (earlier_iff_ne_first rank hrank last S last hi).mpr hne
      exact ⟨hS, hi, hearlier⟩
  unfold prescribed
  rw [heq, even_reconstruction q hq hsq last]

end PaperP1.PrescribedPatternDivisors
