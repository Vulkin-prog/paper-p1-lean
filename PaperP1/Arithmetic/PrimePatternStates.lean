module

public import PaperP1.Asymptotics.ExposureAssignmentBudget

/-! # Actual finite exposure states and their one-step determination -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimePatternStates

open Finset PaperP1.EvenPrimePatterns PaperP1.ExposureAssignmentBudget
open PaperP1.PrescribedPatternDivisors

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {ι : Type*}

abbrev State (ι : Type*) := (ι → ℕ) × (Finset ι → ℕ)

def Seen (rank : ι → ℕ) (k : ℕ) (S : Finset ι) : Prop := ∃ i ∈ S, rank i < k

def state (rank : ι → ℕ) (k : ℕ) (n : ι → ℕ) (D : Finset ι → ℕ) : State ι :=
  (fun i ↦ if rank i < k then n i else 0,
    fun S ↦ if Seen rank k S then D S else 1)

theorem coordinate_eq (rank : ι → ℕ) (k : ℕ) (n m : ι → ℕ) (D E : Finset ι → ℕ)
    (hstate : state rank k n D = state rank k m E) (i : ι) (hi : rank i < k) : n i = m i := by
  have h := congrArg (fun s : State ι ↦ s.1 i) hstate
  simpa only [state, ite_eq_left hi] using h

theorem factor_eq (rank : ι → ℕ) (k : ℕ) (n m : ι → ℕ) (D E : Finset ι → ℕ)
    (hstate : state rank k n D = state rank k m E) (S : Finset ι) (hS : Seen rank k S) : D S = E S := by
  have h := congrArg (fun s : State ι ↦ s.2 S) hstate
  simpa only [state, ite_eq_left hS] using h

theorem state_zero (rank : ι → ℕ) (n : ι → ℕ) (D : Finset ι → ℕ) :
    state rank 0 n D = (fun _ ↦ 0, fun _ ↦ 1) := by
  apply Prod.ext
  · funext i
    simp [state]
  · funext S
    simp [state, Seen]

theorem state_eq_mono (rank : ι → ℕ) (k l : ℕ) (hkl : k ≤ l)
    (n m : ι → ℕ) (D E : Finset ι → ℕ) (hstate : state rank l n D = state rank l m E) :
    state rank k n D = state rank k m E := by
  apply Prod.ext
  · funext i
    by_cases hi : rank i < k
    · have hil : rank i < l := by omega
      simpa only [state, ite_eq_left hi] using coordinate_eq rank l n m D E hstate i hil
    · simp only [state, ite_eq_right hi]
  · funext S
    by_cases hS : Seen rank k S
    · have hSl : Seen rank l S := by
        obtain ⟨i, hi, hik⟩ := hS
        exact ⟨i, hi, lt_of_lt_of_le hik hkl⟩
      simpa only [state, ite_eq_left hS] using factor_eq rank l n m D E hstate S hSl
    · simp only [state, ite_eq_right hS]

theorem final_coordinate_injective (rank : ι → ℕ) (v : ℕ) (hrange : ∀ i, rank i < v)
    (D : (ι → ℕ) → Finset ι → ℕ) : Function.Injective (fun n ↦ state rank v n (D n)) := by
  intro n m hnm
  funext i
  exact coordinate_eq rank v n m (D n) (D m) hnm i (hrange i)

variable [Fintype ι] [DecidableEq ι]

def stepRecord (rank : ι → ℕ) (i : ι) (n : ι → ℕ) (D : Finset ι → ℕ) :
    ℕ × (freshPatterns rank i → ℕ) := (n i, fun S ↦ D S.val)

theorem prescribed_eq_of_state_eq (q r : ι → ℕ) (rank : ι → ℕ) (k : ℕ) (i : ι)
    (hki : rank i = k) (n m : ι → ℕ)
    (hstate : state rank k n (part q) = state rank k m (part r)) :
    prescribed q rank i = prescribed r rank i := by
  apply prod_congr rfl
  intro S hS
  obtain ⟨_, _, j, hj, hji⟩ := mem_filter.mp hS
  exact factor_eq rank k n m (part q) (part r) hstate S ⟨j, hj, by omega⟩

theorem advance_determined (rank : ι → ℕ) (hrank : Function.Injective rank) (k : ℕ) (i : ι)
    (hki : rank i = k) (n m : ι → ℕ) (D E : Finset ι → ℕ)
    (hD : ∀ S ∉ patterns, D S = 1) (hE : ∀ S ∉ patterns, E S = 1)
    (hstate : state rank k n D = state rank k m E)
    (hrecord : stepRecord rank i n D = stepRecord rank i m E) :
    state rank (k + 1) n D = state rank (k + 1) m E := by
  apply Prod.ext
  · funext j
    by_cases hj : rank j < k + 1
    · have hnm : n j = m j := by
        by_cases hjk : rank j < k
        · exact coordinate_eq rank k n m D E hstate j hjk
        · have hji : j = i := hrank (by omega)
          subst j
          exact congrArg Prod.fst hrecord
      simpa only [state, ite_eq_left hj] using hnm
    · simp only [state, ite_eq_right hj]
  · funext S
    by_cases hS : Seen rank (k + 1) S
    · have hDE : D S = E S := by
        by_cases hprev : Seen rank k S
        · exact factor_eq rank k n m D E hstate S hprev
        · by_cases hpat : S ∈ patterns
          · obtain ⟨j, hj, hjk⟩ := hS
            have hjge : k ≤ rank j := by
              by_contra hnot
              exact hprev ⟨j, hj, by omega⟩
            have hji : j = i := hrank (by omega)
            have hiS : i ∈ S := hji ▸ hj
            have hfresh : S ∈ freshPatterns rank i := by
              apply mem_filter.mpr
              refine ⟨mem_filter.mpr ⟨hpat, hiS⟩, ?_⟩
              intro hearlier
              obtain ⟨j, hj, hji⟩ := hearlier
              exact hprev ⟨j, hj, by omega⟩
            exact congrArg (fun r : ℕ × (freshPatterns rank i → ℕ) ↦ r.2 ⟨S, hfresh⟩) hrecord
          · rw [hD S hpat, hE S hpat]
      simpa only [state, ite_eq_left hS] using hDE
    · simp only [state, ite_eq_right hS]

end PaperP1.PrimePatternStates
