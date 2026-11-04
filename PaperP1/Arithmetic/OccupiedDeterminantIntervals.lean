module

public import PaperP1.Arithmetic.DeterminantIntervalPartition

/-! # Exact population summation over the actually occupied determinant intervals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OccupiedDeterminantIntervals

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantRelativeIntervals PaperP1.DeterminantIntervalPartition

def occupied (M : ℕ) (D E : ℝ) (S : Finset Quad) : Finset ℕ :=
  (intervalIndices M).filter (fun k ↦ (cluster M D E k S).Nonempty)

theorem sum_clusters (M : ℕ) (D E : ℝ) (S : Finset Quad) :
    (∑ k ∈ intervalIndices M, (cluster M D E k S).card) =
      ∑ k ∈ occupied M D E S, (cluster M D E k S).card := by
  unfold occupied
  rw [sum_filter]
  apply sum_congr rfl
  intro k _
  by_cases hk : (cluster M D E k S).Nonempty
  · simp only [ite_eq_left hk]
  · have he := not_nonempty_iff_eq_empty.mp hk
    simp [he]

theorem index_range (M : ℕ) (hM : 4 ≤ M) (D E : ℝ) (hD : 0 < D) (hE : 0 < E)
    (S : Finset Quad)
    (hS : ∀ p ∈ S, D ≤ p.1.1 ∧ (p.1.1 : ℝ) ≤ 2 * D ∧ E ≤ p.1.2 ∧ (p.1.2 : ℝ) ≤ 2 * E) :
    ∀ k ∈ occupied M D E S, M ≤ 4 * k ∧ k ≤ 2 * M := by
  intro k hk
  obtain ⟨hkI, hnonempty⟩ := mem_filter.mp hk
  obtain ⟨p, hp⟩ := hnonempty
  obtain ⟨hpS, hindex⟩ := (mem_cluster M D E k S p).mp hp
  have hbox := hS p hpS
  have hi := index_bounds M hM hD hE hbox.1 hbox.2.1 hbox.2.2.1 hbox.2.2.2
  rw [hindex] at hi
  have hlo : (M : ℝ) ≤ 4 * k := by linarith only [hi.1]
  exact ⟨by exact_mod_cast hlo, (mem_Icc.mp hkI).2⟩

end PaperP1.OccupiedDeterminantIntervals
