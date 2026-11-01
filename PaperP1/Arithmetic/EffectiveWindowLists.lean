module

public import PaperP1.Arithmetic.ProjectedWindowLists
public import PaperP1.Arithmetic.FiniteEvenSquareClasses

/-! # Arbitrary finite block effective spaces lift to actual even offset witnesses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveWindowLists

open Finset PaperP1.Arithmetic PaperP1.ProjectedWindowLists PaperP1.BoundedIntegerMotifs

def lists {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (O : Finset ℕ) :
    Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦ Function.Injective n ∧
    ∃ u : Fin r → (ℕ →₀ F₂),
      (∀ i, u i ∈ PaperP1.FiniteEvenSquareClasses.space (blocks i (n i)) ∧ u i ≠ 0) ∧
        (∑ i, u i) ∈ PaperP1.OldSpaceProjection.oldSpace O

theorem mem_lists {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (O : Finset ℕ)
    (n : Fin r → ℕ) : n ∈ lists G blocks O ↔
      (∀ i, n i ∈ G) ∧ Function.Injective n ∧ ∃ u : Fin r → (ℕ →₀ F₂),
        (∀ i, u i ∈ PaperP1.FiniteEvenSquareClasses.space (blocks i (n i)) ∧ u i ≠ 0) ∧
          (∑ i, u i) ∈ PaperP1.OldSpaceProjection.oldSpace O := by
  classical
  simp only [lists, mem_filter, Fintype.mem_piFinset]

theorem value_at_difference (x v : ℕ) :
    PaperP1.LinearKernelFibres.value x ((v : ℤ) - x) = v := by
  dsimp [PaperP1.LinearKernelFibres.value]
  rw [show (x : ℤ) + ((v : ℤ) - x) = v by abel]
  exact Int.natAbs_natCast v

theorem effective_nonempty (S : Finset ℕ) (u : ℕ →₀ F₂)
    (hu : u ∈ PaperP1.FiniteEvenSquareClasses.space S) (hne : u ≠ 0) : S.Nonempty := by
  by_contra hnot
  have hS := not_nonempty_iff_eq_empty.mp hnot
  have hu0 : u = 0 := by
    simpa only [hS, PaperP1.FiniteEvenSquareClasses.space_empty, Submodule.mem_bot] using hu
  exact hne hu0

theorem mem_blockValues_of_distance (W x v : ℕ) (h : ((v : ℤ) - x).natAbs ≤ W) :
    v ∈ blockValues W x := by
  apply mem_image.mpr
  refine ⟨(v : ℤ) - x, ?_, value_at_difference x v⟩
  exact (subset_offsets W {((v : ℤ) - x)}).mpr (by
    intro a ha
    rw [mem_singleton.mp ha]
    exact h) (mem_singleton_self _)

theorem even_space_selection (S : Finset ℕ) (u : ℕ →₀ F₂)
    (hu : u ∈ PaperP1.FiniteEvenSquareClasses.space S) :
    ∃ B : Finset ℕ, B ⊆ S ∧ Even B.card ∧ (∑ v ∈ B, parityVec v) = u := by
  classical
  obtain ⟨w, hw, hwu⟩ := (PaperP1.EvenImage.mem_image_iff
    (PaperP1.FiniteEvenSquareClasses.data S) u).mp hu
  let T := PaperP1.FiniteEvenSquareClasses.selected S w
  let B := T.image Subtype.val
  have hBsub : B ⊆ S := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := mem_image.mp hv
    exact a.property
  have hcard : B.card = T.card := card_image_of_injective T Subtype.val_injective
  have heven : Even T.card := (PaperP1.FiniteEvenSquareClasses.zero_sum_iff_even_selected S w).mp hw
  refine ⟨B, hBsub, hcard.symm ▸ heven, ?_⟩
  calc
    _ = ∑ v ∈ T, parityVec v.val := by
      apply sum_image
      intro a _ b _ hab
      exact Subtype.ext hab
    _ = PaperP1.EvenImage.combination (PaperP1.FiniteEvenSquareClasses.data S) w := by
      rw [PaperP1.EvenImage.combination_apply]
      dsimp [T, PaperP1.FiniteEvenSquareClasses.selected, PaperP1.FiniteEvenSquareClasses.data]
      rw [sum_filter]
      apply sum_congr rfl
      intro v _
      rcases binary_eq_zero_or_one (w v) with hz | ho
      · simp [hz]
      · simp [ho]
    _ = u := hwu

theorem lift_selection (W x : ℕ) (B : Finset ℕ) (hx : W < x)
    (hB : B ⊆ blockValues W x) (heven : Even B.card) :
    ∃ A : Finset ℤ, Even A.card ∧ A ⊆ offsets W ∧ vector x A = ∑ v ∈ B, parityVec v := by
  classical
  let f := fun v : ℕ ↦ (v : ℤ) - (x : ℤ)
  have hf : Function.Injective f := by
    intro v w h
    have hcast : (v : ℤ) = w := sub_left_inj.mp h
    exact_mod_cast hcast
  let A := B.image f
  have hA : A ⊆ offsets W := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    obtain ⟨b, hb, hval⟩ := mem_image.mp (hB hv)
    have hcast := PaperP1.SmoothModulusHosts.value_cast x W b hx
      ((subset_offsets W (offsets W)).mp Subset.rfl b hb)
    rw [hval] at hcast
    have hdiff : f v = b := by dsimp [f]; omega
    exact hdiff.symm ▸ hb
  have hcard : A.card = B.card := card_image_of_injective B hf
  refine ⟨A, hcard.symm ▸ heven, hA, ?_⟩
  rw [vector, sum_image]
  · apply sum_congr rfl
    intro v _
    congr 1
    dsimp [PaperP1.LinearKernelFibres.value, f]
    rw [show (x : ℤ) + ((v : ℤ) - x) = v by abel]
    exact Int.natAbs_natCast v
  · exact fun a _ b _ hab ↦ hf hab

theorem subset_window_lists {r s : ℕ} (G T : Finset ℕ) (W : ℕ) (old : Fin s → ℕ)
    (blocks : Fin r → ℕ → Finset ℕ) (O : Finset ℕ) (hGT : G ⊆ T)
    (hG : ∀ x ∈ G, W < x) (hblocks : ∀ i, ∀ x ∈ G, blocks i x ⊆ blockValues W x)
    (hO : O ⊆ oldValues W old) :
    lists G blocks O ⊆ PaperP1.ProjectedWindowLists.lists T W old := by
  classical
  intro n hn
  obtain ⟨hnG, hinj, u, hu, hsum⟩ := (mem_lists G blocks O n).mp hn
  have hselected : ∀ i, ∃ A : Finset ℤ, Admissible W (n i) A ∧ vector (n i) A = u i := by
    intro i
    obtain ⟨B, hB, heven, hBu⟩ := even_space_selection (blocks i (n i)) (u i) (hu i).1
    obtain ⟨A, hAeven, hApool, hAu⟩ := lift_selection W (n i) B (hG (n i) (hnG i))
      (hB.trans (hblocks i (n i) (hnG i))) heven
    refine ⟨A, ⟨hAeven, hApool, ?_⟩, hAu.trans hBu⟩
    rw [hAu, hBu]
    exact (hu i).2
  choose A hA hAu using hselected
  apply (PaperP1.ProjectedWindowLists.mem_lists T W old n).mpr
  refine ⟨fun i ↦ hGT (hnG i), hinj, A, hA, ?_⟩
  have heq : (∑ i, vector (n i) (A i)) = ∑ i, u i := sum_congr rfl (fun i _ ↦ hAu i)
  rw [heq]
  exact oldSpace_mono hO hsum

end PaperP1.EffectiveWindowLists
