module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Prime

/-! # Actual homogeneous products separate any finite incomparable family of homogeneous primes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousPrimeSeparators

open DirectSum Finset

theorem homogeneous_outside {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] (I J : Ideal A)
    (hI : I.IsHomogeneous H) (hnot : ¬ I ≤ J) :
    ∃ (e : ℕ) (a : A), a ∈ H e ∧ a ∈ I ∧ a ∉ J := by
  classical
  have hex : ∃ a : A, a ∈ I ∧ a ∉ J := by
    by_contra! hh
    exact hnot (fun a ha ↦ hh a ha)
  obtain ⟨a, haI, haJ⟩ := hex
  have hn : ∃ n, (decompose H a n : A) ∉ J := by
    by_contra! hh
    apply haJ
    rw [← sum_support_decompose H a]
    exact J.sum_mem (fun n _hn ↦ hh n)
  obtain ⟨n, hn⟩ := hn
  exact ⟨n, decompose H a n, (decompose H a n).property, (hI.mem_iff.mp haI) n, hn⟩

theorem one_separator {F A ι : Type*} [Field F] [CommRing A] [Algebra F A] [Fintype ι]
    (H : ℕ → Submodule F A) [GradedAlgebra H] (Q : ι → Ideal A)
    (hprime : ∀ i, (Q i).IsPrime) (hhom : ∀ i, (Q i).IsHomogeneous H)
    (hinc : ∀ i j, j ≠ i → ¬ Q j ≤ Q i) (i : ι) :
    ∃ (w : ℕ) (f : A), f ∈ H w ∧ f ∉ Q i ∧ ∀ j, j ≠ i → f ∈ Q j := by
  classical
  let T := (univ : Finset ι).erase i
  have hex : ∀ j : T, ∃ (n : ℕ) (a : A), a ∈ H n ∧ a ∈ Q j.val ∧ a ∉ Q i := by
    intro j
    exact homogeneous_outside H (Q j.val) (Q i) (hhom j.val)
      (hinc i j.val (Finset.mem_erase.mp j.property).1)
  choose w a ha using hex
  refine ⟨∑ j : T, w j, ∏ j : T, a j,
    SetLike.prod_mem_graded H w a (fun j _hj ↦ (ha j).1), ?_, ?_⟩
  · have hnon : ∀ S : Finset T, (∏ j ∈ S, a j) ∉ Q i := by
      intro S
      induction S using Finset.induction_on with
      | empty => simpa only [prod_empty] using (hprime i).one_notMem
      | @insert j S hj ih =>
        rw [prod_insert hj]
        exact (hprime i).mul_notMem (ha j).2.2 ih
    exact hnon univ
  · intro j hji
    let j' : T := ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩⟩
    exact (Q j).prod_mem (Finset.mem_univ j') (ha j').2.1

theorem finite_family {F A ι : Type*} [Field F] [CommRing A] [Algebra F A] [Fintype ι]
    (H : ℕ → Submodule F A) [GradedAlgebra H] (Q : ι → Ideal A)
    (hprime : ∀ i, (Q i).IsPrime) (hhom : ∀ i, (Q i).IsHomogeneous H)
    (hinc : ∀ i j, j ≠ i → ¬ Q j ≤ Q i) :
    ∃ (w : ι → ℕ) (f : ι → A), ∀ i, f i ∈ H (w i) ∧ f i ∉ Q i ∧
      ∀ j, j ≠ i → f i ∈ Q j := by
  choose w f hf using fun i ↦ one_separator H Q hprime hhom hinc i
  exact ⟨w, f, hf⟩

end PaperP1.HomogeneousPrimeSeparators
