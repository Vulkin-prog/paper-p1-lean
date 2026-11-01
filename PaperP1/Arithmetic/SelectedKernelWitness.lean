module

public import PaperP1.Arithmetic.KernelAssignments
public import PaperP1.Arithmetic.PrivateWindowPrimes

/-! # Selected large odd primes must divide a value in the other window -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedKernelWitness

open Finset PaperP1.Arithmetic PaperP1.LargeOddKernel PaperP1.KernelSupportFibres
open PaperP1.PrivateWindowPrimes

def AnchoredRelation (U V B : ℕ) (i : Fin B) : Prop :=
  ∃ w v : Fin B → F₂, w i ≠ 0 ∧
    (∑ j, w j • parityVec (U + j.val)) + (∑ j, v j • parityVec (V + j.val)) = 0

theorem other_prime_divisor {U V B p : ℕ} (i : Fin B)
    (hrel : AnchoredRelation U V B i) (hp : p ∈ roughSupport B (U + i.val)) :
    ∃ j : Fin B, p ∣ V + j.val := by
  obtain ⟨w, v, hwi, hrel⟩ := hrel
  obtain ⟨hpodd, hBp⟩ := mem_filter.mp hp
  have hpi := mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hpodd
  by_contra hnone
  have hnot : ∀ j : Fin B, ¬ p ∣ V + j.val := by simpa only [not_exists] using hnone
  have hsecond : (∑ j : Fin B, v j * parityVec (V + j.val) p) = 0 := by
    apply sum_eq_zero
    intro j _
    simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd (hnot j),
      Nat.cast_zero, mul_zero]
  have hfirst : (∑ j : Fin B, w j * parityVec (U + j.val) p) =
      w i * parityVec (U + i.val) p := by
    apply sum_eq_single i
    · intro j _ hji
      rw [parity_other_vertex_zero hBp i j hji.symm hpi, mul_zero]
    · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  have hcoord := congrArg (fun z : ℕ →₀ F₂ ↦ z p) hrel
  simp only [Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.zero_apply] at hcoord
  rw [hfirst, hsecond, add_zero] at hcoord
  exact (mul_ne_zero hwi hpi) hcoord

theorem other_start_mem_hits {x y B U N : ℕ} (i : Fin B)
    (hy : y ∈ Finset.Ico U (U + N))
    (hrel : AnchoredRelation (x - 1) (y - 1) B i) :
    y ∈ PaperP1.KernelAssignments.hits (roughSupport B (x - 1 + i.val)) B U N := by
  refine mem_filter.mpr ⟨hy, ?_⟩
  intro p hp
  exact other_prime_divisor i hrel hp

end PaperP1.SelectedKernelWitness
