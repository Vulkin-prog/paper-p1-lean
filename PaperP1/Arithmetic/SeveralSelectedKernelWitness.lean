module

public import PaperP1.Arithmetic.SeveralKernelReceivers
public import PaperP1.Arithmetic.SelectedKernelWitness

/-! # A selected anchor prime must be received by some other window -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeveralSelectedKernelWitness

open Finset PaperP1.Arithmetic PaperP1.LargeOddKernel PaperP1.KernelSupportFibres
open PaperP1.PrivateWindowPrimes

variable {ι : Type*} [Fintype ι]

def AnchoredRelation (U : ℕ) (V : ι → ℕ) (B : ℕ) (i : Fin B) : Prop :=
  ∃ w : Fin B → F₂, ∃ v : ι → Fin B → F₂, w i ≠ 0 ∧
    (∑ j, w j • parityVec (U + j.val)) +
      (∑ k, ∑ j, v k j • parityVec (V k + j.val)) = 0

theorem other_prime_divisor {U B p : ℕ} {V : ι → ℕ} (i : Fin B)
    (hrel : AnchoredRelation U V B i) (hp : p ∈ roughSupport B (U + i.val)) :
    ∃ k : ι, ∃ j : Fin B, p ∣ V k + j.val := by
  obtain ⟨w, v, hwi, hrel⟩ := hrel
  obtain ⟨hpodd, hBp⟩ := mem_filter.mp hp
  have hpi := mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hpodd
  by_contra hnone
  have hnot : ∀ k : ι, ∀ j : Fin B, ¬ p ∣ V k + j.val := by simpa only [not_exists] using hnone
  have hsecond : (∑ k : ι, ∑ j : Fin B, v k j * parityVec (V k + j.val) p) = 0 := by
    apply sum_eq_zero
    intro k _
    apply sum_eq_zero
    intro j _
    simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd (hnot k j),
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

theorem other_starts_mem_hits [DecidableEq ι] {x B U N : ℕ} {z : ι → ℕ} (i : Fin B)
    (hz : ∀ k, z k ∈ Finset.Ico U (U + N))
    (hrel : AnchoredRelation (x - 1) (fun k ↦ z k - 1) B i) :
    z ∈ PaperP1.SeveralKernelReceivers.hits (roughSupport B (x - 1 + i.val)) B U N := by
  refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hz, ?_⟩
  intro p hp
  exact other_prime_divisor i hrel hp

end PaperP1.SeveralSelectedKernelWitness
