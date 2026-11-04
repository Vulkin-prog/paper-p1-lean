module

public import PaperP1.Arithmetic.AsymmetricEvenLoss
public import PaperP1.Arithmetic.KernelAssignments
public import PaperP1.Arithmetic.PrivateWindowPrimes

/-! # Anchors need only a relation above the actual prime cutoff

The coefficient vectors are unrestricted on both sides. No old parity,
small-prime equation or full square-class relation is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TruncatedAnchorWitness

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEvenLoss PaperP1.LargeOddKernel
  PaperP1.PrivateWindowPrimes PaperP1.KernelSupportFibres

def AnchoredRelation (U V H : ℕ) (i : Fin H) : Prop :=
  ∃ w v : Fin H → F₂, w i ≠ 0 ∧
    (∑ j, w j • largeParity H (U + j.val)) = ∑ j, v j • largeParity H (V + j.val)

theorem parity_above (H n p : ℕ) (hp : H < p) : largeParity H n p = parityVec n p := by
  simp only [largeParity, Finsupp.filter_apply, hp, ite_true]

theorem other_prime_divisor {U V H p : ℕ} (i : Fin H)
    (hrel : AnchoredRelation U V H i) (hp : p ∈ roughSupport H (U + i.val)) :
    ∃ j : Fin H, p ∣ V + j.val := by
  obtain ⟨w, v, hwi, hrel⟩ := hrel
  obtain ⟨hpodd, hHp⟩ := mem_filter.mp hp
  have hpi := mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hpodd
  by_contra hnone
  have hnot : ∀ j : Fin H, ¬p ∣ V + j.val := by simpa only [not_exists] using hnone
  have hsecond : (∑ j : Fin H, v j * parityVec (V + j.val) p) = 0 := by
    apply sum_eq_zero
    intro j _
    simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd (hnot j), Nat.cast_zero, mul_zero]
  have hfirst : (∑ j : Fin H, w j * parityVec (U + j.val) p) =
      w i * parityVec (U + i.val) p := by
    apply sum_eq_single i
    · intro j _ hji
      rw [parity_other_vertex_zero hHp i j hji.symm hpi, mul_zero]
    · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  have hcoord := congrArg (fun z : ℕ →₀ F₂ ↦ z p) hrel
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, parity_above H _ p hHp] at hcoord
  rw [hfirst, hsecond] at hcoord
  exact (mul_ne_zero hwi hpi) hcoord

theorem other_start_mem_hits {x y H U N : ℕ} (i : Fin H)
    (hy : y ∈ Ico U (U + N)) (hrel : AnchoredRelation (x - 1) (y - 1) H i) :
    y ∈ KernelAssignments.hits (roughSupport H (x - 1 + i.val)) H U N := by
  exact mem_filter.mpr ⟨hy, fun _ hp ↦ other_prime_divisor i hrel hp⟩

end PaperP1.TruncatedAnchorWitness
