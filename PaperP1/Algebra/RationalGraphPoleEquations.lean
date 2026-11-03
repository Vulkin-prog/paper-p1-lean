module

public import PaperP1.Algebra.RationalGraphSquareRoots
public import Mathlib.Algebra.Polynomial.Roots

/-! # Only degree-many disjoint offset equations meet actual poles of a rational graph -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalGraphPoleEquations

open Polynomial Finset

variable {F ι : Type*} [Field F] [CharZero F]

def badEquations (A : Finset ι) (I : ι → Finset ℤ) (q : F[X]) : Finset ι := by
  classical
  exact A.filter fun ν ↦ ∃ z ∈ I ν, q.eval (-(z : F)) = 0

omit [CharZero F] in
theorem mem_badEquations (A : Finset ι) (I : ι → Finset ℤ) (q : F[X]) (ν : ι) :
    ν ∈ badEquations A I q ↔ ν ∈ A ∧ ∃ z ∈ I ν, q.eval (-(z : F)) = 0 := by
  classical
  exact Finset.mem_filter

theorem card_badEquations_le (A : Finset ι) (I : ι → Finset ℤ) (q : F[X]) (hq : q ≠ 0)
    (hdisj : (A : Set ι).PairwiseDisjoint I) : (badEquations A I q).card ≤ q.natDegree := by
  classical
  choose z hzI hzroot using (fun ν : badEquations A I q ↦ (mem_badEquations A I q ν).mp ν.property |>.2)
  let f : badEquations A I q → q.roots.toFinset := fun ν ↦
    ⟨-(z ν : F), Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr (hzroot ν))⟩
  have hf : Function.Injective f := by
    intro ν μ h
    have hneg : -(z ν : F) = -(z μ : F) := congrArg Subtype.val h
    have heq : z ν = z μ := Int.cast_injective (neg_injective hneg)
    apply Subtype.ext
    by_contra hne
    exact Finset.disjoint_left.mp
      (hdisj ((mem_badEquations A I q ν).mp ν.property).1 ((mem_badEquations A I q μ).mp μ.property).1 hne)
      (hzI ν) (heq ▸ hzI μ)
  exact (Finset.card_le_card_of_injective hf).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' q))

variable [DecidableEq ι]

omit [CharZero F] in
theorem survivor_nonvanishing (A : Finset ι) (I : ι → Finset ℤ) (q : F[X])
    (ν : ι) (hν : ν ∈ A \ badEquations A I q) (z : ℤ) (hz : z ∈ I ν) :
    q.eval (-(z : F)) ≠ 0 := by
  intro hzero
  exact (Finset.mem_sdiff.mp hν).2 ((mem_badEquations A I q ν).mpr ⟨(Finset.mem_sdiff.mp hν).1, z, hz, hzero⟩)

theorem survivors_card (A : Finset ι) (I : ι → Finset ℤ) (p q : F[X]) (hq : q ≠ 0)
    (hdisj : (A : Set ι).PairwiseDisjoint I)
    (hA : 3 * max p.natDegree q.natDegree + 1 ≤ A.card) :
    2 * max p.natDegree q.natDegree + 1 ≤ (A \ badEquations A I q).card := by
  have hbad := card_badEquations_le A I q hq hdisj
  have hqdeg := le_max_right p.natDegree q.natDegree
  have hcard : A.card ≤ (A \ badEquations A I q).card + (badEquations A I q).card := card_le_card_sdiff_add_card
  omega

end PaperP1.RationalGraphPoleEquations
