module

public import PaperP1.Algebra.UnivariateSplitSquareClasses
public import PaperP1.Algebra.SquareClassRadicalDegreeBound

/-! # Actual finite covers of univariate split radical data have exponential degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnivariateRadicalCoverDegree

open Finset PaperP1.FieldSquareClasses

variable {R K L ι : Type*} [CommRing R] [IsDomain R] [CharZero R] [IsIntegrallyClosed R]
  [Field K] [Field L] [Algebra K L] [Fintype ι]

theorem power_dvd_degree (e : K ≃+* UnivariateSplitSquareClasses.FunctionField R)
    (a : ι → K) (c : ι → R) (hc : ∀ i, c i ≠ 0) (I : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty) (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hvalue : ∀ i, e (a i) = UnivariateSplitSquareClasses.value (c i) (I i))
    (r : ι → L) (hr : ∀ i, r i ^ 2 = algebraMap K L (a i)) :
    2 ^ Fintype.card ι ∣ Module.finrank K L := by
  let : CharZero K := charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  have ha (i : ι) : a i ≠ 0 := by
    intro hz
    have h := congrArg e hz
    rw [hvalue i, map_zero] at h
    exact UnivariateSplitSquareClasses.value_ne_zero (c i) (hc i) (I i) h
  have hli : LinearIndependent (ZMod 2) (fun i ↦ ofNonzero (a i) (ha i)) := by
    apply LinearIndependent.of_comp (FieldSquareClassMap.map e.toRingHom)
    have heq : (FieldSquareClassMap.map e.toRingHom) ∘ (fun i ↦ ofNonzero (a i) (ha i)) =
        fun i ↦ UnivariateSplitSquareClasses.squareClass (c i) (hc i) (I i) := by
      funext i
      simp only [Function.comp_apply, FieldSquareClassMap.map_ofNonzero]
      change ofNonzero (e (a i)) _ = _
      simp only [hvalue i, UnivariateSplitSquareClasses.squareClass]
    rw [heq]
    exact UnivariateSplitSquareClasses.linearIndependent c hc I hne hI
  simpa only [Finset.card_univ] using
    SquareClassRadicalDegreeBound.power_dvd_degree a ha hli Finset.univ
      (fun i _ ↦ ⟨r i, by simpa only [pow_two] using (hr i).symm⟩)

theorem power_le_degree [Module.Finite K L] (e : K ≃+* UnivariateSplitSquareClasses.FunctionField R)
    (a : ι → K) (c : ι → R) (hc : ∀ i, c i ≠ 0) (I : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty) (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hvalue : ∀ i, e (a i) = UnivariateSplitSquareClasses.value (c i) (I i))
    (r : ι → L) (hr : ∀ i, r i ^ 2 = algebraMap K L (a i)) :
    2 ^ Fintype.card ι ≤ Module.finrank K L :=
  Nat.le_of_dvd Module.finrank_pos (power_dvd_degree e a c hc I hne hI hvalue r hr)

theorem no_bounded_cover [Module.Finite K L] (e : K ≃+* UnivariateSplitSquareClasses.FunctionField R)
    (a : ι → K) (c : ι → R) (hc : ∀ i, c i ≠ 0) (I : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty) (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hvalue : ∀ i, e (a i) = UnivariateSplitSquareClasses.value (c i) (I i))
    (r : ι → L) (hr : ∀ i, r i ^ 2 = algebraMap K L (a i)) (E : ℕ)
    (hrank : Module.finrank K L ≤ E) (hlarge : E ≤ Fintype.card ι) : False := by
  have h := power_le_degree e a c hc I hne hI hvalue r hr
  exact (Fintype.card ι).lt_two_pow_self.not_ge (h.trans (hrank.trans hlarge))

end PaperP1.UnivariateRadicalCoverDegree
