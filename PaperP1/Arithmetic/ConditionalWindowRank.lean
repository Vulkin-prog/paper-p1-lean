module

public import PaperP1.Algebra.EvenSupportRank
public import PaperP1.Algebra.QuotientRank
public import PaperP1.Coding.WindowRelationCode
public import PaperP1.Arithmetic.LargeOddKernel

/-! # The actual conditional relation kernel is supported on the old prime pool -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalWindowRank

open Finset PaperP1.Arithmetic PaperP1.DefectCounting PaperP1.DefectivePredicate
  PaperP1.WindowRelationCode PaperP1.LargeOddKernel

def oldPrimes (R : Finset ℕ) : Finset ℕ := R.biUnion Nat.primeFactors

def primePool (R : Finset ℕ) (B : ℕ) : Finset ℕ := smallPrimesUpTo B ∪ oldPrimes R

def oldSpan (R : Finset ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  Submodule.span F₂ (parityVec '' (R : Set ℕ))

instance oldSpan_finite (R : Finset ℕ) : FiniteDimensional F₂ (oldSpan R) :=
  FiniteDimensional.span_of_finite _ (R.finite_toSet.image parityVec)

def supportedIndices (R : Finset ℕ) (U B : ℕ) : Finset (Fin B) :=
  univ.filter fun i ↦ oddPrimeSupport (U + i.val) ⊆ primePool R B

def evenMap (U B : ℕ) : LinearMap.ker (windowEvennessMap B) →ₗ[F₂] (ℕ →₀ F₂) :=
  (windowParityMap U B).comp (LinearMap.ker (windowEvennessMap B)).subtype

def relativeKernel (R : Finset ℕ) (U B : ℕ) :
    Submodule F₂ (LinearMap.ker (windowEvennessMap B)) := (oldSpan R).comap (evenMap U B)

def conditionalNullity (R : Finset ℕ) (U B : ℕ) : ℕ := Module.finrank F₂ (relativeKernel R U B)

theorem primePool_prime (R : Finset ℕ) (B p : ℕ) (hp : p ∈ primePool R B) : Nat.Prime p := by
  rcases mem_union.mp hp with hp | hp
  · exact (mem_smallPrimesUpTo.mp hp).1
  · obtain ⟨n, _, hn⟩ := mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors hn

theorem oldSpan_coordinate_zero {R : Finset ℕ} {p : ℕ} (hp : p ∉ oldPrimes R)
    {v : ℕ →₀ F₂} (hv : v ∈ oldSpan R) : v p = 0 := by
  have hle : oldSpan R ≤ LinearMap.ker (Finsupp.lapply p : (ℕ →₀ F₂) →ₗ[F₂] F₂) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, hn, rfl⟩
    change parityVec n p = 0
    by_contra hparity
    have hfactor : p ∈ n.primeFactors := Finsupp.support_mapRange (Finsupp.mem_support_iff.mpr hparity)
    exact hp (mem_biUnion.mpr ⟨n, hn, hfactor⟩)
  exact hle hv

theorem coefficient_zero_outside_pool {R : Finset ℕ} {U B : ℕ} (w : Fin B → F₂)
    (hw : windowParityMap U B w ∈ oldSpan R) (i : Fin B)
    (hi : i ∉ supportedIndices R U B) : w i = 0 := by
  classical
  have hnot : ¬oddPrimeSupport (U + i.val) ⊆ primePool R B := by
    simpa only [supportedIndices, mem_filter, mem_univ, true_and] using hi
  obtain ⟨p, hp, hpPool⟩ := Finset.not_subset.mp hnot
  have hprime := prime_of_mem_oddPrimeSupport hp
  have hparity := mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hp
  have hBp : B < p := by
    by_contra h
    exact hpPool (mem_union_left _ (mem_smallPrimesUpTo.mpr ⟨hprime, by omega⟩))
  have hcoord := oldSpan_coordinate_zero (R := R) (p := p)
    (fun h ↦ hpPool (mem_union_right _ h)) hw
  change (∑ j, w j • parityVec (U + j.val)) p = 0 at hcoord
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at hcoord
  have hsum : (∑ j : Fin B, w j * parityVec (U + j.val) p) = w i * parityVec (U + i.val) p := by
    apply sum_eq_single i
    · intro j _ hji
      rw [PrivateWindowPrimes.parity_other_vertex_zero hBp i j hji.symm hparity, mul_zero]
    · simp
  rw [hsum] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_right hparity

theorem conditionalNullity_le (R : Finset ℕ) (U B : ℕ) :
    conditionalNullity R U B ≤ (supportedIndices R U B).card - 1 := by
  unfold conditionalNullity
  let g : relativeKernel R U B →ₗ[F₂] (Fin B → F₂) :=
    (LinearMap.ker (windowEvennessMap B)).subtype.comp (relativeKernel R U B).subtype
  have hg : Function.Injective g := Subtype.val_injective.comp Subtype.val_injective
  refine EvenSupportRank.finrank_le_of_supported_even (K := F₂) (E := relativeKernel R U B)
    g hg (supportedIndices R U B) ?_ ?_
  · intro w i hi
    exact coefficient_zero_outside_pool w.val.val w.property i hi
  · intro w
    change (∑ i, w.val.val i) = 0
    have h := w.val.property
    change windowEvennessMap B w.val.val = 0 at h
    simpa only [windowEvennessMap, Fintype.linearCombination_apply, smul_eq_mul, mul_one] using h

theorem conditionalNullity_eq_zero_of_card_le_one {R : Finset ℕ} {U B : ℕ}
    (hcard : (supportedIndices R U B).card ≤ 1) : conditionalNullity R U B = 0 := by
  have h := conditionalNullity_le R U B
  omega

end PaperP1.ConditionalWindowRank
