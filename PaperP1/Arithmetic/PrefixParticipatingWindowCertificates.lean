module

public import PaperP1.Arithmetic.SeveralSelectedKernelWitness
public import PaperP1.Arithmetic.PrefixModerateCertificateCount
public import PaperP1.Arithmetic.PrefixSaturationPrimes
public import PaperP1.Arithmetic.RelativeBlockRelations
public import PaperP1.Arithmetic.NormalizedWindowSets
public import PaperP1.Algebra.BinaryEvenSelections

/-! # Every unmarked participating window yields a moderate certificate or an actual saturation edge, uniformly in the order -/

/-! The centre range in this module is the positive prefix [2,N+2),
with exactly N centres; no critical lower bound on a centre is assumed. -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrefixParticipatingWindowCertificates

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PrefixModerateAnchors
  PaperP1.PrefixModerateCertificateCount PaperP1.TruncatedKernelProducts PaperP1.PrimeAssignments PaperP1.RankinSmallKernel

local instance participatingCertificatesPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem other_odd_receiver {ι : Type*} [Fintype ι] {U B p : ℕ} {V : ι → ℕ} (i : Fin B)
    (hrel : SeveralSelectedKernelWitness.AnchoredRelation U V B i)
    (hp : p ∈ KernelSupportFibres.roughSupport B (U + i.val)) :
    ∃ k : ι, ∃ j : Fin B, p ∈ DefectivePredicate.oddPrimeSupport (V k + j.val) := by
  classical
  obtain ⟨w, v, hwi, hrel⟩ := hrel
  obtain ⟨hpodd, hBp⟩ := mem_filter.mp hp
  have hpi := LargeOddKernel.mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hpodd
  by_contra hnone
  have hnot : ∀ k : ι, ∀ j : Fin B, parityVec (V k + j.val) p = 0 := by
    intro k j
    apply not_ne_iff.mp
    intro hne
    exact hnone ⟨k, j, LargeOddKernel.mem_oddPrimeSupport_iff_parityVec_ne_zero.mpr hne⟩
  have hsecond : (∑ k : ι, ∑ j : Fin B, v k j * parityVec (V k + j.val) p) = 0 := by
    apply sum_eq_zero
    intro k _
    exact sum_eq_zero fun j _ ↦ by rw [hnot k j, mul_zero]
  have hfirst : (∑ j : Fin B, w j * parityVec (U + j.val) p) = w i * parityVec (U + i.val) p := by
    apply sum_eq_single i
    · intro j _ hji
      rw [PrivateWindowPrimes.parity_other_vertex_zero hBp i j hji.symm hpi, mul_zero]
    · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  have hcoord := congrArg (fun z : ℕ →₀ F₂ ↦ z p) hrel
  simp only [Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.zero_apply] at hcoord
  rw [hfirst, hsecond, add_zero] at hcoord
  exact (mul_ne_zero hwi hpi) hcoord

theorem physical_relation {r L N : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, n i ∈ Ico 2 (N + 2)) (_hN : 2 ≤ N)
    (hc : RelativeBlockRelations.Covered
      (fun _ x ↦ NormalizedWindowSets.values x L) ∅ n) (a : Fin r) :
    ∃ w : Fin r → Fin (L + 1) → F₂, (∀ j, (∑ v, w j v) = 0) ∧ w a ≠ 0 ∧
      (∑ j, ∑ v, w j v • parityVec (n j - 1 + v.val)) = 0 := by
  classical
  obtain ⟨u, hu, hne, hsum⟩ := hc a
  have hzero : (∑ j, u j) = 0 := by
    simpa only [OldSpaceProjection.oldSpace, FiniteSetValueSpan.span, coe_empty,
      Set.image_empty, Submodule.span_empty, Submodule.mem_bot] using hsum
  have hlift (j : Fin r) : ∃ w : Fin (L + 1) → F₂,
      (∑ v, w v) = 0 ∧ (∑ v, w v • parityVec (n j - 1 + v.val)) = u j := by
    have hj : u j ∈ squareClassSpace (n j) L := by
      rw [← NormalizedWindowSets.space_values]
      exact hu j
    rw [NormalizedWindowSets.squareClassSpace_eq_evenImage] at hj
    obtain ⟨w, hw, heq⟩ := (EvenImage.mem_image_iff _ _).mp hj
    refine ⟨w, hw, ?_⟩
    rw [EvenImage.combination_apply] at heq
    simpa only [startCompleteVertexLabel_eq_offset (show 0 < n j by have h := (mem_Ico.mp (hn j)).1; omega)] using heq
  choose w hw heq using hlift
  refine ⟨w, hw, ?_, ?_⟩
  · intro hwa
    have hz : u a = 0 := by rw [← heq a, hwa]; simp
    exact hne hz
  · simpa only [heq] using hzero

theorem coordinate_alternative {r L N : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, n i ∈ Ico 2 (N + 2)) (hinj : Function.Injective n)
    (hN : 2 ≤ N) (Y T : ℝ)
    (hY : ((L + 1 : ℕ) : ℝ) ≤ Y)
    (hc : RelativeBlockRelations.Covered
      (fun _ x ↦ NormalizedWindowSets.values x L) ∅ n)
    (a : Fin r) (hunmarked : Unmarked (L + 1) Y T (n a)) :
    HasCertificate r (L + 1) N Y T n ∨
      ∃ j : Fin r, PrefixSaturationPrimes.Edge (L + 1) N Y (n a) (n j) := by
  classical
  obtain ⟨w, hw, hwa, htotal⟩ := physical_relation n hn (by omega) hc a
  let wa : LinearMap.ker (EvenSupportRank.sumMap F₂ (Fin (L + 1))) := ⟨w a, by
    simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using hw a⟩
  have hwa' : wa ≠ 0 := fun hz ↦ hwa (congrArg Subtype.val hz)
  have htwo := BinaryEvenSelections.selected_card_two hwa'
  change 2 ≤ (BinaryEvenSelections.selected (w a)).card at htwo
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (show 1 < (BinaryEvenSelections.selected (w a)).card by omega)
  have hwu : w a u ≠ 0 := (mem_filter.mp hu).2
  have hwv : w a v ≠ 0 := (mem_filter.mp hv).2
  let A : Anchor r (L + 1) N := (a, ⟨n a, hn a⟩, u, v)
  have hrelation : (∑ i, w a i • parityVec (n a - 1 + i.val)) +
      (∑ j : Receiver a, ∑ i, w j.val i • parityVec (n j.val - 1 + i.val)) = 0 := by
    rw [← Fintype.sum_eq_add_sum_subtype_ne (fun j ↦ ∑ i, w j i • parityVec (n j - 1 + i.val)) a]
    exact htotal
  have hreceiving : ∀ p : primes Y A, ∃ j : Receiver a, ∃ i : Fin (L + 1),
      p.val ∈ DefectivePredicate.oddPrimeSupport (n j.val - 1 + i.val) := by
    intro p
    have hpp := Nat.prime_of_mem_primeFactors p.property
    have hdvd := Nat.dvd_of_mem_primeFactors p.property
    have hdiv : p.val ∣ truncatedKernel Y (n a - 1 + u.val) ∨
        p.val ∣ truncatedKernel Y (n a - 1 + v.val) := hpp.dvd_mul.mp hdvd
    rcases hdiv with hp | hp
    · have hs := (prime_dvd_kernel_iff Y _ _ hpp).mp hp
      have hBp : L + 1 < p.val := by exact_mod_cast hY.trans_lt (mem_filter.mp hs).2
      exact other_odd_receiver u ⟨w a, (fun j : Receiver a ↦ w j.val), hwu, hrelation⟩
        (mem_filter.mpr ⟨(mem_filter.mp hs).1, hBp⟩)
    · have hs := (prime_dvd_kernel_iff Y _ _ hpp).mp hp
      have hBp : L + 1 < p.val := by exact_mod_cast hY.trans_lt (mem_filter.mp hs).2
      exact other_odd_receiver v ⟨w a, (fun j : Receiver a ↦ w j.val), hwv, hrelation⟩
        (mem_filter.mpr ⟨(mem_filter.mp hs).1, hBp⟩)
  choose recv off hodd using hreceiving
  let f : Code (ι := Receiver a) (primes Y A) (L + 1) := fun p ↦ (recv p, off p)
  by_cases hmoderate : ∀ j : Receiver a, groupModulus f j ≤ 6 * N * (L + 1)
  · exact Or.inl ⟨hinj, A, rfl, huv, hunmarked, f, hmoderate, hodd⟩
  · push Not at hmoderate
    obtain ⟨j, hj⟩ := hmoderate
    refine Or.inr ⟨j.val, (fun heq ↦ j.property (hinj heq).symm), u, v, huv, groupModulus f j, hj, ?_, ?_⟩
    · have hd : groupModulus f j ∣ (primes Y A).prod id := by
        rw [← product_groupModulus f]
        exact dvd_prod_of_mem _ (mem_univ j)
      exact hd.trans (Nat.prod_primeFactors_dvd _)
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hdvd : p ∣ ∏ q : Group f j, groupPrime f j q := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨q, _, hpq⟩ := (hpp.prime.dvd_finsetProd_iff (groupPrime f j)).mp hdvd
      have hpeq : p = q.val.val := (Nat.prime_dvd_prime_iff_eq hpp
        (Nat.prime_of_mem_primeFactors q.val.property)).mp hpq
      refine ⟨(f q.val).2, ?_⟩
      have hmem := hodd q.val
      have hrecv : recv q.val = j := q.property
      rw [hrecv] at hmem
      simpa only [hpeq, PrefixSaturationPrimes.value, f] using dvd_of_mem_oddPrimeSupport hmem

end PaperP1.PrefixParticipatingWindowCertificates
