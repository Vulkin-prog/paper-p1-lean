module

public import PaperP1.Arithmetic.MultiAnchorCertificateCount
public import PaperP1.Arithmetic.MultiAnchorSaturation
public import PaperP1.Arithmetic.ParticipatingWindowCertificates

/-! # Selected large-kernel anchors suffice for a moderate certificate or a saturated edge -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedAnchorRelation

open Finset PaperP1.Arithmetic PaperP1.MultiAnchorValues
  PaperP1.MultiAnchorCertificateCount PaperP1.TruncatedKernelProducts PaperP1.PrimeAssignments
open PaperP1.ModerateAnchors (Receiver)

local instance multiAnchorRelationPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem coordinate_alternative {t r B N : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, n i ∈ Ico N (2 * N)) (hinj : Function.Injective n)
    (Y T : ℝ) (hY : (B : ℝ) ≤ Y) (a : Fin r)
    (w : Fin r → Fin B → F₂)
    (u : Fin t → Fin B) (hu : Function.Injective u)
    (hwu : ∀ i, w a (u i) ≠ 0)
    (hlarge : ∀ i, T < (PaperP1.RankinSmallKernel.truncatedKernel Y (n a - 1 + (u i).val) : ℝ))
    (htotal : (∑ j, ∑ i, w j i • parityVec (n j - 1 + i.val)) = 0) :
    n ∈ PaperP1.MultiAnchorTupleCover.tupleCover t r B N Y T ∨
      ∃ j : Fin r, PaperP1.MultiAnchorSaturation.Edge t B N Y (n a) (n j) := by
  classical
  let A : Anchor t r B N := (a, ⟨n a, hn a⟩, u)
  have hrelation : (∑ i, w a i • parityVec (n a - 1 + i.val)) +
      (∑ j : Receiver a, ∑ i, w j.val i • parityVec (n j.val - 1 + i.val)) = 0 := by
    rw [← Fintype.sum_eq_add_sum_subtype_ne
      (fun j ↦ ∑ i, w j i • parityVec (n j - 1 + i.val)) a]
    exact htotal
  have hreceiving : ∀ p : primes Y A, ∃ j : Receiver a, ∃ i : Fin B,
      p.val ∈ PaperP1.DefectivePredicate.oddPrimeSupport (n j.val - 1 + i.val) := by
    intro p
    obtain ⟨i, hi⟩ := prime_receiving_value Y A p.property
    have hBp : B < p.val := by exact_mod_cast hY.trans_lt (mem_filter.mp hi).2
    exact PaperP1.ParticipatingWindowCertificates.other_odd_receiver (u i)
      ⟨w a, (fun j : Receiver a ↦ w j.val), hwu i, hrelation⟩
      (mem_filter.mpr ⟨(mem_filter.mp hi).1, hBp⟩)
  choose recv off hodd using hreceiving
  let f : Code (ι := Receiver a) (primes Y A) B := fun p ↦ (recv p, off p)
  by_cases hmoderate : ∀ j : Receiver a, groupModulus f j ≤ 6 * N * B
  · apply Or.inl
    apply (PaperP1.MultiAnchorTupleCover.mem_tupleCover t r B N Y T n).mpr
    refine ⟨A, ⟨hu, hlarge⟩, rfl, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨f, (PaperP1.ModeratePrimeAssignments.mem_moderateCodes _ _ _ f).mpr hmoderate, ?_⟩
    apply (PaperP1.ModeratePrimeAssignments.mem_receiving N N f _).mpr
    intro j
    refine ⟨by simpa only [two_mul] using hn j.val, ?_⟩
    intro p hp
    have hdvd := dvd_of_mem_oddPrimeSupport (hodd p)
    change p.val ∣ n (f p).1.val - 1 + (f p).2.val at hdvd
    simpa only [hp] using hdvd
  · push Not at hmoderate
    obtain ⟨j, hj⟩ := hmoderate
    refine Or.inr ⟨j.val, (fun heq ↦ j.property (hinj heq).symm), u, hu,
      groupModulus f j, hj, ?_, ?_⟩
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
      simpa only [hpeq, PaperP1.SaturationPrimes.value, f] using dvd_of_mem_oddPrimeSupport hmem

end PaperP1.SelectedAnchorRelation
