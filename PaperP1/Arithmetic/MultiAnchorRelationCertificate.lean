module

public import PaperP1.Arithmetic.MultiAnchorCertificateCount
public import PaperP1.Arithmetic.MultiAnchorSaturation
public import PaperP1.Arithmetic.ParticipatingWindowCertificates

/-! # A physical relation with t selected values gives a certificate or an actual edge -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorRelationCertificate

open Finset PaperP1.Arithmetic PaperP1.MultiAnchorValues
  PaperP1.MultiAnchorCertificateCount PaperP1.TruncatedKernelProducts PaperP1.PrimeAssignments
open PaperP1.ModerateAnchors (Receiver)
open PaperP1.ModerateCertificateCount (Unmarked)

local instance multiAnchorRelationPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem selected_offsets {B : ℕ} (t : ℕ) (w : Fin B → F₂)
    (hcard : t ≤ (PaperP1.BinaryEvenSelections.selected w).card) :
    ∃ u : Fin t → Fin B, Function.Injective u ∧ ∀ i, w (u i) ≠ 0 := by
  classical
  let S := PaperP1.BinaryEvenSelections.selected w
  have hsize : t ≤ Fintype.card S := by simpa only [Fintype.card_coe] using hcard
  let e : Fin t → S := fun i ↦ (Fintype.equivFin S).symm (Fin.castLE hsize i)
  refine ⟨fun i ↦ (e i).val, ?_, ?_⟩
  · intro i j hij
    have he : e i = e j := Subtype.ext hij
    have hfin := (Fintype.equivFin S).symm.injective he
    exact Fin.ext (congrArg (fun z : Fin (Fintype.card S) ↦ z.val) hfin)
  · intro i
    have hm := (e i).property
    simp only [S, PaperP1.BinaryEvenSelections.selected, mem_filter] at hm
    exact hm.2

theorem coordinate_alternative {t r B N : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, n i ∈ Ico N (2 * N)) (hinj : Function.Injective n)
    (Y T : ℝ) (hY : (B : ℝ) ≤ Y) (a : Fin r)
    (w : Fin r → Fin B → F₂)
    (hcard : t ≤ (PaperP1.BinaryEvenSelections.selected (w a)).card)
    (htotal : (∑ j, ∑ i, w j i • parityVec (n j - 1 + i.val)) = 0)
    (hunmarked : Unmarked B Y T (n a)) :
    HasCertificate t r B N Y T n ∨
      ∃ j : Fin r, PaperP1.MultiAnchorSaturation.Edge t B N Y (n a) (n j) := by
  classical
  obtain ⟨u, hu, hwu⟩ := selected_offsets t (w a) hcard
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
  · exact Or.inl ⟨hinj, A, rfl, hu, hunmarked, f, hmoderate, hodd⟩
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

end PaperP1.MultiAnchorRelationCertificate
