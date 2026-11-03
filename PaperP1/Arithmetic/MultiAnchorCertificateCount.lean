module

public import PaperP1.Arithmetic.MultiAnchorTupleCover
public import PaperP1.Arithmetic.ModerateCertificateCount

/-! # Literal t-anchor moderate certificates, uniformly in the family order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorCertificateCount

open Finset PaperP1.MultiAnchorValues PaperP1.MultiAnchorTupleCover
open PaperP1.ModerateAnchors (Receiver)
open PaperP1.ModerateCertificateCount (Unmarked)

def HasCertificate (t r B N : ℕ) (Y T : ℝ) (z : Fin r → ℕ) : Prop :=
  Function.Injective z ∧ ∃ A : Anchor t r B N,
    z A.1 = A.2.1.val ∧ Function.Injective A.2.2 ∧ Unmarked B Y T A.2.1.val ∧
    ∃ f : PaperP1.PrimeAssignments.Code (ι := Receiver A.1) (primes Y A) B,
      (∀ j, PaperP1.PrimeAssignments.groupModulus f j ≤ 6 * N * B) ∧
      ∀ p : primes Y A, p.val ∈ PaperP1.DefectivePredicate.oddPrimeSupport
        (z (f p).1.val - 1 + (f p).2.val)

def sourceTuples (t r B N : ℕ) (Y T : ℝ) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ Ico N (2 * N)).filter (HasCertificate t r B N Y T)

theorem mem_sourceTuples (t r B N : ℕ) (Y T : ℝ) (z : Fin r → ℕ) :
    z ∈ sourceTuples t r B N Y T ↔
      (∀ i, z i ∈ Ico N (2 * N)) ∧ HasCertificate t r B N Y T z := by
  classical
  simp only [sourceTuples, mem_filter, Fintype.mem_piFinset]

theorem sourceTuples_subset_cover (t r B N : ℕ) (Y T : ℝ) :
    sourceTuples t r B N Y T ⊆ tupleCover t r B N Y T := by
  intro z hz
  obtain ⟨hwindows, _, A, ha, hinj, hunmarked, f, hmoderate, hodd⟩ :=
    (mem_sourceTuples t r B N Y T z).mp hz
  have hgood : Good Y T A := ⟨hinj, fun i ↦ hunmarked (A.2.2 i)⟩
  have hreceiving : (fun j : Receiver A.1 ↦ z j.val) ∈
      PaperP1.ModeratePrimeAssignments.receiving N N f := by
    apply (PaperP1.ModeratePrimeAssignments.mem_receiving N N f _).mpr
    intro j
    refine ⟨by simpa only [two_mul] using hwindows j.val, ?_⟩
    intro p hp
    have hdvd := PaperP1.TruncatedKernelProducts.dvd_of_mem_oddPrimeSupport (hodd p)
    simpa only [hp] using hdvd
  have hcovered : (fun j : Receiver A.1 ↦ z j.val) ∈
      PaperP1.ModeratePrimeAssignments.covered (primes Y A) B N N :=
    mem_biUnion.mpr ⟨f,
      (PaperP1.ModeratePrimeAssignments.mem_moderateCodes _ _ _ f).mpr hmoderate, hreceiving⟩
  exact (mem_tupleCover t r B N Y T z).mpr ⟨A, hgood, ha, hcovered⟩

theorem sourceTuples_zero (t B N : ℕ) (Y T : ℝ) : sourceTuples t 0 B N Y T = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨_, _, A, _⟩ := (mem_sourceTuples t 0 B N Y T z).mp hz
  exact Fin.elim0 A.1

theorem sourceTuples_empty_of_lt (t r B N : ℕ) (Y T : ℝ) (hNr : N < r) :
    sourceTuples t r B N Y T = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hwindows, hcert⟩ := (mem_sourceTuples t r B N Y T z).mp hz
  let f : Fin r → Ico N (2 * N) := fun i ↦ ⟨z i, hwindows i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    exact hcert.1 (congrArg Subtype.val hij)
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_coe, Nat.card_Ico, two_mul,
    Nat.add_sub_cancel_left] at hcard
  omega

theorem finite_bound (t r B N : ℕ) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (hN : 3 ^ t < N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y T : ℝ) (hY : (B : ℝ) ≤ Y) (hT : 1 ≤ T) :
    ((sourceTuples t r B N Y T).card : ℝ) ≤
      (6 : ℝ) ^ t * r * (B : ℝ) ^ (2 * t) * 2 ^ (r - 1) * (N : ℝ) ^ r / T ^ t *
        (↑(r * B) : ℝ) ^ PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y := by
  have hsub : ((sourceTuples t r B N Y T).card : ℝ) ≤ (tupleCover t r B N Y T).card := by
    exact_mod_cast card_le_card (sourceTuples_subset_cover t r B N Y T)
  exact hsub.trans (card_tupleCover_le t r B N ht hr hN hB hBN Y T hY hT)

end PaperP1.MultiAnchorCertificateCount
