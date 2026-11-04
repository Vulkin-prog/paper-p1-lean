module

public import PaperP1.Arithmetic.PrefixModerateTupleCover
public import PaperP1.Arithmetic.UniformFixedSourceCertificates
public import PaperP1.Analysis.ElementaryLogGrowth

/-! # The literal finite moderate-certificate bound, uniform in the order -/

/-! The centre range in this module is the positive prefix [2,N+2),
with exactly N centres; no critical lower bound on a centre is assumed. -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrefixModerateCertificateCount

open Finset PaperP1.PrefixModerateAnchors PaperP1.PrefixModerateTupleCover PaperP1.DefectivePredicate

def Unmarked (B : ℕ) (Y T : ℝ) (c : ℕ) : Prop :=
  ∀ u : Fin B, T < (PaperP1.RankinSmallKernel.truncatedKernel Y (c - 1 + u.val) : ℝ)

def HasCertificate (r B N : ℕ) (Y T : ℝ) (z : Fin r → ℕ) : Prop :=
  Function.Injective z ∧ ∃ A : Anchor r B N,
    z A.1 = A.2.1.val ∧ A.2.2.1 ≠ A.2.2.2 ∧ Unmarked B Y T A.2.1.val ∧
    ∃ f : PaperP1.PrimeAssignments.Code (ι := Receiver A.1) (primes Y A) B,
      (∀ j, PaperP1.PrimeAssignments.groupModulus f j ≤ 6 * N * B) ∧
      ∀ p : primes Y A, p.val ∈ oddPrimeSupport
        (z (f p).1.val - 1 + (f p).2.val)

def sourceTuples (r B N : ℕ) (Y T : ℝ) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ Finset.Ico 2 (N + 2)).filter (HasCertificate r B N Y T)

theorem mem_sourceTuples (r B N : ℕ) (Y T : ℝ) (z : Fin r → ℕ) :
    z ∈ sourceTuples r B N Y T ↔ (∀ i, z i ∈ Finset.Ico 2 (N + 2)) ∧ HasCertificate r B N Y T z := by
  classical
  simp only [sourceTuples, mem_filter, Fintype.mem_piFinset]

theorem sourceTuples_subset_cover (r B N : ℕ) (Y T : ℝ) :
    sourceTuples r B N Y T ⊆ tupleCover r B N Y T := by
  intro z hz
  obtain ⟨hwindows, _, A, ha, huv, hunmarked, f, hmoderate, hodd⟩ := (mem_sourceTuples r B N Y T z).mp hz
  have hgood : Good Y T A := ⟨huv, hunmarked A.2.2.1, hunmarked A.2.2.2⟩
  have hreceiving : (fun j : Receiver A.1 ↦ z j.val) ∈
      PaperP1.ModeratePrimeAssignments.receiving 2 N f := by
    apply (PaperP1.ModeratePrimeAssignments.mem_receiving 2 N f _).mpr
    intro j
    refine ⟨by simpa only [Nat.add_comm] using hwindows j.val, ?_⟩
    intro p hp
    have hdvd := PaperP1.TruncatedKernelProducts.dvd_of_mem_oddPrimeSupport (hodd p)
    simpa only [hp] using hdvd
  have hcovered : (fun j : Receiver A.1 ↦ z j.val) ∈
      PaperP1.ModeratePrimeAssignments.covered (primes Y A) B 2 N :=
    mem_biUnion.mpr ⟨f, (PaperP1.ModeratePrimeAssignments.mem_moderateCodes _ _ _ f).mpr hmoderate, hreceiving⟩
  exact (mem_tupleCover r B N Y T z).mpr ⟨A, hgood, ha, hcovered⟩

theorem sourceTuples_zero (B N : ℕ) (Y T : ℝ) : sourceTuples 0 B N Y T = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨_, _, A, _⟩ := (mem_sourceTuples 0 B N Y T z).mp hz
  exact Fin.elim0 A.1

theorem sourceTuples_empty_of_lt (r B N : ℕ) (Y T : ℝ) (hNr : N < r) :
    sourceTuples r B N Y T = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hwindows, hcert⟩ := (mem_sourceTuples r B N Y T z).mp hz
  let f : Fin r → Finset.Ico 2 (N + 2) := fun i ↦ ⟨z i, hwindows i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    exact hcert.1 (congrArg Subtype.val hij)
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_coe, Nat.card_Ico, Nat.add_sub_cancel] at hcard
  omega

theorem main_7_2_finite (r B N : ℕ) (hr : 1 ≤ r) (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y T : ℝ) (hY : (B : ℝ) ≤ Y) (hT : 1 ≤ T) :
    ((sourceTuples r B N Y T).card : ℝ) ≤
      36 * (r : ℝ) * (B : ℝ) ^ 4 * 2 ^ (r - 1) * (N : ℝ) ^ r / T ^ 2 *
        (↑(r * B) : ℝ) ^ PaperP1.PrimeProductBudget.assignmentExponent N Y := by
  have hsub : ((sourceTuples r B N Y T).card : ℝ) ≤ (tupleCover r B N Y T).card := by
    exact_mod_cast card_le_card (sourceTuples_subset_cover r B N Y T)
  exact hsub.trans (card_tupleCover_le r B N hr hN hB hBN Y T hY hT)


end PaperP1.PrefixModerateCertificateCount
