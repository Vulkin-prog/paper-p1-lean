module

public import PaperP1.Arithmetic.ModeratePrimeAssignments
public import PaperP1.Arithmetic.KernelSupportFibres

/-! # The finite CRT cost of assigning one actual kernel to several windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeveralKernelReceivers

open Finset PaperP1.PrimeAssignments PaperP1.ModeratePrimeAssignments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hits (P : Finset ℕ) (B U N : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ : ι ↦ Finset.Ico U (U + N)).filter fun z ↦
    ∀ p ∈ P, ∃ i : ι, ∃ j : Fin B, p ∣ z i - 1 + j.val

theorem hits_cover (P : Finset ℕ) (B U N : ℕ) :
    hits (ι := ι) P B U N ⊆ (univ : Finset (Code (ι := ι) P B)).biUnion (receiving U N) := by
  intro z hz
  obtain ⟨hz, hprimes⟩ := mem_filter.mp hz
  have hzblock : ∀ i, z i ∈ Finset.Ico U (U + N) := Fintype.mem_piFinset.mp hz
  have hex (p : P) : ∃ w : ι × Fin B, p.val ∣ z w.1 - 1 + w.2.val := by
    obtain ⟨i, j, hj⟩ := hprimes p.val p.property
    exact ⟨(i, j), hj⟩
  let f : Code (ι := ι) P B := fun p ↦ Classical.choose (hex p)
  refine mem_biUnion.mpr ⟨f, mem_univ _, (mem_receiving U N f z).mpr ?_⟩
  intro i
  refine ⟨hzblock i, ?_⟩
  intro p hpi
  have h := Classical.choose_spec (hex p)
  change p.val ∣ z (f p).1 - 1 + (f p).2.val at h
  rw [hpi] at h
  exact h

theorem one_add_div_bound {N q : ℕ} (hq : 0 < q) (hbound : q ≤ 3 * N) :
    1 + (N : ℝ) / q ≤ 4 * N / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hone : (1 : ℝ) ≤ 3 * N / q := by
    apply (le_div_iff₀ hqR).mpr
    have h : (q : ℝ) ≤ 3 * N := by exact_mod_cast hbound
    simpa only [one_mul] using h
  calc
    _ ≤ 3 * N / q + (N : ℝ) / q := add_le_add hone (le_refl _)
    _ = _ := by ring

theorem receiving_card {P : Finset ℕ} {B : ℕ} (U N : ℕ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P, Nat.Prime p) (hprod : P.prod id ≤ 3 * N) (f : Code (ι := ι) P B) :
    ((receiving U N f).card : ℝ) ≤
      4 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (P.prod id : ℕ) := by
  have hp : 0 < P.prod id := prod_pos (fun p hp ↦ (hP p hp).pos)
  have hgp (i : ι) : 0 < groupModulus f i :=
    PaperP1.ModerateReceiverCost.modulus_pos (groupPrime f)
      (fun i p ↦ (groupPrime_prime hP f i p).pos) i
  have hgi (i : ι) : groupModulus f i ≤ 3 * N := by
    have hdvd : groupModulus f i ∣ ∏ j, groupModulus f j := dvd_prod_of_mem _ (mem_univ i)
    rw [product_groupModulus] at hdvd
    exact (Nat.le_of_dvd hp hdvd).trans hprod
  have hcost := PaperP1.ModerateReceiverCost.card_assignments_le_cost U N
    (groupPrime f) (groupOffset f) hU (groupPrime_pairwise_coprime hP f)
  calc
    _ ≤ ∏ i, (1 + (N : ℝ) / groupModulus f i) := hcost
    _ ≤ ∏ i, (4 * (N : ℝ) / groupModulus f i) :=
      prod_le_prod₀ (fun i _ ↦ by positivity)
        (fun i _ ↦ one_add_div_bound (hgp i) (hgi i))
    _ = _ := by
      rw [prod_div_distrib, prod_const, card_univ, mul_pow, ← Nat.cast_prod, product_groupModulus]

theorem hits_card {P : Finset ℕ} {B : ℕ} (U N : ℕ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P, Nat.Prime p) (hprod : P.prod id ≤ 3 * N) :
    ((hits (ι := ι) P B U N).card : ℝ) ≤
      ((Fintype.card ι * B : ℕ) : ℝ) ^ P.card *
        (4 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (P.prod id : ℕ)) := by
  have hnonneg : 0 ≤ (4 : ℝ) ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (P.prod id : ℕ) := by positivity
  calc
    _ ≤ (((univ : Finset (Code (ι := ι) P B)).biUnion (receiving U N)).card : ℝ) := by
      exact_mod_cast card_le_card (hits_cover (ι := ι) P B U N)
    _ ≤ ((∑ f : Code (ι := ι) P B, (receiving U N f).card : ℕ) : ℝ) := by exact_mod_cast card_biUnion_le
    _ = ∑ f : Code (ι := ι) P B, ((receiving U N f).card : ℝ) := by norm_cast
    _ ≤ ∑ _f : Code (ι := ι) P B,
        (4 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (P.prod id : ℕ)) :=
      sum_le_sum (fun f _ ↦ receiving_card U N hU hP hprod f)
    _ = _ := by simp only [sum_const, card_univ, card_codes, nsmul_eq_mul, Nat.cast_pow]

end PaperP1.SeveralKernelReceivers
