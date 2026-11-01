module

public import PaperP1.Arithmetic.AnchorCertificateGraph
public import PaperP1.Arithmetic.PrimeSubsetAllocations
public import PaperP1.Arithmetic.LargeSmoothCertificates

/-! # A large received prime product forces an actual short certificate edge -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReceivedPrimeCertificate

open Finset PaperP1.LinearKernelFibres PaperP1.BoundedIntegerMotifs
  PaperP1.AnchorCertificateGraph

theorem primeFactors_product_subset (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (P.prod id).primeFactors ⊆ P := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  obtain ⟨q, hq, hpq⟩ := (hpp.prime.dvd_finsetProd_iff id).mp (Nat.dvd_of_mem_primeFactors hp)
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hpp (hP q hq)).mp hpq
  exact heq ▸ hq

theorem edge_of_received_product {ρ : Type*} [Fintype ρ] [DecidableEq ρ] [Nonempty ρ]
    (X W t x : ℕ) (Y : ℝ) (c : Code W t) (z : ρ → ℕ) (P : Finset ℕ)
    (hX : 1 ≤ X) (hY : 1 < Y)
    (hP : ∀ p ∈ P, p.Prime ∧ Y < (p : ℝ))
    (hsub : P ⊆ PaperP1.RoughValuePrimePool.pool Y (anchorValue x c))
    (hreceiving : ∀ p ∈ P, ∃ j : ρ, ∃ u : offsets W, p ∣ value (z j) u.val)
    (hlarge : threshold X W ^ Fintype.card ρ < P.prod id) :
    ∃ j : ρ, Edge X W t Y x (z j) := by
  let v : ρ → ℕ := fun j ↦ ∏ u : offsets W, value (z j) u.val
  have hcover : ∀ p ∈ P, ∃ j, p ∣ v j := by
    intro p hp
    obtain ⟨j, u, hu⟩ := hreceiving p hp
    exact ⟨j, hu.trans (dvd_prod_of_mem _ (mem_univ u))⟩
  obtain ⟨G, hG, _hcop, hprod⟩ := PaperP1.PrimeSubsetAllocations.exists_coprime_allocation P v
    (fun p hp ↦ (hP p hp).1) hcover
  have hsome : ∃ j, threshold X W < G j := by
    by_contra hnot
    have hall : ∀ j, G j ≤ threshold X W := by simpa only [not_exists, not_lt] using hnot
    have hbound : ∏ j, G j ≤ threshold X W ^ Fintype.card ρ := by
      calc
        _ ≤ ∏ _j : ρ, threshold X W := prod_le_prod (fun j _ ↦ hall j)
        _ = _ := by simp only [prod_const, card_univ]
    rw [hprod] at hbound
    omega
  obtain ⟨j, hj⟩ := hsome
  have hPpos : 0 < P.prod id := prod_pos (fun p hp ↦ (hP p hp).1.pos)
  have hGdiv : G j ∣ P.prod id := by
    rw [← hprod]
    exact dvd_prod_of_mem G (mem_univ j)
  have hGsf : Squarefree (G j) := (PaperP1.LargeSmoothCertificates.prime_product_squarefree P
    (fun p hp ↦ (hP p hp).1)).squarefree_of_dvd hGdiv
  let R := (G j).primeFactors
  have hRsub : R ⊆ P :=
    (Nat.primeFactors_mono hGdiv hPpos.ne').trans (primeFactors_product_subset P (fun p hp ↦ (hP p hp).1))
  have hRprod : R.prod id = G j := Nat.prod_primeFactors_of_squarefree hGsf
  have hthreshold : (1 : ℝ) ≤ threshold X W := by
    exact_mod_cast hX.trans (threshold_ge X W)
  obtain ⟨T, hTR, hTprod, hTcard⟩ := PaperP1.ShortPrimePassage.exists_short_subset R (threshold X W) Y
    hthreshold hY (fun p hp ↦ (hP p (hRsub hp)).2.le) (by exact_mod_cast (by rwa [hRprod] : threshold X W < R.prod id))
  refine ⟨j, c, T, (hTR.trans hRsub).trans hsub, hTcard, by exact_mod_cast hTprod, ?_⟩
  intro p hp
  have hpR := hTR hp
  have hpp := Nat.prime_of_mem_primeFactors hpR
  have hdiv : p ∣ v j := (Nat.dvd_of_mem_primeFactors hpR).trans (hG j).2
  obtain ⟨u, _, hu⟩ := (hpp.prime.dvd_finsetProd_iff (fun u : offsets W ↦ value (z j) u.val)).mp hdiv
  exact ⟨u, hu⟩

end PaperP1.ReceivedPrimeCertificate
