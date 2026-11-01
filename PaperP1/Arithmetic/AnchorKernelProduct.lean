module

public import PaperP1.Arithmetic.PrivateOffsetPrimeReceivers

/-! # Actual coprime anchor kernels and their received prime product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchorKernelProduct

open Finset PaperP1.Arithmetic PaperP1.LinearKernelFibres
  PaperP1.RankinSmallKernel PaperP1.TruncatedKernelProducts PaperP1.AnchorCertificateGraph

def product {W t : ℕ} (Y : ℝ) (x : ℕ) (c : Code W t) : ℕ :=
  ∏ i, truncatedKernel Y (anchorValue x c i)

def primes {W t : ℕ} (Y : ℝ) (x : ℕ) (c : Code W t) : Finset ℕ := (product Y x c).primeFactors

theorem product_squarefree {W t : ℕ} (Y : ℝ) (x : ℕ) (c : Code W t)
    (hx : W < x) (hY : (2 * W : ℝ) ≤ Y) (hinj : Function.Injective c) :
    Squarefree (product Y x c) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    have hne := PaperP1.PrivateOffsetPrimeReceivers.values_ne x W (c i).val (c j).val hx
      (offset_bound W (c i)) (offset_bound W (c j)) (fun h ↦ hij (hinj (Subtype.ext h)))
    have hdist := PaperP1.PrivateOffsetPrimeReceivers.values_dist x W (c i).val (c j).val hx
      (offset_bound W (c i)) (offset_bound W (c j))
    apply Nat.coprime_iff_isRelPrime.mp
    exact kernels_coprime Y _ _ hne ((by exact_mod_cast hdist : (Nat.dist (value x (c i).val) (value x (c j).val) : ℝ) ≤ 2 * W).trans hY)
  · intro i _
    exact kernel_squarefree Y _

theorem primes_product {W t : ℕ} (Y : ℝ) (x : ℕ) (c : Code W t)
    (hx : W < x) (hY : (2 * W : ℝ) ≤ Y) (hinj : Function.Injective c) :
    (primes Y x c).prod id = product Y x c :=
  Nat.prod_primeFactors_of_squarefree (product_squarefree Y x c hx hY hinj)

theorem prime_data {W t : ℕ} (Y : ℝ) (x : ℕ) (c : Code W t) (p : ℕ) (hp : p ∈ primes Y x c) :
    p.Prime ∧ Y < (p : ℝ) ∧ ∃ i : Fin t, p ∈ support Y (anchorValue x c i) := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdiv := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨i, _, hi⟩ := (hpp.prime.dvd_finsetProd_iff (fun i ↦ truncatedKernel Y (anchorValue x c i))).mp hdiv
  have hs := (prime_dvd_kernel_iff Y _ p hpp).mp hi
  exact ⟨hpp, (mem_filter.mp hs).2, i, hs⟩

theorem primes_subset_pool {W t : ℕ} (Y : ℝ) (x : ℕ) (c : Code W t) :
    primes Y x c ⊆ PaperP1.RoughValuePrimePool.pool Y (anchorValue x c) := by
  intro p hp
  obtain ⟨hpp, hpY, i, hi⟩ := prime_data Y x c p hp
  have hpFactors : p ∈ (anchorValue x c i).primeFactors :=
    Finsupp.support_mapRange (mem_filter.mp hi).1
  exact mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr
    ⟨hpFactors, hpY⟩⟩

theorem product_lower {W t : ℕ} (Y : ℝ) (x : ℕ) (c : Code W t) (N b : ℝ)
    (hN : 0 < N) (ht : 1 ≤ t)
    (hlarge : ∀ i, N ^ b < (truncatedKernel Y (anchorValue x c i) : ℝ)) :
    N ^ (b * (t : ℝ)) < (product Y x c : ℕ) := by
  let _ : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
  have hp := prod_lt_prod_of_nonempty₀ (s := (univ : Finset (Fin t)))
    (fun _ _ ↦ Real.rpow_pos_of_pos hN b) (fun i _ ↦ hlarge i) univ_nonempty
  have heq : (N ^ b) ^ t = N ^ (b * (t : ℝ)) := (Real.rpow_mul_natCast hN.le b t).symm
  simpa only [prod_const, card_univ, Fintype.card_fin, heq, product, Nat.cast_prod] using hp

theorem edge_of_selected_anchors {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (X W t x : ℕ) (Y N b : ℝ) (c : Code W t) (z : ρ → ℕ)
    (S : Finset ℤ) (T : ρ → Finset ℤ) (hX : 1 ≤ X) (ht : 1 ≤ t)
    (hx : W < x) (hN : 0 < N) (hYone : 1 < Y) (hY : (2 * W : ℝ) ≤ Y)
    (hinj : Function.Injective c) (hsource : ∀ i, (c i).val ∈ S)
    (hS : ∀ u ∈ S, u.natAbs ≤ W) (hT : ∀ j, ∀ v ∈ T j, v.natAbs ≤ W)
    (hlarge : ∀ i, N ^ b < (truncatedKernel Y (anchorValue x c i) : ℝ))
    (hthreshold : (threshold X W : ℝ) ^ Fintype.card ρ ≤ N ^ (b * (t : ℝ)))
    (hrelation : (∑ u ∈ S, parityVec (value x u)) + (∑ j, ∑ v ∈ T j, parityVec (value (z j) v)) = 0) :
    ∃ j : ρ, Edge X W t Y x (z j) := by
  classical
  let P := primes Y x c
  have hPdata : ∀ p ∈ P, p.Prime ∧ Y < (p : ℝ) := fun p hp ↦
    ⟨(prime_data Y x c p hp).1, (prime_data Y x c p hp).2.1⟩
  have hPprod : P.prod id = product Y x c := primes_product Y x c hx hY hinj
  have hbig : threshold X W ^ Fintype.card ρ < P.prod id := by
    have hb := hthreshold.trans_lt (product_lower Y x c N b hN ht hlarge)
    rw [← hPprod] at hb
    exact_mod_cast hb
  have hreceiving : ∀ p ∈ P, ∃ j : ρ, ∃ u : PaperP1.BoundedIntegerMotifs.offsets W, p ∣ value (z j) u.val := by
    intro p hp
    obtain ⟨_, _, i, hi⟩ := prime_data Y x c p hp
    obtain ⟨j, v, hv, hd⟩ := PaperP1.PrivateOffsetPrimeReceivers.other_receiver x W z S T (c i).val Y p
      hx hS (hsource i) hY hi hrelation
    have hvpool : v ∈ PaperP1.BoundedIntegerMotifs.offsets W :=
      (PaperP1.BoundedIntegerMotifs.subset_offsets W {v}).mpr (by
        intro u hu; rw [mem_singleton.mp hu]; exact hT j v hv) (mem_singleton_self _)
    exact ⟨j, ⟨v, hvpool⟩, hd⟩
  have hPne : P.Nonempty := by
    by_contra hnot
    rw [not_nonempty_iff_eq_empty.mp hnot, prod_empty] at hbig
    have hpow : 1 ≤ threshold X W ^ Fintype.card ρ :=
      one_le_pow₀ (hX.trans (threshold_ge X W))
    omega
  obtain ⟨p, hp⟩ := hPne
  obtain ⟨j, _, _⟩ := hreceiving p hp
  let _ : Nonempty ρ := ⟨j⟩
  exact PaperP1.ReceivedPrimeCertificate.edge_of_received_product X W t x Y c z P hX hYone
    hPdata (primes_subset_pool Y x c) hreceiving hbig

end PaperP1.AnchorKernelProduct
