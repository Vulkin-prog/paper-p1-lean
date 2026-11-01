module

public import PaperP1.Arithmetic.GcdLcmProductBound
public import PaperP1.Arithmetic.PrimeSubsetAllocations
public import PaperP1.Arithmetic.KernelSquareBudget
public import PaperP1.Arithmetic.SmoothModulusHosts

/-! # Constructing a large squarefree smooth modulus from nearby large parts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeSmoothCertificates

open Finset PaperP1.SmallPrimeBudget PaperP1.LinearKernelFibres
  PaperP1.LargeOddKernel PaperP1.SmoothModulusHosts

theorem small_part_dvd (Y n : ℕ) (hn : 0 < n) : smallOddPart Y n ∣ n := by
  refine ⟨largeOddKernel Y n * PaperP1.DefectivePredicate.canonicalSquarePart n ^ 2, ?_⟩
  rw [← mul_assoc, small_mul_large, squarefreeKernel_mul_squarePart hn.ne']

theorem gcd_parts_le (Y n W : ℕ) (a b : ℤ) (hn : W < n)
    (ha : a.natAbs ≤ W) (hb : b.natAbs ≤ W) (hab : a ≠ b) :
    Nat.gcd (smallOddPart Y (value n a)) (smallOddPart Y (value n b)) ≤ 2 * W := by
  have hva := value_cast n W a hn ha
  have hvb := value_cast n W b hn hb
  have hapos : 0 < value n a := by
    have haa : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ha
    have hal := (abs_le.mp haa).1
    have hnZ : (W : ℤ) < n := by exact_mod_cast hn
    omega
  have hbpos : 0 < value n b := by
    have hbb : |b| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hb
    have hbl := (abs_le.mp hbb).1
    have hnZ : (W : ℤ) < n := by exact_mod_cast hn
    omega
  have hne : value n a ≠ value n b := by
    intro heq
    have hcast := congrArg (fun x : ℕ ↦ (x : ℤ)) heq
    rw [hva, hvb] at hcast
    exact hab (by omega)
  have hdiva : Nat.gcd (smallOddPart Y (value n a)) (smallOddPart Y (value n b)) ∣ value n a :=
    (Nat.gcd_dvd_left _ _).trans (small_part_dvd Y _ hapos)
  have hdivb : Nat.gcd (smallOddPart Y (value n a)) (smallOddPart Y (value n b)) ∣ value n b :=
    (Nat.gcd_dvd_right _ _).trans (small_part_dvd Y _ hbpos)
  have hdist : Nat.dist (value n a) (value n b) ≤ 2 * W := by
    have haa : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ha
    have hbb : |b| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hb
    have hal := abs_le.mp haa
    have hbl := abs_le.mp hbb
    rcases le_total (value n a) (value n b) with h | h
    · rw [Nat.dist_eq_sub_of_le h]; omega
    · rw [Nat.dist_eq_sub_of_le_right h]; omega
  apply (Nat.le_of_dvd (Nat.dist_pos_of_ne hne) ?_).trans hdist
  rcases le_total (value n a) (value n b) with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    exact Nat.dvd_sub hdivb hdiva
  · rw [Nat.dist_eq_sub_of_le_right h]
    exact Nat.dvd_sub hdiva hdivb

theorem prime_product_kernel_one (P : Finset ℕ) (Y : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Y) : largeOddKernel Y (P.prod id) = 1 := by
  apply (largeOddKernel_eq_one_iff Y _).mpr
  intro p hp hYp
  by_contra hparity
  have hs := mem_oddPrimeSupport_iff_parityVec_ne_zero.mpr hparity
  have hd := PaperP1.TruncatedKernelProducts.dvd_of_mem_oddPrimeSupport hs
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hP q hq).1).mp hpq
  exact (not_le_of_gt hYp) (heq ▸ (hP q hq).2)

theorem prime_product_squarefree (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : Squarefree (P.prod id) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)
  · intro p hp
    exact (hP p hp).squarefree

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_certificate (Y n W : ℕ) (a : ι → ℤ) (X : ℝ)
    (hW : 0 < W) (hn : W < n) (ha : ∀ i, (a i).natAbs ≤ W)
    (hinj : Function.Injective a) (hX : 1 ≤ X)
    (hlarge : X * (2 * W : ℝ) ^ (Fintype.card ι ^ 2) <
      ∏ i, (smallOddPart Y (value n (a i)) : ℝ)) :
    ∃ m : ℕ, X < m ∧ (m : ℝ) ≤ X * Y ∧ Squarefree m ∧ largeOddKernel Y m = 1 ∧
      HasCertificate (ι := ι) m W n := by
  let f : ι → ℕ := fun i ↦ smallOddPart Y (value n (a i))
  let P := univ.biUnion fun i : ι ↦ smallOddSupport Y (value n (a i))
  have hf : ∀ i, 0 < f i := fun i ↦ smallOddPart_pos _ _
  have hP : ∀ p ∈ P, p.Prime ∧ p ≤ Y := by
    intro p hp
    obtain ⟨i, _, hpi⟩ := mem_biUnion.mp hp
    exact PaperP1.DefectCounting.mem_smallPrimesUpTo.mp (smallOddSupport_subset _ _ hpi)
  have hprodpos : 0 < P.prod id := prod_pos (fun p hp ↦ (hP p hp).1.pos)
  have hflcm := PaperP1.GcdLcmProductBound.product_le_lcm_mul_bound univ f (2 * W) (by omega)
    (fun i _ ↦ hf i) (by
      intro i _ j _ hij
      exact gcd_parts_le Y n W (a i) (a j) hn (ha i) (ha j) (fun h ↦ hij (hinj h)))
  have hdiv : univ.lcm f ∣ P.prod id := by
    apply Finset.lcm_dvd
    intro i _
    apply prod_dvd_prod_of_subset _ _ id
    intro p hp
    exact mem_biUnion.mpr ⟨i, mem_univ i, hp⟩
  have hle : univ.lcm f ≤ P.prod id := Nat.le_of_dvd hprodpos hdiv
  have hbound : (∏ i, (f i : ℝ)) ≤ (P.prod id : ℕ) * (2 * W : ℝ) ^ (Fintype.card ι ^ 2) := by
    have hcast : (∏ i, (f i : ℝ)) ≤ (univ.lcm f : ℕ) * (2 * W : ℝ) ^ (Fintype.card ι ^ 2) := by
      exact_mod_cast (by simpa only [card_univ] using hflcm)
    exact hcast.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (by positivity))
  have hbig : X < (P.prod id : ℕ) := by
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) (by positivity : (0 : ℝ) ≤ (2 * W : ℝ) ^ (Fintype.card ι ^ 2))
    exact (not_lt_of_ge (hbound.trans hmul)) hlarge
  obtain ⟨T, hTP, hlo, hhi⟩ := PaperP1.PrimeSubsetAllocations.first_passage P X Y hX
    (fun p hp ↦ ⟨(hP p hp).1.one_lt.le, by exact_mod_cast (hP p hp).2⟩) hbig
  obtain ⟨G, hG, hcop, hprod⟩ := PaperP1.PrimeSubsetAllocations.exists_coprime_allocation T
    (fun i ↦ value n (a i)) (fun p hp ↦ (hP p (hTP hp)).1) (by
      intro p hp
      obtain ⟨i, _, hpi⟩ := mem_biUnion.mp (hTP hp)
      exact ⟨i, PaperP1.TruncatedKernelProducts.dvd_of_mem_oddPrimeSupport (mem_filter.mp hpi).1⟩)
  exact ⟨T.prod id, hlo, hhi, prime_product_squarefree T (fun p hp ↦ (hP p (hTP hp)).1),
    prime_product_kernel_one T Y (fun p hp ↦ hP p (hTP hp)),
    a, ha, G, hcop, hprod, fun i ↦ (hG i).2⟩

end PaperP1.LargeSmoothCertificates
