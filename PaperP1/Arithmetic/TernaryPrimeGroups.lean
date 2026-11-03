module

public import PaperP1.Arithmetic.AssignedPrimeGroups
public import PaperP1.Arithmetic.LargeOddKernel

/-! # Actual odd-prime groups on three arbitrary finite arithmetic sets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPrimeGroups

open Finset PaperP1.Arithmetic PaperP1.DefectivePredicate PaperP1.LargeOddKernel

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def supportPool (U : Fin 3 → Finset ℕ) : Finset (Fin 3 → ℕ) :=
  ((U 0 ×ˢ U 1) ×ˢ U 2).image fun t ↦ ![t.1.1, t.1.2, t.2]

def primes (H : ℕ) (u : Fin 3 → ℕ) : Finset ℕ :=
  (oddPrimeSupport (u 0)).filter fun p ↦ H < p ∧ p ∈ oddPrimeSupport (u 1) ∧ p ∈ oddPrimeSupport (u 2)

def group (H : ℕ) (u : Fin 3 → ℕ) : ℕ := (primes H u).prod id

def active (U : Fin 3 → Finset ℕ) (H : ℕ) : Finset (Fin 3 → ℕ) :=
  (supportPool U).filter fun u ↦ 1 < group H u

theorem mem_supportPool (U : Fin 3 → Finset ℕ) (u : Fin 3 → ℕ) :
    u ∈ supportPool U ↔ ∀ i, u i ∈ U i := by
  rw [supportPool, mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    obtain ⟨h01, h2⟩ := mem_product.mp ht
    obtain ⟨h0, h1⟩ := mem_product.mp h01
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro hu
    refine ⟨((u 0, u 1), u 2), mem_product.mpr ⟨mem_product.mpr ⟨hu 0, hu 1⟩, hu 2⟩, ?_⟩
    funext i
    fin_cases i <;> rfl

theorem supportPool_card (U : Fin 3 → Finset ℕ) :
    (supportPool U).card = (U 0).card * (U 1).card * (U 2).card := by
  have hinj : Function.Injective (fun t : (ℕ × ℕ) × ℕ ↦ (![t.1.1, t.1.2, t.2] : Fin 3 → ℕ)) := by
    intro t s heq
    apply Prod.ext
    · apply Prod.ext
      · exact congrFun heq 0
      · exact congrFun heq 1
    · exact congrFun heq 2
  rw [supportPool, card_image_of_injective _ hinj, card_product, card_product]

theorem mem_primes (H : ℕ) (u : Fin 3 → ℕ) (p : ℕ) :
    p ∈ primes H u ↔ H < p ∧ ∀ i, p ∈ oddPrimeSupport (u i) := by
  constructor
  · intro hp
    obtain ⟨h0, hH, h1, h2⟩ := mem_filter.mp hp
    refine ⟨hH, ?_⟩
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · rintro ⟨hH, hp⟩
    exact mem_filter.mpr ⟨hp 0, hH, hp 1, hp 2⟩

theorem prime_of_mem {H p : ℕ} {u : Fin 3 → ℕ} (hp : p ∈ primes H u) : Nat.Prime p :=
  prime_of_mem_oddPrimeSupport (((mem_primes H u p).mp hp).2 0)

theorem prime_dvd_value {H p : ℕ} {u : Fin 3 → ℕ} (hp : p ∈ primes H u) (i : Fin 3) : p ∣ u i := by
  have hs := ((mem_primes H u p).mp hp).2 i
  exact Nat.dvd_of_mem_primeFactors (Finsupp.support_mapRange hs)

theorem group_pos (H : ℕ) (u : Fin 3 → ℕ) : 0 < group H u :=
  prod_pos fun _ hp ↦ (prime_of_mem hp).pos

theorem prime_dvd_group {H p : ℕ} {u : Fin 3 → ℕ} (hp : p ∈ primes H u) : p ∣ group H u :=
  dvd_prod_of_mem id hp

theorem group_dvd_value (H : ℕ) (u : Fin 3 → ℕ) (i : Fin 3) : group H u ∣ u i := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (prime_of_mem hp).prime
  · intro p hp
    exact prime_dvd_value hp i

theorem group_squarefree (H : ℕ) (u : Fin 3 → ℕ) : Squarefree (group H u) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (prime_of_mem hp) (prime_of_mem hq)).mpr hpq)
  · intro p hp
    exact (prime_of_mem hp).squarefree

theorem eq_of_shared_prime {U : Fin 3 → Finset ℕ} {H p : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    {u v : Fin 3 → ℕ} (hu : u ∈ supportPool U) (hv : v ∈ supportPool U)
    (hpu : p ∈ primes H u) (hpv : p ∈ primes H v) : u = v := by
  funext i
  have hpH := ((mem_primes H u p).mp hpu).1
  have hdiv : (p : ℤ) ∣ (u i : ℤ) - v i := dvd_sub
    (Int.natCast_dvd_natCast.mpr (prime_dvd_value hpu i))
    (Int.natCast_dvd_natCast.mpr (prime_dvd_value hpv i))
  have hdivNat : p ∣ ((u i : ℤ) - v i).natAbs := Int.natCast_dvd.mp hdiv
  have hbound := hwidth i (u i) ((mem_supportPool U u).mp hu i) (v i) ((mem_supportPool U v).mp hv i)
  have hz : (u i : ℤ) - v i = 0 := by
    by_contra hne
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hdivNat
    omega
  exact_mod_cast sub_eq_zero.mp hz

theorem primes_disjoint {U : Fin 3 → Finset ℕ} {H : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    {u v : Fin 3 → ℕ} (hu : u ∈ supportPool U) (hv : v ∈ supportPool U) (huv : u ≠ v) :
    Disjoint (primes H u) (primes H v) := by
  apply disjoint_left.mpr
  intro p hpu hpv
  exact huv (eq_of_shared_prime hwidth hu hv hpu hpv)

theorem group_coprime {U : Fin 3 → Finset ℕ} {H : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    {u v : Fin 3 → ℕ} (hu : u ∈ supportPool U) (hv : v ∈ supportPool U) (huv : u ≠ v) :
    Nat.Coprime (group H u) (group H v) := by
  have hdis := primes_disjoint hwidth hu hv huv
  unfold group
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  rw [Nat.coprime_prod_right_iff]
  intro q hq
  apply (Nat.coprime_primes (prime_of_mem hp) (prime_of_mem hq)).mpr
  intro hpq
  subst q
  exact disjoint_left.mp hdis hp hq

theorem mem_active (U : Fin 3 → Finset ℕ) (H : ℕ) (u : Fin 3 → ℕ) :
    u ∈ active U H ↔ (∀ i, u i ∈ U i) ∧ 1 < group H u := by
  simp only [active, mem_filter, mem_supportPool]

theorem active_values_injective {U : Fin 3 → Finset ℕ} {H : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H) :
    Set.InjOn (group H) (active U H) := by
  intro u hu v hv heq
  by_contra huv
  have hc := group_coprime hwidth (mem_filter.mp hu).1 (mem_filter.mp hv).1 huv
  rw [heq] at hc
  have hone : group H v = 1 := by simpa only [Nat.Coprime, Nat.gcd_self] using hc
  have hgt := (mem_filter.mp hv).2
  omega

end PaperP1.TernaryPrimeGroups
