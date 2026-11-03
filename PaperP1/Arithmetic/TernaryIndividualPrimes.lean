module

public import PaperP1.Arithmetic.TernaryTopProducts
public import PaperP1.Arithmetic.TernaryGroupDeterminants

/-! # Individual ternary primes, including repeated offset supports

A selected prime product divides the product of its actual support groups.
Consequently three primes with a large product must use three distinct
supports: one or two supports are already covered by the proved group budget.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryIndividualPrimes

open Finset PaperP1.TernaryPrimeGroups PaperP1.TernaryTopProducts PaperP1.FiniteEvenSquareClasses

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def pool (U : Fin 3 → Finset ℕ) (H : ℕ) : Finset ℕ := (supportPool U).biUnion (primes H)

theorem mem_pool (U : Fin 3 → Finset ℕ) (H p : ℕ) :
    p ∈ pool U H ↔ ∃ u ∈ supportPool U, p ∈ primes H u := mem_biUnion

theorem prime_of_mem {U : Fin 3 → Finset ℕ} {H p : ℕ} (hp : p ∈ pool U H) : Nat.Prime p := by
  obtain ⟨u, _hu, hpu⟩ := mem_biUnion.mp hp
  exact TernaryPrimeGroups.prime_of_mem hpu

theorem supporting_active {U : Fin 3 → Finset ℕ} {H p : ℕ} {u : Fin 3 → ℕ}
    (hu : u ∈ supportPool U) (hp : p ∈ primes H u) : u ∈ active U H := by
  have hpprime := TernaryPrimeGroups.prime_of_mem hp
  have hgroup : p ≤ group H u := Nat.le_of_dvd (group_pos H u) (prime_dvd_group hp)
  exact mem_filter.mpr ⟨hu, hpprime.one_lt.trans_le hgroup⟩

theorem covered_product_le (H : ℕ) (P : Finset ℕ) (S : Finset (Fin 3 → ℕ))
    (hP : ∀ p ∈ P, Nat.Prime p) (hcover : ∀ p ∈ P, ∃ u ∈ S, p ∈ primes H u) :
    P.prod id ≤ ∏ u ∈ S, group H u := by
  apply Nat.le_of_dvd (prod_pos (fun u _ ↦ group_pos H u))
  apply prod_primes_dvd
  · intro p hp
    exact (hP p hp).prime
  · intro p hp
    obtain ⟨u, hu, hpu⟩ := hcover p hp
    exact (prime_dvd_group hpu).trans (dvd_prod_of_mem (group H) hu)

theorem small_support_product_bound {U : Fin 3 → Finset ℕ} {A H : ℕ} (hA : 1 ≤ A)
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hpos : ∀ i, ∀ n ∈ U i, 0 < n) (hmax : ∀ i, ∀ n ∈ U i, n ≤ A)
    (hinj : ∀ i, Function.Injective (data (U i)))
    (hdirect : Pairwise (fun i j ↦ Disjoint (space (U i)) (space (U j))))
    (S : Finset (Fin 3 → ℕ)) (hS : S ⊆ active U H) (hcard : S.card ≤ 2) :
    (∏ u ∈ S, group H u) ≤ 2 * A * (H + 1) := by
  classical
  by_cases hz : S.card = 0
  · rw [card_eq_zero.mp hz, prod_empty]
    nlinarith
  by_cases ho : S.card = 1
  · obtain ⟨u, rfl⟩ := card_eq_one.mp ho
    have hum := ((mem_active U H u).mp (hS (mem_singleton_self u))).1
    have hle := (Nat.le_of_dvd (hpos 0 (u 0) (hum 0)) (group_dvd_value H u 0)).trans (hmax 0 (u 0) (hum 0))
    simp only [prod_singleton]
    nlinarith
  · have ht : S.card = 2 := by omega
    obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp ht
    have hu := (mem_filter.mp (hS (mem_insert_self u {v}))).1
    have hv := (mem_filter.mp (hS (mem_insert_of_mem (mem_singleton_self v)))).1
    rw [prod_pair huv]
    exact TernaryGroupDeterminants.group_product_le hwidth hpos hmax hinj hdirect hu hv huv

theorem three_primes_le_top_groups {U : Fin 3 → Finset ℕ} {A H : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hpos : ∀ i, ∀ n ∈ U i, 0 < n) (hmax : ∀ i, ∀ n ∈ U i, n ≤ A)
    (hinj : ∀ i, Function.Injective (data (U i)))
    (hdirect : Pairwise (fun i j ↦ Disjoint (space (U i)) (space (U j))))
    (P : Finset ℕ) (hP : P ⊆ pool U H) (hcard : P.card = 3)
    (hlarge : 2 * A * (H + 1) < P.prod id) : P.prod id ≤ topProduct U H 3 := by
  classical
  have hdata : ∀ p : P, ∃ u ∈ supportPool U, p.val ∈ primes H u := by
    intro p
    exact mem_biUnion.mp (hP p.property)
  choose u hu hpu using hdata
  let S : Finset (Fin 3 → ℕ) := P.attach.image u
  have hS : S ⊆ active U H := by
    intro v hv
    obtain ⟨p, _, rfl⟩ := mem_image.mp hv
    exact supporting_active (hu p) (hpu p)
  have hcover : ∀ p ∈ P, ∃ v ∈ S, p ∈ primes H v := by
    intro p hp
    exact ⟨u ⟨p, hp⟩, mem_image.mpr ⟨⟨p, hp⟩, mem_attach _ _, rfl⟩, hpu ⟨p, hp⟩⟩
  have hQ := covered_product_le H P S (fun p hp ↦ prime_of_mem (hP hp)) hcover
  have hScard : S.card ≤ 3 := by
    have h : S.card ≤ P.attach.card := card_image_le
    simpa only [card_attach, hcard] using h
  have hA : 1 ≤ A := by
    obtain ⟨p, hp⟩ : P.Nonempty := card_pos.mp (by omega)
    have hum := (mem_supportPool U (u ⟨p, hp⟩)).mp (hu ⟨p, hp⟩)
    have hl := (hpos 0 _ (hum 0)).trans_le (hmax 0 _ (hum 0))
    omega
  have hthree : S.card = 3 := by
    by_contra hnot
    have htwo : S.card ≤ 2 := by omega
    exact (not_lt_of_ge (hQ.trans (small_support_product_bound hA hwidth hpos hmax hinj hdirect S hS htwo))) hlarge
  exact hQ.trans (selected_le_top U H 3 S hS hthree)

end PaperP1.TernaryIndividualPrimes
