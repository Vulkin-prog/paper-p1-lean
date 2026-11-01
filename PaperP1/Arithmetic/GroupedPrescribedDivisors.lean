module

public import PaperP1.Arithmetic.GroupedKernelResultants
public import PaperP1.Arithmetic.SquarefreeOutsideDivisor

/-! # Actual allocation of a prescribed divisor away from the difference resultant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GroupedPrescribedDivisors

open Finset PaperP1.SplitOffsetProducts PaperP1.GroupedKernelResultants
open PaperP1.SplitOffsetSupports PaperP1.SquarefreeOutsideDivisor

def assignedSupport (e n : ℕ) (B : Finset ℤ) : Finset ℕ := e.primeFactors.filter fun p ↦ p ∣ kernel B n
def assigned (e n : ℕ) (B : Finset ℤ) : ℕ := (assignedSupport e n B).prod id

theorem assigned_pos (e n : ℕ) (B : Finset ℤ) : 0 < assigned e n B :=
  prod_pos (fun _p hp ↦ (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos)

theorem assigned_divides_block (e n : ℕ) (B : Finset ℤ) : assigned e n B ∣ kernel B n := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).prime
  · intro p hp
    exact (mem_filter.mp hp).2

theorem assigned_divides_divisor (e n : ℕ) (B : Finset ℤ) : assigned e n B ∣ e := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).prime
  · intro p hp
    exact Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1

theorem prime_dvd_assigned_iff (e n p : ℕ) (B : Finset ℤ) (hp : Nat.Prime p) :
    p ∣ assigned e n B ↔ p ∈ assignedSupport e n B := by
  constructor
  · intro hd
    obtain ⟨r, hr, hpr⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp
      (Nat.prime_of_mem_primeFactors (mem_filter.mp hr).1)).mp hpr
    exact heq ▸ hr
  · exact fun h ↦ dvd_prod_of_mem id h

theorem shared_block_prime_divides_resultant (P : Finset (Finset ℤ)) (n p : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id)
    (hvalues : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0)
    (B C : Finset ℤ) (hB : B ∈ P) (hC : C ∈ P) (hBC : B ≠ C)
    (hp : Nat.Prime p) (hpB : p ∣ kernel B n) (hpC : p ∣ kernel C n) :
    p ∣ resultant (P.biUnion id) := by
  have hpos : ∀ E ∈ P, 0 < product E n := by
    intro E hE
    apply prod_pos
    intro a ha
    exact Int.natAbs_pos.mpr (hvalues a (mem_biUnion.mpr ⟨E, hE, ha⟩))
  have hprodB := hpB.trans (kernel_dvd B n (hpos B hB))
  have hprodC := hpC.trans (kernel_dvd C n (hpos C hC))
  obtain ⟨a, ha, hpa⟩ := (hp.prime.dvd_finsetProd_iff (fun a : ℤ ↦ ((n : ℤ) + a).natAbs)).mp hprodB
  obtain ⟨b, hb, hpb⟩ := (hp.prime.dvd_finsetProd_iff (fun b : ℤ ↦ ((n : ℤ) + b).natAbs)).mp hprodC
  have hBCdis : Disjoint B C := hdis hB hC hBC
  have hab : a ≠ b := by
    intro heq
    apply (Finset.disjoint_left.mp hBCdis ha)
    rwa [heq]
  exact shared_prime_divides_resultant (P.biUnion id) n p a b
    (mem_biUnion.mpr ⟨B, hB, ha⟩) (mem_biUnion.mpr ⟨C, hC, hb⟩) hab hpa hpb

theorem supports_disjoint (P : Finset (Finset ℤ)) (e n : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id)
    (hvalues : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0)
    (hcop : Nat.Coprime e (resultant (P.biUnion id)))
    (B C : Finset ℤ) (hB : B ∈ P) (hC : C ∈ P) (hBC : B ≠ C) :
    Disjoint (assignedSupport e n B) (assignedSupport e n C) := by
  apply Finset.disjoint_left.mpr
  intro p hpB hpC
  obtain ⟨hpe, hpBk⟩ := mem_filter.mp hpB
  obtain ⟨_, hpCk⟩ := mem_filter.mp hpC
  have hp := Nat.prime_of_mem_primeFactors hpe
  have hpD := shared_block_prime_divides_resultant P n p hdis hvalues B C hB hC hBC hp hpBk hpCk
  have hg := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpe) hpD
  rw [hcop.gcd_eq_one] at hg
  exact hp.ne_one (Nat.dvd_one.mp hg)

theorem support_union (P : Finset (Finset ℤ)) (e n : ℕ) (he : e ∣ grouped P n) :
    P.biUnion (assignedSupport e n) = e.primeFactors := by
  ext p
  constructor
  · intro hp
    obtain ⟨B, _, hpB⟩ := mem_biUnion.mp hp
    exact (mem_filter.mp hpB).1
  · intro hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpM := (Nat.dvd_of_mem_primeFactors hp).trans he
    obtain ⟨B, hB, hpB⟩ := (hpprime.prime.dvd_finsetProd_iff (fun B ↦ kernel B n)).mp hpM
    exact mem_biUnion.mpr ⟨B, hB, mem_filter.mpr ⟨hp, hpB⟩⟩

theorem assigned_product (P : Finset (Finset ℤ)) (e n : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id)
    (hvalues : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0)
    (hcop : Nat.Coprime e (resultant (P.biUnion id))) (hsf : Squarefree e)
    (he : e ∣ grouped P n) : (∏ B ∈ P, assigned e n B) = e := by
  have hsdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) (assignedSupport e n) :=
    fun B hB C hC hBC ↦ supports_disjoint P e n hdis hvalues hcop B C hB hC hBC
  have hp := prod_biUnion (f := id) hsdis
  rw [support_union P e n he] at hp
  simp only [id_eq] at hp
  rw [Nat.prod_primeFactors_of_squarefree hsf] at hp
  exact hp.symm

theorem assigned_coprime (P : Finset (Finset ℤ)) (e n : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id)
    (hvalues : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0)
    (hcop : Nat.Coprime e (resultant (P.biUnion id)))
    (B C : Finset ℤ) (hB : B ∈ P) (hC : C ∈ P) (hBC : B ≠ C) :
    Nat.Coprime (assigned e n B) (assigned e n C) := by
  apply Nat.coprime_of_dvd
  intro p hp hpB hpC
  have hs := supports_disjoint P e n hdis hvalues hcop B C hB hC hBC
  exact (Finset.disjoint_left.mp hs ((prime_dvd_assigned_iff e n p B hp).mp hpB))
    ((prime_dvd_assigned_iff e n p C hp).mp hpC)

theorem outside_source_allocation (P : Finset (Finset ℤ)) (e n : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id)
    (hvalues : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0)
    (he : e ∣ kernel (P.biUnion id) n) :
    let e' := outside e (resultant (P.biUnion id))
    (∏ B ∈ P, assigned e' n B) = e' ∧
    (∀ B ∈ P, assigned e' n B ∣ kernel B n ∧ assigned e' n B ∣ e') ∧
    Set.Pairwise (P : Set (Finset ℤ)) (fun B C ↦ Nat.Coprime (assigned e' n B) (assigned e' n C)) := by
  dsimp only
  let e' := outside e (resultant (P.biUnion id))
  have hcop := outside_coprime e (resultant (P.biUnion id))
  have hsf := outside_squarefree e (resultant (P.biUnion id))
  obtain ⟨R, _, hR⟩ := grouped_overlap_decomposition P n hdis hvalues
  have hqdiv : kernel (P.biUnion id) n ∣ grouped P n := ⟨R ^ 2, hR⟩
  have hediv : e' ∣ grouped P n := (outside_dvd e (resultant (P.biUnion id))).trans (he.trans hqdiv)
  refine ⟨assigned_product P e' n hdis hvalues hcop hsf hediv, ?_, ?_⟩
  · intro B _
    exact ⟨assigned_divides_block e' n B, assigned_divides_divisor e' n B⟩
  · intro B hB C hC hBC
    exact assigned_coprime P e' n hdis hvalues hcop B C hB hC hBC

end PaperP1.GroupedPrescribedDivisors
