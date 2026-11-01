module

public import PaperP1.Arithmetic.SquarefreeKernelProducts

/-! # Removing the actual primes of a resultant from a squarefree divisor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquarefreeOutsideDivisor

open Finset

def outsideSupport (e D : ℕ) : Finset ℕ := e.primeFactors.filter fun p ↦ ¬p ∣ D
def insideSupport (e D : ℕ) : Finset ℕ := e.primeFactors.filter fun p ↦ p ∣ D
def outside (e D : ℕ) : ℕ := (outsideSupport e D).prod id
def inside (e D : ℕ) : ℕ := (insideSupport e D).prod id

theorem outside_pos (e D : ℕ) : 0 < outside e D :=
  prod_pos (fun _p hp ↦ (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos)

theorem inside_pos (e D : ℕ) : 0 < inside e D :=
  prod_pos (fun _p hp ↦ (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos)

theorem outside_dvd (e D : ℕ) : outside e D ∣ e := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).prime
  · intro p hp
    exact Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1

theorem inside_dvd (e D : ℕ) : inside e D ∣ D := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).prime
  · intro p hp
    exact (mem_filter.mp hp).2

theorem inside_divides_divisor (e D : ℕ) : inside e D ∣ e := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).prime
  · intro p hp
    exact Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1

theorem prime_dvd_outside_iff (e D p : ℕ) (hp : Nat.Prime p) :
    p ∣ outside e D ↔ p ∈ outsideSupport e D := by
  constructor
  · intro hd
    obtain ⟨r, hr, hpr⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp
      (Nat.prime_of_mem_primeFactors (mem_filter.mp hr).1)).mp hpr
    exact heq ▸ hr
  · exact fun h ↦ dvd_prod_of_mem id h

theorem outside_coprime (e D : ℕ) : Nat.Coprime (outside e D) D := by
  apply Nat.coprime_of_dvd
  intro p hp hpe hpD
  exact (mem_filter.mp ((prime_dvd_outside_iff e D p hp).mp hpe)).2 hpD

theorem outside_squarefree (e D : ℕ) : Squarefree (outside e D) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
        (Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1)).mpr hpq)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).squarefree

theorem split (e D : ℕ) (he : Squarefree e) : outside e D * inside e D = e := by
  calc
    _ = e.primeFactors.prod id := prod_filter_not_mul_prod_filter e.primeFactors (fun p ↦ p ∣ D) id
    _ = e := Nat.prod_primeFactors_of_squarefree he

theorem inside_eq_gcd (e D : ℕ) (he : Squarefree e) : inside e D = Nat.gcd e D := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (inside_divides_divisor e D) (inside_dvd e D)
  · have hsf : Squarefree (Nat.gcd e D) := he.squarefree_of_dvd (Nat.gcd_dvd_left e D)
    rw [← Nat.prod_primeFactors_of_squarefree hsf]
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).prime
    · intro p hp
      have hpg := Nat.dvd_of_mem_primeFactors hp
      have hpe := hpg.trans (Nat.gcd_dvd_left e D)
      have hpD := hpg.trans (Nat.gcd_dvd_right e D)
      apply dvd_prod_of_mem id
      exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpe, he.ne_zero⟩, hpD⟩

theorem outside_eq_div_gcd (e D : ℕ) (he : Squarefree e) : outside e D = e / Nat.gcd e D := by
  have hmul : inside e D * (e / inside e D) = inside e D * outside e D := by
    calc
      _ = e := by rw [mul_comm, Nat.div_mul_cancel (inside_divides_divisor e D)]
      _ = _ := by rw [mul_comm, split e D he]
  have hq := Nat.eq_of_mul_eq_mul_left (inside_pos e D) hmul
  rw [inside_eq_gcd e D he] at hq
  exact hq.symm

theorem prime_dvd_radical_iff (D p : ℕ) (hD : 0 < D) (hp : Nat.Prime p) :
    p ∣ D.primeFactors.prod id ↔ p ∣ D := by
  constructor
  · intro hdiv
    obtain ⟨r, hr, hpr⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdiv
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hr)).mp hpr
    exact heq ▸ Nat.dvd_of_mem_primeFactors hr
  · intro hdiv
    exact dvd_prod_of_mem id (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hD.ne'⟩)

theorem outside_eq_source (e D : ℕ) (he : Squarefree e) (hD : 0 < D) :
    outside e D = e / Nat.gcd e (D.primeFactors.prod id) := by
  have hs : insideSupport e D = insideSupport e (D.primeFactors.prod id) := by
    ext p
    simp only [insideSupport, mem_filter]
    constructor
    · rintro ⟨hp, hdiv⟩
      exact ⟨hp, (prime_dvd_radical_iff D p hD (Nat.prime_of_mem_primeFactors hp)).mpr hdiv⟩
    · rintro ⟨hp, hdiv⟩
      exact ⟨hp, (prime_dvd_radical_iff D p hD (Nat.prime_of_mem_primeFactors hp)).mp hdiv⟩
  have hi : inside e D = inside e (D.primeFactors.prod id) := congrArg (fun S : Finset ℕ ↦ S.prod id) hs
  rw [inside_eq_gcd e D he, inside_eq_gcd e (D.primeFactors.prod id) he] at hi
  rw [outside_eq_div_gcd e D he, hi]

theorem log_loss (e D : ℕ) (he : Squarefree e) (hD : 0 < D) :
    Real.log e ≤ Real.log (outside e D) + Real.log D := by
  have hi : inside e D ≤ D := Nat.le_of_dvd hD (inside_dvd e D)
  have hlog := Real.log_le_log (by exact_mod_cast inside_pos e D : (0 : ℝ) < inside e D)
    (by exact_mod_cast hi : (inside e D : ℝ) ≤ D)
  have hsplit : (outside e D : ℝ) * inside e D = (e : ℝ) := by exact_mod_cast split e D he
  rw [← hsplit, Real.log_mul (by exact_mod_cast (outside_pos e D).ne')
    (by exact_mod_cast (inside_pos e D).ne')]
  linarith

end PaperP1.SquarefreeOutsideDivisor
