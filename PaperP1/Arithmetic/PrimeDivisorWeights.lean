module

public import PaperP1.Arithmetic.OrdinarySmoothCensus
public import PaperP1.Arithmetic.IntervalDivisibilityCount

/-! # Exact prime-divisor weights and the literal Ramare quotient identity with square-divisor exceptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeDivisorWeights
open Finset
open scoped Classical

def factors (P : Finset ℕ) (n : ℕ) : Finset ℕ := P.filter (fun p ↦ p ∣ n)

def count (P : Finset ℕ) (n : ℕ) : ℕ := (factors P n).card

theorem factors_mul_prime (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (p m : ℕ)
    (hp : p ∈ P) : factors P (p*m) = insert p (factors P m) := by
  ext q
  simp only [factors, mem_filter, mem_insert]
  constructor
  · intro hq
    rcases (hP q hq.1).dvd_mul.mp hq.2 with hqp | hqm
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq (hP q hq.1) (hP p hp)).mp hqp)
    · exact Or.inr ⟨hq.1, hqm⟩
  · rintro (hqp | hq)
    · subst q
      exact ⟨hp, dvd_mul_right p m⟩
    · exact ⟨hq.1, dvd_mul_of_dvd_right hq.2 p⟩

theorem count_mul_prime (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (p m : ℕ)
    (hp : p ∈ P) : count P (p*m) = count P m + if p ∣ m then 0 else 1 := by
  unfold count
  rw [factors_mul_prime P hP p m hp]
  by_cases hpm : p ∣ m
  · have hmem : p ∈ factors P m := mem_filter.mpr ⟨hp, hpm⟩
    rw [card_insert_of_mem hmem]
    simp only [hpm, ite_true, add_zero]
  · rw [card_insert_of_notMem (by simpa only [factors, mem_filter, hp, true_and] using hpm)]
    simp only [hpm, ite_false]

theorem count_pos {P : Finset ℕ} {n p : ℕ} (hp : p ∈ P) (hd : p ∣ n) : 0 < count P n :=
  Finset.card_pos.mpr ⟨p, mem_filter.mpr ⟨hp, hd⟩⟩

theorem exact_weight_identity (P : Finset ℕ) (n : ℕ) (hn : 0 < count P n)
    (f : ℕ → ℂ) (hf : ∀ a b, f (a*b) = f a * f b) :
    (∑ p ∈ factors P n, f p * f (n/p) / (count P n : ℂ)) = f n := by
  have he : ∀ p ∈ factors P n, f p * f (n/p) = f n := by
    intro p hp
    rw [← hf, Nat.mul_div_cancel' (mem_filter.mp hp).2]
  have hsum : (∑ p ∈ factors P n, f p * f (n/p) / (count P n : ℂ)) =
      ∑ _p ∈ factors P n, f n / (count P n : ℂ) :=
    sum_congr rfl (fun p hp ↦ by rw [he p hp])
  rw [hsum, sum_const, nsmul_eq_mul]
  have hne : (count P n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  change (count P n : ℂ) * (f n / count P n) = _
  field_simp
theorem quotient_count_add_one (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (n p : ℕ)
    (hp : p ∈ P) (hpn : p ∣ n) (hpsq : ¬p^2 ∣ n) : count P (n/p) + 1 = count P n := by
  have hnot : ¬p ∣ n/p := by
    intro hh
    apply hpsq
    rw [pow_two]
    exact (Nat.dvd_div_iff_mul_dvd hpn).mp hh
  have hh := count_mul_prime P hP p (n/p) hp
  rw [Nat.mul_div_cancel' hpn, ite_eq_right hnot] at hh
  exact hh.symm

theorem ramare_on_squarefree_support (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (n : ℕ)
    (hn : 0 < count P n) (hsq : ∀ p ∈ P, ¬p^2 ∣ n)
    (f : ℕ → ℂ) (hf : ∀ a b, f (a*b) = f a * f b) :
    (∑ p ∈ factors P n, f p * f (n/p) / ((count P (n/p) + 1 : ℕ) : ℂ)) = f n := by
  calc
    _ = ∑ p ∈ factors P n, f p * f (n/p) / (count P n : ℂ) := by
      apply sum_congr rfl
      intro p hp
      rw [quotient_count_add_one P hP n p (mem_filter.mp hp).1 (mem_filter.mp hp).2 (hsq p (mem_filter.mp hp).1)]
    _ = _ := exact_weight_identity P n hn f hf

def squareExceptions (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Ioc 0 X).filter fun n ↦ ∃ p ∈ P, p^2 ∣ n

theorem square_exceptions_card (P : Finset ℕ) (X : ℕ) :
    (squareExceptions P X).card ≤ ∑ p ∈ P, X / p^2 := by
  have he : squareExceptions P X = P.biUnion (fun p ↦ (Ioc 0 X).filter (p^2 ∣ ·)) := by
    ext n
    simp only [squareExceptions, mem_filter, mem_biUnion]
    tauto
  rw [he]
  exact (card_biUnion_le).trans_eq (by simp only [Nat.Ioc_filter_dvd_card_eq_div])

theorem multiples_image (S : Finset ℕ) (X p : ℕ) (hp : 0 < p)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ X) :
    ((Icc 1 (X/p)).filter (fun m ↦ p*m ∈ S)).image (fun m ↦ p*m) = S.filter (p ∣ ·) := by
  ext n
  constructor
  · intro hn
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    exact mem_filter.mpr ⟨(mem_filter.mp hm).2, dvd_mul_right p m⟩
  · intro hn
    obtain ⟨hnS, hpn⟩ := mem_filter.mp hn
    obtain ⟨hn0, hnX⟩ := hS n hnS
    refine mem_image.mpr ⟨n/p, mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩, Nat.mul_div_cancel' hpn⟩
    · exact Nat.div_pos (Nat.le_of_dvd hn0 hpn) hp
    · exact Nat.div_le_div_right hnX
    · simpa only [Nat.mul_div_cancel' hpn] using hnS

theorem sum_multiples (S : Finset ℕ) (X p : ℕ) (hp : 0 < p)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ X) (g : ℕ → ℂ) :
    (∑ n ∈ S.filter (p ∣ ·), g n) =
      ∑ m ∈ Icc 1 (X/p), if p*m ∈ S then g (p*m) else 0 := by
  rw [← multiples_image S X p hp hS, sum_image]
  · rw [sum_filter]
  · intro m _ n _ h
    exact Nat.eq_of_mul_eq_mul_left hp h

theorem ramare_sum (S P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ X) (hfactor : ∀ n ∈ S, 0 < count P n)
    (hsq : ∀ n ∈ S, ∀ p ∈ P, ¬p^2 ∣ n)
    (f : ℕ → ℂ) (hf : ∀ a b, f (a*b) = f a * f b) :
    (∑ n ∈ S, f n) =
      ∑ p ∈ P, ∑ m ∈ Icc 1 (X/p),
        if p*m ∈ S then f p * f m / ((count P m + 1 : ℕ) : ℂ) else 0 := by
  calc
    _ = ∑ n ∈ S, ∑ p ∈ factors P n, f p * f (n/p) / ((count P (n/p)+1 : ℕ) : ℂ) := by
      apply sum_congr rfl
      intro n hn
      exact (ramare_on_squarefree_support P hP n (hfactor n hn) (hsq n hn) f hf).symm
    _ = ∑ p ∈ P, ∑ n ∈ S.filter (p ∣ ·), f p * f (n/p) / ((count P (n/p)+1 : ℕ) : ℂ) := by
      simp only [factors, sum_filter]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      rw [sum_multiples S X p (hP p hp).pos hS]
      apply sum_congr rfl
      intro m hm
      rw [Nat.mul_div_cancel_left m (hP p hp).pos]

end PrimeDivisorWeights
