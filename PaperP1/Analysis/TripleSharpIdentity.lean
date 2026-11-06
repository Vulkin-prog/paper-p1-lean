module

public import PaperP1.Analysis.TripleCoefficientFibre
public import PaperP1.Arithmetic.RealTripleConvolution
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TripleSharpIdentity
open Finset Nat MeasureTheory PaperP1 TripleCoefficientFibre
open scoped Classical

theorem filtered_levels (X d : ℕ) (hd : 0 < d) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (hcover : Icc 1 X ⊆ S) :
    S.filter (fun n ↦ d*n ≤ X)=Icc 1 (X/d) := by
  ext n
  simp only [mem_filter,mem_Icc]
  constructor
  · rintro ⟨hn,hcut⟩
    exact ⟨hS n hn,(Nat.le_div_iff_mul_le hd).mpr (by simpa only [mul_comm] using hcut)⟩
  · rintro ⟨hpos,hcut⟩
    have hprod : d*n ≤ X := by
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hcut
    have hnX : n ≤ X := (Nat.le_mul_of_pos_left n hd).trans hprod
    exact ⟨hcover (mem_Icc.mpr ⟨hpos,hnX⟩),hprod⟩

theorem sharp_expansion (f : ℕ → ℂ) (X : ℕ) (P Q S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hS : ∀ n ∈ S, 0 < n) (hcover : Icc 1 X ⊆ S) :
    FiniteGaussianPerron.sharp (X : ℝ) (triples P Q S) (coefficient f X) level=
      ∑ p ∈ P, ∑ q ∈ Q, ∑ n ∈ Icc 1 (X/(p*q)), coefficient f X ((p,q),n) := by
  simp only [FiniteGaussianPerron.sharp,triples,sum_product,level,Nat.cast_le]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  rw [← sum_filter,filtered_levels X (p*q) (Nat.mul_pos (hP p hp).pos (hQ q hq).pos) S hS hcover]

theorem sharp_eq_triple (f : ℕ →* ℂ) (X : ℕ) (P Q S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hS : ∀ n ∈ S, 0 < n) (hcover : Icc 1 X ⊆ S)
    (hQcover : ∀ p ∈ P, ∀ q ∈ (Icc 1 (X/p)).filter Nat.Prime, q ∈ Q) :
    FiniteGaussianPerron.sharp (X : ℝ) (triples P Q S) (coefficient f X) level=
      RealTripleConvolution.triple f X P := by
  rw [sharp_expansion f X P Q S hP hQ hS hcover,RealTripleConvolution.triple_expansion]
  apply sum_congr rfl
  intro p hp
  symm
  apply sum_subset (hQcover p hp)
  intro q hq hnot
  have hprime := hQ q hq
  have hlt : X/p < q := by
    by_contra! hh
    exact hnot (mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.one_le,hh⟩,hprime⟩)
  have hzero : X/(p*q)=0 := by
    rw [← Nat.div_div_eq_div_mul]
    exact Nat.div_eq_of_lt hlt
  simp only [hzero,show Icc 1 (0 : ℕ)=∅ by decide,sum_empty]

def bandPrimes (X : ℕ) (U : ℝ) : Finset ℕ :=
  ((Icc 1 X).filter Nat.Prime).filter (fun q ↦ Real.log (q : ℝ) ≤ 2*U)

theorem band_primes_cover (X p : ℕ) (U : ℝ)
    (hband : Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) :
    ∀ q ∈ (Icc 1 (X/p)).filter Nat.Prime, q ∈ bandPrimes X U := by
  intro q hq
  have hq' := mem_filter.mp hq
  have hqI := mem_Icc.mp hq'.1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq'.2.pos
  have hquot : (q : ℝ) ≤ (X : ℝ)/(p : ℝ) :=
    (by exact_mod_cast hqI.2 : (q : ℝ) ≤ (X/p : ℕ)).trans Nat.cast_div_le
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hqI.1,hqI.2.trans (Nat.div_le_self X p)⟩,hq'.2⟩,
    (Real.log_le_log hqR hquot).trans hband⟩



theorem band_primes_prime (X : ℕ) (U : ℝ) (q : ℕ) (hq : q ∈ bandPrimes X U) : q.Prime :=
  (mem_filter.mp (mem_filter.mp hq).1).2

theorem band_primes_log (X : ℕ) (U : ℝ) (q : ℕ) (hq : q ∈ bandPrimes X U) : Real.log (q : ℝ) ≤ 2*U :=
  (mem_filter.mp hq).2

theorem band_sharp_eq_triple (f : ℕ →* ℂ) (X : ℕ) (U : ℝ) (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U)
    (hS : ∀ n ∈ S, 0 < n) (hcover : Icc 1 X ⊆ S) :
    FiniteGaussianPerron.sharp (X : ℝ) (triples P (bandPrimes X U) S) (coefficient f X) level=
      RealTripleConvolution.triple f X P := by
  apply sharp_eq_triple f X P (bandPrimes X U) S (fun p hp ↦ (hP p hp).1)
    (band_primes_prime X U) hS hcover
  intro p hp
  exact band_primes_cover X p U (hP p hp).2
end PaperP1.TripleSharpIdentity
