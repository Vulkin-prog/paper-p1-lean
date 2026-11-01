module

public import PaperP1.Arithmetic.NormalizedUnitCount
public import PaperP1.Arithmetic.UnionMatchDensity
public import Mathlib.Data.Int.GCD

/-! # Actual normalized value coincidences imply the matching congruences -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.ExactMatchCongruences

open PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount

theorem gcd_quotient_divides {c a : ℕ} (hc : 0 < c) (w : ℤ) (hdiv : (c : ℤ) ∣ (a : ℤ) * w) :
    ((c / c.gcd a : ℕ) : ℤ) ∣ w := by
  have hbezout := Nat.gcd_eq_gcd_ab c a
  have heq : ((c.gcd a : ℕ) : ℤ) * w =
      (c : ℤ) * (Nat.gcdA c a * w) + ((a : ℤ) * w) * Nat.gcdB c a := by
    rw [hbezout]
    ring
  have hgdiv : (c : ℤ) ∣ ((c.gcd a : ℕ) : ℤ) * w := by
    rw [heq]
    exact dvd_add (dvd_mul_right _ _) (hdiv.mul_right _)
  have hprod : (c : ℤ) = ((c / c.gcd a : ℕ) : ℤ) * (c.gcd a : ℕ) := by
    exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_left c a)).symm
  rw [hprod, mul_comm ((c / c.gcd a : ℕ) : ℤ) (c.gcd a : ℕ)] at hgdiv
  have hg : (0 : ℤ) < (c.gcd a : ℕ) := by exact_mod_cast Nat.gcd_pos_of_pos_left a hc
  exact Int.dvd_of_mul_dvd_mul_left hg.ne' hgdiv

theorem source_parameter {a b x y L : ℕ} (ha : 0 < a) (hab : a.Coprime b) (hx : 2 ≤ x)
    (i j : Fin (L + 1)) (hunit : b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j) :
    ∃ t : ℕ, 0 < t ∧ startCompleteVertexLabel x L i = a * t ∧ startCompleteVertexLabel y L j = b * t := by
  have hdiv : a ∣ startCompleteVertexLabel x L i := hab.dvd_of_dvd_mul_left ⟨_, hunit⟩
  obtain ⟨t, ht⟩ := hdiv
  have hlabel : 0 < startCompleteVertexLabel x L i := values_positive hx _ (mem_values.mpr ⟨i, rfl⟩)
  have htpos : 0 < t := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, mul_zero] at ht
    omega
  refine ⟨t, htpos, ht, ?_⟩
  apply mul_left_cancel₀ ha.ne'
  calc
    a * startCompleteVertexLabel y L j = b * startCompleteVertexLabel x L i := hunit.symm
    _ = a * (b * t) := by rw [ht]; ring

theorem one_family_congruence {q c d x z L t : ℕ} (hc : 0 < c) (hx : 0 < x) (hz : 0 < z)
    (i₀ i k : Fin (L + 1)) (h : ℤ)
    (hbase : startCompleteVertexLabel x L i₀ = q * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hmatch : q * d * startCompleteVertexLabel z L k = c * startCompleteVertexLabel x L i) :
    ((c / c.gcd q : ℕ) : ℤ) ∣ h + (d : ℤ) * offset k := by
  have hbaseZ : (x : ℤ) + offset i₀ = (q : ℤ) * t := by
    rw [← label_cast hx]
    exact_mod_cast hbase
  have hmatchZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hmatch
  push_cast at hmatchZ
  rw [label_cast hz, label_cast hx] at hmatchZ
  have hbaseMul := congrArg (fun n : ℤ ↦ (c : ℤ) * n) hbaseZ
  have htargetMul := congrArg (fun n : ℤ ↦ (q : ℤ) * n) htarget
  have heq : (q : ℤ) * (h + (d : ℤ) * offset k) = (c : ℤ) * (offset i - offset i₀) := by
    nlinarith
  exact gcd_quotient_divides hc _ ⟨offset i - offset i₀, heq⟩

end PaperP1.ExactMatchCongruences
