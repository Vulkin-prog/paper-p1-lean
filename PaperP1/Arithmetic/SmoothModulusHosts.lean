module

public import PaperP1.Diophantine.LinearKernelFibres
public import PaperP1.Arithmetic.ShortIntervalCongruences
public import PaperP1.Combinatorics.BoundedIntegerMotifs
public import PaperP1.Combinatorics.FiniteCoverCount
public import Mathlib.Data.Fintype.Pi

/-! # Actual centres with a large coprime divisor certificate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothModulusHosts

open Finset PaperP1.LinearKernelFibres PaperP1.BoundedIntegerMotifs

theorem value_cast (n W : ℕ) (a : ℤ) (hn : W < n) (ha : a.natAbs ≤ W) :
    (value n a : ℤ) = (n : ℤ) + a := by
  have habs : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ha
  have hal := (abs_le.mp habs).1
  have hWn : (W : ℤ) < n := by exact_mod_cast hn
  have hp : 0 < (n : ℤ) + a := by omega
  change (((n : ℤ) + a).natAbs : ℤ) = (n : ℤ) + a
  rw [← Int.abs_eq_natAbs, abs_of_pos hp]

theorem common_modEq (n m W d : ℕ) (a : ℤ) (hn : W < n) (hm : W < m)
    (ha : a.natAbs ≤ W) (hdn : d ∣ value n a) (hdm : d ∣ value m a) : Nat.ModEq d n m := by
  have hn' : (d : ℤ) ∣ (n : ℤ) + a := by
    rw [← value_cast n W a hn ha]
    exact_mod_cast hdn
  have hm' : (d : ℤ) ∣ (m : ℤ) + a := by
    rw [← value_cast m W a hm ha]
    exact_mod_cast hdm
  apply Nat.modEq_iff_dvd.mpr
  convert dvd_sub hm' hn' using 1; ring

variable {ι : Type*} [Fintype ι]

theorem fixed_fibre_count (S : Finset ℕ) (X W : ℕ) (a : ι → ℤ) (G : ι → ℕ)
    (hbox : ∀ n ∈ S, W < n ∧ n ≤ X) (ha : ∀ i, (a i).natAbs ≤ W)
    (hcop : Pairwise fun i j ↦ Nat.Coprime (G i) (G j)) (hprod : X ≤ ∏ i, G i)
    (hdiv : ∀ n ∈ S, ∀ i, G i ∣ value n (a i)) : S.card ≤ 1 := by
  apply card_le_one.mpr
  intro n hn m hm
  have hmod : ∀ i, Nat.ModEq (G i) n m :=
    fun i ↦ common_modEq n m W (G i) (a i) (hbox n hn).1 (hbox m hm).1 (ha i) (hdiv n hn i) (hdiv m hm i)
  have hdiff := PaperP1.ShortIntervalCongruences.product_dvd_difference G hcop n m hmod
  have hdiff' := PaperP1.ShortIntervalCongruences.product_dvd_difference G hcop m n (fun i ↦ (hmod i).symm)
  have hnbox := hbox n hn
  have hmbox := hbox m hm
  have hz : m - n = 0 := Nat.eq_zero_of_dvd_of_lt hdiff (lt_of_lt_of_le (by
    have hn' := (hbox n hn).1
    have hm' := (hbox m hm).2
    omega) hprod)
  have hz' : n - m = 0 := Nat.eq_zero_of_dvd_of_lt hdiff' (lt_of_lt_of_le (by
    have hm' := (hbox m hm).1
    have hn' := (hbox n hn).2
    omega) hprod)
  omega

def HasCertificate (m W n : ℕ) : Prop :=
  ∃ a : ι → ℤ, (∀ i, (a i).natAbs ≤ W) ∧ ∃ G : ι → ℕ,
    Pairwise (fun i j ↦ Nat.Coprime (G i) (G j)) ∧ ∏ i, G i = m ∧
      ∀ i, G i ∣ value n (a i)

theorem fixed_modulus_count (m W X : ℕ) (hm : 0 < m) (hXm : X ≤ m) (S : Finset ℕ)
    (hS : ∀ n ∈ S, W < n ∧ n ≤ X ∧ HasCertificate (ι := ι) m W n) :
    S.card ≤ (2 * W + 1) ^ Fintype.card ι * m.divisors.card ^ Fintype.card ι := by
  classical
  let O := Fintype.piFinset fun _ : ι ↦ offsets W
  let D := Fintype.piFinset fun _ : ι ↦ m.divisors
  let I := (O ×ˢ D).filter fun w ↦
    Pairwise (fun i j ↦ Nat.Coprime (w.2 i) (w.2 j)) ∧ ∏ i, w.2 i = m
  let F := fun w : (ι → ℤ) × (ι → ℕ) ↦ S.filter fun n ↦ ∀ i, w.2 i ∣ value n (w.1 i)
  have hcover : ∀ n ∈ S, ∃ w ∈ I, n ∈ F w := by
    intro n hnS
    obtain ⟨a, ha, G, hcop, hprod, hdiv⟩ := (hS n hnS).2.2
    have haO : a ∈ O := by
      apply Fintype.mem_piFinset.mpr
      intro i
      exact (subset_offsets W {a i}).mpr (by intro x hx; rw [mem_singleton.mp hx]; exact ha i) (mem_singleton_self _)
    have hGD : G ∈ D := by
      apply Fintype.mem_piFinset.mpr
      intro i
      apply Nat.mem_divisors.mpr
      refine ⟨?_, hm.ne'⟩
      rw [← hprod]
      exact dvd_prod_of_mem G (mem_univ i)
    exact ⟨(a, G), mem_filter.mpr ⟨mem_product.mpr ⟨haO, hGD⟩, hcop, hprod⟩,
      mem_filter.mpr ⟨hnS, hdiv⟩⟩
  have hF : ∀ w ∈ I, ((F w).card : ℝ) ≤ 1 := by
    intro w hw
    obtain ⟨hwpool, hcop, hprod⟩ := mem_filter.mp hw
    have haO := Fintype.mem_piFinset.mp (mem_product.mp hwpool).1
    have ha : ∀ i, (w.1 i).natAbs ≤ W := by
      intro i
      exact (subset_offsets W {w.1 i}).mp (singleton_subset_iff.mpr (haO i)) _ (mem_singleton_self _)
    have hc := fixed_fibre_count (F w) X W w.1 w.2 (by
      intro n hnF
      have hnS := (mem_filter.mp hnF).1
      exact ⟨(hS n hnS).1, (hS n hnS).2.1⟩) ha hcop (by rw [hprod]; exact hXm)
      (fun n hnF ↦ (mem_filter.mp hnF).2)
    exact_mod_cast hc
  have hcard := PaperP1.FiniteCoverCount.cardinal_le S I F 1 hcover hF
  have hSI : S.card ≤ I.card := by exact_mod_cast (by simpa only [mul_one] using hcard : (S.card : ℝ) ≤ I.card)
  have hI : I.card ≤ (O ×ˢ D).card := card_filter_le _ _
  calc
    _ ≤ (O ×ˢ D).card := hSI.trans hI
    _ = _ := by
      rw [card_product]
      dsimp [O, D]
      rw [Fintype.card_piFinset, Fintype.card_piFinset]
      simp only [prod_const, card_univ, offsets_card]

end PaperP1.SmoothModulusHosts
