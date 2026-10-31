module

public import PaperP1.Coding.BinaryResidual
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# The binary Griesmer bound

For a binary code of length `n`, dimension `r`, and positive minimum distance
at least `d`, the redundancy is at least
`sum (i < t) (ceil (d / 2^i)) - t` whenever `t ≤ r`.

The proof iterates minimum-word residual codes. The positive-integer ceiling
is first written as `(d - 1) / 2^i + 1`, keeping the argument entirely in
natural-number arithmetic. No coding-theory proposition is assumed.
-/

@[expose] public section

namespace PaperP1.GriesmerBound

open PaperP1.Arithmetic PaperP1.BinaryResidual Finset

local instance griesmerPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

/-- The first `t` terms of the binary Griesmer sum for a positive distance. -/
def griesmerSum (t d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, ((d - 1) / 2 ^ i + 1)

@[simp]
theorem griesmerSum_zero (d : ℕ) : griesmerSum 0 d = 0 := by
  simp only [griesmerSum, Finset.range_zero, Finset.sum_empty]

theorem length_le_griesmerSum (t d : ℕ) : t ≤ griesmerSum t d := by
  calc
    t = ∑ _i ∈ Finset.range t, 1 := by simp
    _ ≤ griesmerSum t d := by
      unfold griesmerSum
      exact Finset.sum_le_sum (fun i _ ↦ Nat.le_add_left 1 ((d - 1) / 2 ^ i))

/-- Taking a residual code divides the lower distance by two, rounded up. -/
theorem griesmerSum_succ (t d : ℕ) (hd : 0 < d) :
    griesmerSum (t + 1) d = d + griesmerSum t ((d + 1) / 2) := by
  have hhalf : (d + 1) / 2 - 1 = (d - 1) / 2 := by omega
  have hfirst : d - 1 + 1 = d := by omega
  rw [griesmerSum, Finset.sum_range_succ']
  simp only [pow_zero, Nat.div_one, hfirst]
  rw [add_comm]
  congr 1
  unfold griesmerSum
  apply Finset.sum_congr rfl
  intro i _
  rw [hhalf, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm 2]

/-- The version without truncated subtraction. It also retains the unused
`r - t` dimensions after the `t` residual steps. -/
theorem griesmer_with_unused_dimension (t : ℕ) {ι : Type*} [Fintype ι]
    (C : Submodule F₂ (Word ι)) {d : ℕ} (hd : 0 < d)
    (hmin : MinWeightAtLeast C d) (ht : t ≤ Module.finrank F₂ C) :
    Module.finrank F₂ C + griesmerSum t d ≤ Fintype.card ι + t := by
  induction t generalizing ι d with
  | zero =>
      simpa only [griesmerSum_zero, add_zero, Module.finrank_fintype_fun_eq_card] using
        C.finrank_le
  | succ t ih =>
      have hr : 0 < Module.finrank F₂ C := by omega
      obtain ⟨c, hc⟩ := exists_minimum_word C hr
      let R := residualCode C c
      have hdim := finrank_residual_add_one C c hc
      have hlen := card_outside_add_weight (c : Word ι)
      have hdc : d ≤ hammingNorm (c : Word ι) := hmin c hc.1
      have hhalfpos : 0 < (d + 1) / 2 := by omega
      have hres : MinWeightAtLeast R ((d + 1) / 2) := by
        intro y hy
        exact (Nat.div_le_div_right (Nat.add_le_add_right hdc 1)).trans
          (residual_minWeight C c hc y hy)
      have htr : t ≤ Module.finrank F₂ R := by
        change Module.finrank F₂ R + 1 = _ at hdim
        omega
      have hrec := ih R hhalfpos hres htr
      rw [griesmerSum_succ t d hd]
      change Module.finrank F₂ R + 1 = _ at hdim
      omega

/-- The full Griesmer bound for binary linear codes. -/
theorem griesmer_bound {ι : Type*} [Fintype ι]
    (C : Submodule F₂ (Word ι)) {d : ℕ} (hd : 0 < d)
    (hmin : MinWeightAtLeast C d) :
    griesmerSum (Module.finrank F₂ C) d ≤ Fintype.card ι := by
  have h := griesmer_with_unused_dimension (Module.finrank F₂ C) C hd hmin le_rfl
  omega

/-- The prefix form used for the relation code in P1, Lemma 2.1. -/
theorem griesmer_redundancy {ι : Type*} [Fintype ι]
    (C : Submodule F₂ (Word ι)) {d t : ℕ} (hd : 0 < d)
    (hmin : MinWeightAtLeast C d) (ht : t ≤ Module.finrank F₂ C) :
    griesmerSum t d - t ≤ Fintype.card ι - Module.finrank F₂ C := by
  have h := griesmer_with_unused_dimension t C hd hmin ht
  have hr : Module.finrank F₂ C ≤ Fintype.card ι := by
    simpa only [Module.finrank_fintype_fun_eq_card] using C.finrank_le
  omega

/-- The natural quotient form is exactly the usual real-valued ceiling. -/
theorem positive_nat_div_ceil (d q : ℕ) (hd : 0 < d) (hq : 0 < q) :
    ⌈(d : ℝ) / q⌉₊ = (d - 1) / q + 1 := by
  apply eq_of_forall_ge_iff
  intro m
  rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hq)]
  have hnat : (d - 1) / q + 1 ≤ m ↔ d ≤ m * q := by
    rw [Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul hq]
    omega
  rw [hnat]
  exact_mod_cast (Iff.rfl : d ≤ m * q ↔ d ≤ m * q)

theorem griesmerSum_eq_sum_ceil (t d : ℕ) (hd : 0 < d) :
    griesmerSum t d = ∑ i ∈ Finset.range t, ⌈(d : ℝ) / (2 : ℝ) ^ i⌉₊ := by
  unfold griesmerSum
  apply Finset.sum_congr rfl
  intro i _
  have h := positive_nat_div_ceil d (2 ^ i) hd (by positivity)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h.symm

/-- P1's exact ceiling notation, for an arbitrary binary linear code. -/
theorem griesmer_redundancy_ceil {ι : Type*} [Fintype ι]
    (C : Submodule F₂ (Word ι)) {d t : ℕ} (hd : 0 < d)
    (hmin : MinWeightAtLeast C d) (ht : t ≤ Module.finrank F₂ C) :
    (∑ i ∈ Finset.range t, ⌈(d : ℝ) / (2 : ℝ) ^ i⌉₊) - t ≤
      Fintype.card ι - Module.finrank F₂ C := by
  rw [← griesmerSum_eq_sum_ceil t d hd]
  exact griesmer_redundancy C hd hmin ht

end PaperP1.GriesmerBound
