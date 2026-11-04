/-
Adapted from Vulkin-prog/paper-c-lean, PaperCPrel8/PrimeForcing.lean,
commit b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0,
Git blob 7083126f254fd91073f7b3786c094ba5b637f1bf.
Changes: Lean 4.36 modules and the P1 raw-value model; the old product PMF
is replaced by actual P1 finite weights and nested normalized uniform averages.
-/
module

public import PaperP1.Arithmetic.PrivatePivotGeometry
public import PaperP1.Probability.PrivateCoordinateForcing
public import Mathlib.Tactic.Abel

/-! # Forcing actual prime signs with the complete conditional sample law

Every observable is an observable of the full prime assignment. Outside the
directed footprint all raw values are fixed; no dependency-graph claim is made.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivatePrimeForcing

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.PrivatePivotGeometry PaperP1.Algebra PaperP1.Probability
  PaperP1.UniformFubini
open scoped BigOperators

local instance privatePrimeForcingDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

variable {M : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def liftBlock (q : ι → PrimeUpTo M) (c : ι → F₂) : SampleSpace M :=
  ∑ a, c a • Pi.single (q a) 1

def forceWord (v : ι → ℕ) (q : ι → PrimeUpTo M) (word : ι → F₂)
    (ω : SampleSpace M) : SampleSpace M :=
  ω + liftBlock q (word - valueSystem M v ω)

theorem value_liftBlock (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (c : ι → F₂) : valueSystem M v (liftBlock q c) = c := by
  simp only [liftBlock, map_sum, map_smul, hq]
  funext a
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]

omit [DecidableEq ι] in
theorem liftBlock_add (q : ι → PrimeUpTo M) (c d : ι → F₂) :
    liftBlock q (c + d) = liftBlock q c + liftBlock q d := by
  simp [liftBlock, add_smul, Finset.sum_add_distrib]

theorem forceWord_hits (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (ω : SampleSpace M) :
    valueSystem M v (forceWord v q word ω) = word := by
  rw [forceWord, map_add, value_liftBlock v q hq]
  exact add_sub_cancel _ _

omit [DecidableEq ι] in
theorem forceWord_fixes (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (word : ι → F₂) (ω : SampleSpace M) (h : valueSystem M v ω = word) :
    forceWord v q word ω = ω := by
  simp [forceWord, h, liftBlock]

theorem forceWord_idempotent (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (ω : SampleSpace M) :
    forceWord v q word (forceWord v q word ω) = forceWord v q word ω :=
  forceWord_fixes v q word _ (forceWord_hits v q hq word ω)

omit [DecidableEq ι] in
theorem forceWord_preserves_nonpivot (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (word : ι → F₂) (ω : SampleSpace M) (p : PrimeUpTo M)
    (hp : ∀ a, p ≠ q a) : forceWord v q word ω p = ω p := by
  simp [forceWord, liftBlock, Finset.sum_apply, hp]

omit [DecidableEq ι] in
theorem forceWord_preserves_small (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (word : ι → F₂) (ω : SampleSpace M) (Y : ℕ)
    (hqY : ∀ a, Y < (q a).val.val) (p : PrimeUpTo M) (hp : p.val.val ≤ Y) :
    forceWord v q word ω p = ω p := by
  apply forceWord_preserves_nonpivot
  intro a he
  have := hqY a
  rw [← he] at this
  omega

omit [DecidableEq ι] in
theorem forceWord_preserves_value (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (word : ι → F₂) (ω : SampleSpace M) (n : ℕ)
    (hn : ∀ a, ¬(q a).val.val ∣ n) :
    valueBit (forceWord v q word ω) n = valueBit ω n := by
  change valueLinear M n (ω + liftBlock q _) = valueLinear M n ω
  rw [map_add]
  suffices h : valueLinear M n (liftBlock q (word - valueSystem M v ω)) = 0 by
    rw [h, add_zero]
  simp only [liftBlock, map_sum, map_smul, valueLinear_apply, valueBit_prime_basis]
  simp [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd (hn _)]

def directedFootprint (G : Finset ℕ) (Q : ℕ) (q : ι → PrimeUpTo M) : Finset ℕ :=
  G.filter fun k ↦ ∃ a, ∃ b : Fin (Q + 1), (q a).val.val ∣ k + b.val

omit [DecidableEq ι] in
theorem forceWord_outside_footprint (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (word : ι → F₂) (ω : SampleSpace M) (G : Finset ℕ) (Q k : ℕ)
    (hk : k ∈ G) (hout : k ∉ directedFootprint G Q q) (b : Fin (Q + 1)) :
    valueBit (forceWord v q word ω) (k + b.val) = valueBit ω (k + b.val) := by
  apply forceWord_preserves_value
  intro a ha
  exact hout (Finset.mem_filter.mpr ⟨hk, ⟨a, b, ha⟩⟩)

def assemble (q : ι → PrimeUpTo M) (r : SampleSpace M) (c : ι → F₂) : SampleSpace M :=
  r + liftBlock q c

theorem assemble_word_iff (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (r : SampleSpace M) (c : ι → F₂) :
    valueSystem M v (assemble q r c) = word ↔ c = word - valueSystem M v r := by
  rw [assemble, map_add, value_liftBlock v q hq]
  constructor <;> intro h
  · rw [← h]
    abel
  · rw [h]
    abel

theorem forceWord_assemble (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (r : SampleSpace M) (c : ι → F₂) :
    forceWord v q word (assemble q r c) = assemble q r (word - valueSystem M v r) := by
  simp only [forceWord, assemble, map_add, value_liftBlock v q hq]
  rw [add_assoc, ← liftBlock_add]
  congr 2
  abel

theorem exact_prime_conditional_expectation (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (μ : FiniteProbability (SampleSpace M)) (f : SampleSpace M → ℝ) :
    finiteExpectation μ.weight (fun r ↦ average (fun c ↦
      f (forceWord v q word (assemble q r c)))) =
    finiteExpectation μ.weight (fun r ↦ average (fun c ↦
      if valueSystem M v (assemble q r c) = word then f (assemble q r c) else 0)) /
        (Fintype.card (ι → F₂) : ℝ)⁻¹ := by
  have h := PrivateCoordinateForcing.exact_conditional_expectation μ
    (fun r ↦ word - valueSystem M v r) (fun z ↦ f (assemble q z.1 z.2))
  simp only [PrivateCoordinateForcing.force, forceWord_assemble v q hq,
    assemble_word_iff v q hq] at h ⊢
  exact h

theorem uniform_assemble_expectation (q : ι → PrimeUpTo M) (f : SampleSpace M → ℝ) :
    average (fun r ↦ average (fun c ↦ f (assemble q r c))) = average f := by
  have hs (c : ι → F₂) : average (fun r ↦ f (assemble q r c)) = average f :=
    UniformFubini.equiv (Equiv.addRight (liftBlock q c)) f
  have hc : average (fun r ↦ average (fun c ↦ f (assemble q r c))) =
      average (fun c ↦ average (fun r ↦ f (assemble q r c))) := by
    calc
      _ = average (fun z : SampleSpace M × (ι → F₂) ↦ f (assemble q z.1 z.2)) :=
        (UniformFubini.product _).symm
      _ = average (fun z : (ι → F₂) × SampleSpace M ↦ f (assemble q z.2 z.1)) :=
        UniformFubini.equiv (Equiv.prodComm (SampleSpace M) (ι → F₂))
          (fun z : (ι → F₂) × SampleSpace M ↦ f (assemble q z.2 z.1))
      _ = _ := UniformFubini.product _
  rw [hc]
  simp_rw [hs]
  exact constant _

theorem uniform_conditional_expectation (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (word : ι → F₂) (f : SampleSpace M → ℝ) :
    average (fun ω ↦ f (forceWord v q word ω)) =
      average (fun ω ↦ if valueSystem M v ω = word then f ω else 0) /
        (Fintype.card (ι → F₂) : ℝ)⁻¹ := by
  have h := exact_prime_conditional_expectation v q hq word
    (uniformFiniteProbability (SampleSpace M)) f
  change average (fun r ↦ average (fun c ↦ f (forceWord v q word (assemble q r c)))) =
    average (fun r ↦ average (fun c ↦
      if valueSystem M v (assemble q r c) = word then f (assemble q r c) else 0)) / _ at h
  rw [uniform_assemble_expectation q (fun ω ↦ f (forceWord v q word ω)),
    uniform_assemble_expectation q (fun ω ↦ if valueSystem M v ω = word then f ω else 0)] at h
  exact h

theorem actual_window_forced {j B : ℕ} (hj : 0 < j) (hM : j + B ≤ M + 1)
    (h1 : ∀ a : Fin B, 1 < OddPrimePivot.largestOddPrime (j + a.val))
    (hB : ∀ a : Fin B, B ≤ OddPrimePivot.largestOddPrime (j + a.val))
    (word : Fin B → F₂) (ω : SampleSpace M) :
    valueSystem M (fun a : Fin B ↦ j + a.val)
      (forceWord (fun a : Fin B ↦ j + a.val) (cylinderPivot hj hM h1) word ω) = word :=
  forceWord_hits _ _ (cylinderPivot_basis hj hM h1 hB) word ω

end PaperP1.PrivatePrimeForcing
