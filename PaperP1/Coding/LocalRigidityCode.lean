module

public import PaperP1.Coding.GriesmerBound
public import PaperP1.Coding.LocalDefectBound
public import PaperP1.Arithmetic.PrivateWindowPrimes
public import Mathlib.NumberTheory.PrimeCounting

/-!
# The finite Griesmer obstruction for a window

The defect coordinates are the actual `B`-defective integers in
`[U,U+B-1]`. Their augmented parity code has redundancy at most `pi(B)+1`.
The proved split-product theorem supplies the exact distance
`ceil (log U / log (64B))`, with no asymptotic prime estimate.
-/

@[expose] public noncomputable section

namespace PaperP1.LocalRigidityCode

open PaperP1.Arithmetic Finset LocalDefectBound DefectivePredicate

local instance localRigidityPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

/-- The finite small-prime count is exactly the usual inclusive function pi. -/
theorem primeCount_eq_primeCounting (B : ℕ) : primeCount B = Nat.primeCounting B := by
  simp only [primeCount, DefectCounting.smallPrimesUpTo, Nat.primeCounting,
    Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- The actual defective values in a window of `B` consecutive integers. -/
def defectValues (U B : ℕ) : Finset ℕ := defectsInInterval B U (B - 1)

def defectEnum (U B : ℕ) (i : Fin (defectValues U B).card) : ℕ :=
  ((defectValues U B).equivFin.symm i).val

theorem defectEnum_mem (U B : ℕ) (i : Fin (defectValues U B).card) :
    defectEnum U B i ∈ defectValues U B :=
  ((defectValues U B).equivFin.symm i).property

theorem defectEnum_bounds (U B : ℕ) (i : Fin (defectValues U B).card) :
    U ≤ defectEnum U B i ∧ defectEnum U B i ≤ U + (B - 1) ∧
      HDefective B (defectEnum U B i) :=
  mem_defectsInInterval.mp (defectEnum_mem U B i)

theorem defectEnum_injective (U B : ℕ) : Function.Injective (defectEnum U B) := by
  intro i j h
  apply (defectValues U B).equivFin.symm.injective
  exact Subtype.ext h

/-- The concrete finite matrix of small-prime parities with its evenness row. -/
def defectCode (U B : ℕ) :
    Submodule F₂ (Fin (defectValues U B).card → F₂) :=
  LinearMap.ker (DefectCodeRank.augmentedParityMap (smallPrime B) (defectEnum U B))

/-- Exact lower distance used in the manuscript, with a natural-number ceiling. -/
def rungeDistance (U B : ℕ) : ℕ := ⌈Real.log U / Real.log (64 * (B : ℝ))⌉₊

theorem rungeDistance_pos {U B : ℕ} (hB : 1 ≤ B) (hU : 2 * B ≤ U) :
    0 < rungeDistance U B := by
  apply Nat.ceil_pos.mpr
  apply div_pos
  · exact Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  · apply Real.log_pos
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith

/-- T1.1 gives the minimum distance for any covered augmented parity matrix. -/
theorem augmented_code_minWeight_of_runge
    {m r U R : ℕ} (hR : 1 ≤ R) (hU : 2 * R ≤ U)
    (primes : Fin r → ℕ) (f : Fin m → ℕ)
    (hf0 : ∀ i, f i ≠ 0)
    (hcover : ∀ i p, parityVec (f i) p ≠ 0 → ∃ j, primes j = p)
    (hinj : Function.Injective f)
    (hlo : ∀ i, U ≤ f i) (hhi : ∀ i, f i ≤ U + R) :
    BinaryResidual.MinWeightAtLeast
      (LinearMap.ker (DefectCodeRank.augmentedParityMap primes f))
      (rungeDistance U R) := by
  intro c hc
  let x : Fin m → F₂ := c
  have hx0 : x ≠ 0 := by
    intro h
    exact hc (Subtype.ext h)
  obtain ⟨k, hk, hcard⟩ := DefectCodeRunge.kernelWord_support_card_eq_two_mul
    primes f x c.property hx0
  have hinput := DefectCodeRunge.kernelWord_translatedRungeInput primes f
    hf0 hcover hinj hlo hhi x c.property
  obtain ⟨γ, hγinj, hγbound, a, ha⟩ :=
    DefectCodeDistance.reindex_translatedRungeInput
      (fun i : HammingBound.wordSupport x ↦ f i) hcard
      hinput.1 hinput.2.1 hinput.2.2
  have hb := SplitProductBound.uniform_split_product hk hR hU γ hγbound hγinj a ha
  have hUpos : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  have hlog : Real.log U ≤ (2 * k : ℝ) * Real.log (64 * (R : ℝ)) := by
    have hr := Real.log_le_log hUpos (show (U : ℝ) ≤ ((64 * R) ^ (2 * k) : ℕ) by
      exact_mod_cast hb)
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using hr
  have hlogpos : 0 < Real.log (64 * (R : ℝ)) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hd : rungeDistance U R ≤ 2 * k := by
    apply Nat.ceil_le.mpr
    rw [div_le_iff₀ hlogpos]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlog
  have hw : hammingNorm x = 2 * k := by
    rw [← HammingBound.card_wordSupport]
    exact hcard
  change rungeDistance U R ≤ hammingNorm x
  rw [hw]
  exact hd

theorem defectCode_minWeight {U B : ℕ} (hB : 1 ≤ B) (hU : 2 * B ≤ U) :
    BinaryResidual.MinWeightAtLeast (defectCode U B) (rungeDistance U B) := by
  apply augmented_code_minWeight_of_runge hB hU
    (smallPrime B) (defectEnum U B)
  · intro i
    have := (defectEnum_bounds U B i).1
    omega
  · intro i p hp
    have hpprime := DefectParitySupport.prime_of_parityVec_ne_zero hp
    apply smallPrime_covers hpprime
    exact (hDefective_iff_parity_support_le _ _).mp
      (defectEnum_bounds U B i).2.2 p hpprime hp
  · exact defectEnum_injective U B
  · intro i
    exact (defectEnum_bounds U B i).1
  · intro i
    have := (defectEnum_bounds U B i).2.1
    omega

theorem defectCode_redundancy (U B : ℕ) :
    (defectValues U B).card - Module.finrank F₂ (defectCode U B) ≤ primeCount B + 1 := by
  have h := DefectCodeRank.defectCode_finrank_ge (smallPrime B) (defectEnum U B)
  change (defectValues U B).card - (primeCount B + 1) ≤
    Module.finrank F₂ (defectCode U B) at h
  omega

/-- The exact finite numerical obstruction for the actual defect code. -/
theorem defectCode_griesmer {U B t : ℕ} (hB : 1 ≤ B) (hU : 2 * B ≤ U)
    (ht : t ≤ Module.finrank F₂ (defectCode U B)) :
    (∑ i ∈ Finset.range t, ⌈(rungeDistance U B : ℝ) / (2 : ℝ) ^ i⌉₊) - t ≤
      primeCount B + 1 := by
  have h := GriesmerBound.griesmer_redundancy_ceil (defectCode U B)
    (rungeDistance_pos hB hU) (defectCode_minWeight hB hU) ht
  simp only [Fintype.card_fin] at h
  exact h.trans (defectCode_redundancy U B)

end PaperP1.LocalRigidityCode
