module

public import PaperP1.Arithmetic.TernaryIndividualPrimes
public import PaperP1.Combinatorics.FiniteFactorTopProducts
public import PaperP1.Arithmetic.CRTProductCover
public import PaperP1.Arithmetic.TernaryCutoffMonotonicity

/-! # Actual largest individual-prime products and their CRT certificates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPrimeTopProducts

open Finset PaperP1.TernaryPrimeGroups PaperP1.TernaryIndividualPrimes
  PaperP1.FiniteEvenSquareClasses

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def topProduct (U : Fin 3 → Finset ℕ) (H k : ℕ) : ℕ := FiniteFactorTopProducts.maximum (pool U H) k

theorem top_product_le_height (U : Fin 3 → Finset ℕ) (H k A : ℕ)
    (hpos : ∀ i, ∀ n ∈ U i, 0 < n) (hmax : ∀ i, ∀ n ∈ U i, n ≤ A) :
    topProduct U H k ≤ A ^ k := by
  apply Finset.sup_le
  intro P hP
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hP
  calc
    _ ≤ ∏ _p ∈ P, A := by
      apply prod_le_prod
      intro p hp
      obtain ⟨u, hu, hpu⟩ := (TernaryIndividualPrimes.mem_pool U H p).mp (hsub hp)
      have hum := (mem_supportPool U u).mp hu
      exact (Nat.le_of_dvd (hpos 0 (u 0) (hum 0)) (prime_dvd_value hpu 0)).trans (hmax 0 (u 0) (hum 0))
    _ = _ := by rw [prod_const, hcard]

theorem cutoff_mono (U : Fin 3 → Finset ℕ) (k : ℕ) {h H : ℕ} (hle : h ≤ H) :
    topProduct U H k ≤ topProduct U h k := by
  apply FiniteFactorTopProducts.mono
  intro p hp
  obtain ⟨u, hu, hpu⟩ := mem_biUnion.mp hp
  exact mem_biUnion.mpr ⟨u, hu, TernaryCutoffMonotonicity.primes_mono u hle hpu⟩

theorem large_three_le_groups {U : Fin 3 → Finset ℕ} {A H : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hpos : ∀ i, ∀ n ∈ U i, 0 < n) (hmax : ∀ i, ∀ n ∈ U i, n ≤ A)
    (hinj : ∀ i, Function.Injective (data (U i)))
    (hdirect : Pairwise (fun i j ↦ Disjoint (space (U i)) (space (U j))))
    (hlarge : 2 * A * (H + 1) < topProduct U H 3) :
    topProduct U H 3 ≤ TernaryTopProducts.topProduct U H 3 := by
  have hp : 0 < topProduct U H 3 := lt_of_le_of_lt (Nat.zero_le _) hlarge
  obtain ⟨P, hP, hcard, hprod⟩ := FiniteFactorTopProducts.attained (pool U H) 3 hp
  change topProduct U H 3 = P.prod id at hprod
  rw [hprod] at hlarge ⊢
  exact three_primes_le_top_groups hwidth hpos hmax hinj hdirect P hP hcard hlarge

theorem top_product_certificate {U : Fin 3 → Finset ℕ} {H k R : ℕ}
    (X : Fin 3 → ℕ) (hp : 0 < topProduct U H k)
    (hoff : ∀ i, ∀ n ∈ U i, ((n : ℤ) - X i).natAbs ≤ R)
    (base : Fin 3 → ℕ) (N : ℕ) (hX : ∀ i, X i ∈ Ico (base i) (base i + N)) :
    X ∈ CRTProductCover.productCentres k 3 base N R (topProduct U H k) := by
  classical
  obtain ⟨P, hP, hcard, hprod⟩ := FiniteFactorTopProducts.attained (pool U H) k hp
  change topProduct U H k = P.prod id at hprod
  let e : Fin k ≃ P := (Finset.equivFinOfCardEq hcard).symm
  let q : Fin k → ℕ := fun j ↦ (e j).val
  have hdata (j : Fin k) : ∃ u ∈ supportPool U, q j ∈ primes H u :=
    (TernaryIndividualPrimes.mem_pool U H (q j)).mp (hP (e j).property)
  choose v hv hq using hdata
  let w : Fin k → Fin 3 → ℤ := fun j i ↦ (v j i : ℤ) - X i
  have hQ : (∏ j, q j) = topProduct U H k := by
    exact ((e.prod_comp (fun p : P ↦ p.val)).trans (prod_coe_sort P id)).trans hprod.symm
  apply (CRTProductCover.mem_productCentres k 3 base N R _ hp X).mpr
  refine ⟨hX, q, w, hQ, ?_, ?_, ?_⟩
  · intro j i
    exact hoff i (v j i) ((mem_supportPool U (v j)).mp (hv j) i)
  · intro i j hij
    apply (Nat.coprime_primes (TernaryPrimeGroups.prime_of_mem (hq i)) (TernaryPrimeGroups.prime_of_mem (hq j))).mpr
    intro heq
    exact hij (e.injective (Subtype.ext heq))
  · intro j i
    have heq : (X i : ℤ) + w j i = (v j i : ℤ) := by dsimp [w]; ring
    rw [heq]
    exact Int.natCast_dvd_natCast.mpr (prime_dvd_value (hq j) i)

end PaperP1.TernaryPrimeTopProducts
