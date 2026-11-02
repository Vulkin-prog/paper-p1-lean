module

public import PaperP1.Arithmetic.TransverseMotifs
public import PaperP1.Arithmetic.RelativeSquarefreeParts
public import PaperP1.Arithmetic.PositiveLineOffsetRoots
public import PaperP1.Arithmetic.SaturationPrimes

/-! # Literal small-prime codes for the square prescriptions of transverse motifs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothMotifCodes

open Finset PaperP1.Arithmetic PaperP1.TransverseMotifs PaperP1.DefectivePredicate
  PaperP1.DefectCounting PaperP1.PositiveLineOffsetRoots PaperP1.LargeOddKernel

def naturalProduct {L : ℕ} (X : Fin 3 → ℕ) (E : Finset (Vertex L)) : ℕ :=
  ∏ v ∈ E, SaturationPrimes.value (X v.1) v.2

def code {L : ℕ} (X : Fin 3 → ℕ) (E : Finset (Vertex L)) : Finset ℕ := oddPrimeSupport (naturalProduct X E)

def coefficient {L : ℕ} (X : Fin 3 → ℕ) (E : Finset (Vertex L)) : ℕ := (code X E).prod id

def SquareOutside {L : ℕ} (H : ℕ) (X : Fin 3 → ℕ) (E : Finset (Vertex L)) : Prop :=
  ∀ p ∈ code X E, p ≤ H

def codePool (H : ℕ) : Finset (Finset ℕ) := (smallPrimesUpTo H).powerset

theorem product_pos {L : ℕ} (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i) (E : Finset (Vertex L)) :
    0 < naturalProduct X E := by
  apply Finset.prod_pos
  intro v _
  have hh := hX v.1
  unfold SaturationPrimes.value
  omega

theorem product_cast {L : ℕ} (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i) (E : Finset (Vertex L)) :
    (naturalProduct X E : ℤ) =
      (∏ u ∈ offsets E 0, ((X 0 : ℤ) + integerOffset u)) *
      (∏ v ∈ offsets E 1, ((X 1 : ℤ) + integerOffset v)) *
      (∏ w ∈ offsets E 2, ((X 2 : ℤ) + integerOffset w)) := by
  have hfactor (v : Vertex L) : (SaturationPrimes.value (X v.1) v.2 : ℤ) =
      (X v.1 : ℤ) + integerOffset v.2 := by
    have hh := hX v.1
    unfold SaturationPrimes.value integerOffset
    omega
  rw [naturalProduct, Nat.cast_prod]
  simp_rw [hfactor]
  exact product_decomposition E (fun v ↦ (X v.1 : ℤ) + integerOffset v.2)

theorem coefficient_pos {L : ℕ} (X : Fin 3 → ℕ) (E : Finset (Vertex L)) : 0 < coefficient X E :=
  Finset.prod_pos (fun _ hp ↦ (prime_of_mem_oddPrimeSupport hp).pos)

theorem code_mem_pool {L H : ℕ} (X : Fin 3 → ℕ) (E : Finset (Vertex L)) (hE : SquareOutside H X E) :
    code X E ∈ codePool H := by
  apply mem_powerset.mpr
  intro p hp
  exact mem_smallPrimesUpTo.mpr ⟨prime_of_mem_oddPrimeSupport hp, hE p hp⟩

theorem pool_coefficient_pos {H : ℕ} {U : Finset ℕ} (hU : U ∈ codePool H) : 0 < U.prod id := by
  apply Finset.prod_pos
  intro p hp
  exact (mem_smallPrimesUpTo.mp ((mem_powerset.mp hU) hp)).1.pos

theorem square_prescription {L : ℕ} (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i) (E : Finset (Vertex L)) :
    IsSquare ((coefficient X E : ℤ) *
      ((∏ u ∈ offsets E 0, ((X 0 : ℤ) + integerOffset u)) *
       (∏ v ∈ offsets E 1, ((X 1 : ℤ) + integerOffset v)) *
       (∏ w ∈ offsets E 2, ((X 2 : ℤ) + integerOffset w)))) := by
  have hs : IsSquare (coefficient X E * naturalProduct X E) :=
    RelativeSquarefreeParts.kernel_mul_isSquare (product_pos X hX E).ne'
  have hsZ : IsSquare ((coefficient X E : ℤ) * (naturalProduct X E : ℤ)) := by exact_mod_cast hs
  rwa [product_cast X hX E] at hsZ

end PaperP1.SmoothMotifCodes
