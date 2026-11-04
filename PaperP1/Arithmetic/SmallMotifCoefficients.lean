module

public import PaperP1.Arithmetic.SmoothMotifCodes
public import PaperP1.Arithmetic.SourceSupportedCoefficientPool
public import PaperP1.Arithmetic.FixedSourceCertificate
public import PaperP1.Arithmetic.CoefficientSplitRadicalPatterns
public import PaperP1.Arithmetic.SplitRadicalPointHeight

/-! # A fixed third window supplies the common coefficients of small motifs

The coefficient is its actual third-block product times the actual small-prime
code. Its common finite pool depends only on the fixed third centre, never on
either variable centre or on the cover that supplied the motif.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallMotifCoefficients

open Finset PaperP1.Arithmetic PaperP1.TransverseMotifs PaperP1.SmoothMotifCodes
  PaperP1.PositiveLineOffsetRoots PaperP1.SplitRadicalPointHeight

def sourceSupport {L : ℕ} (I : Finset (Fin (L + 1))) : Finset (Fin 1 × Fin (L + 1)) :=
  I.image (fun u ↦ (0, u))

def pool (z L H : ℕ) : Finset ℕ :=
  SourceSupportedCoefficientPool.pool
    (FixedSourceCertificate.sourceValues (fun _ : Fin 1 ↦ z) (L + 1)) H 5

def coefficient {L : ℕ} (X : Fin 3 → ℕ) (E : Finset (Vertex L)) : ℕ :=
  SmoothMotifCodes.coefficient X E * ∏ u ∈ offsets E 2, SaturationPrimes.value (X 2) u

theorem source_card {L : ℕ} (I : Finset (Fin (L + 1))) :
    (sourceSupport I).card = I.card := card_image_of_injective _ (fun _ _ hh ↦ congrArg Prod.snd hh)

theorem source_product {L : ℕ} (z : ℕ) (I : Finset (Fin (L + 1))) :
    (sourceSupport I).prod (FixedSourceCertificate.sourceValues (fun _ : Fin 1 ↦ z) (L + 1)) =
      ∏ u ∈ I, SaturationPrimes.value z u := by
  rw [sourceSupport, prod_image (fun _ _ _ _ hh ↦ congrArg Prod.snd hh)]
  rfl

theorem coefficient_pos {L : ℕ} (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i) (E : Finset (Vertex L)) :
    0 < coefficient X E := by
  apply Nat.mul_pos (SmoothMotifCodes.coefficient_pos X E)
  apply prod_pos
  intro u _hu
  have hh := hX 2
  dsimp [SaturationPrimes.value]
  omega

theorem coefficient_mem {L H : ℕ} (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i)
    (E : Finset (Vertex L)) (hsize : E.card ≤ 5) (hE : SquareOutside H X E) :
    coefficient X E ∈ pool (X 2) L H := by
  let I := offsets E 2
  let A := sourceSupport I
  have hA : A.card ≤ 5 := by
    rw [source_card]
    have hh := card_decomposition E
    dsimp only [I]
    omega
  have hprod : 0 < A.prod (FixedSourceCertificate.sourceValues (fun _ : Fin 1 ↦ X 2) (L + 1)) := by
    rw [source_product]
    apply prod_pos
    intro u _hu
    have hh := hX 2
    dsimp [SaturationPrimes.value]
    omega
  have hcode : SmoothMotifCodes.coefficient X E ∣ primorial H := by
    have hsub := mem_powerset.mp (code_mem_pool X E hE)
    have heq : primorial H = (DefectCounting.smallPrimesUpTo H).prod id := by
      rfl
    rw [heq]
    exact prod_dvd_prod_of_subset _ _ id hsub
  apply mem_biUnion.mpr
  refine ⟨A, (SourceSupportedCoefficientPool.mem_positions 5 A).mpr hA, mem_image.mpr ?_⟩
  refine ⟨(SmoothMotifCodes.coefficient X E,
    A.prod (FixedSourceCertificate.sourceValues (fun _ : Fin 1 ↦ X 2) (L + 1))),
    mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hcode, (primorial_pos H).ne'⟩,
      Nat.mem_divisors.mpr ⟨dvd_refl _, hprod.ne'⟩⟩, ?_⟩
  rw [source_product]
  rfl

theorem integer_product {L : ℕ} (I : Finset (Fin (L + 1))) (x : ℤ) :
    integerProduct (integerOffsets I) x = ∏ u ∈ I, (x + integerOffset u) := by
  rw [integerProduct, integerOffsets, prod_image (integerOffset_injective L).injOn]

theorem product_cast {L : ℕ} (z : ℕ) (hz : 2 ≤ z) (I : Finset (Fin (L + 1))) :
    ((∏ u ∈ I, SaturationPrimes.value z u : ℕ) : ℤ) = ∏ u ∈ I, ((z : ℤ) + integerOffset u) := by
  rw [Nat.cast_prod]
  apply prod_congr rfl
  intro u _hu
  exact FixedSourceCertificate.offset_value z L (by omega) u

theorem square {L : ℕ} (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i) (E : Finset (Vertex L)) :
    IsSquare ((coefficient X E : ℤ) * integerProduct (integerOffsets (offsets E 0)) (X 0) *
      integerProduct (integerOffsets (offsets E 1)) (X 1)) := by
  have he : (coefficient X E : ℤ) * integerProduct (integerOffsets (offsets E 0)) (X 0) *
      integerProduct (integerOffsets (offsets E 1)) (X 1) =
      (SmoothMotifCodes.coefficient X E : ℤ) *
        ((∏ u ∈ offsets E 0, ((X 0 : ℤ) + integerOffset u)) *
         (∏ u ∈ offsets E 1, ((X 1 : ℤ) + integerOffset u)) *
         (∏ u ∈ offsets E 2, ((X 2 : ℤ) + integerOffset u))) := by
    rw [coefficient, Nat.cast_mul, product_cast (X 2) (hX 2), integer_product, integer_product]
    ring
  rw [he]
  exact square_prescription X hX E

end PaperP1.SmallMotifCoefficients
