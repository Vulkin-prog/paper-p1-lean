module

public import PaperP1.Algebra.GradedVeroneseGrading
public import PaperP1.Algebra.GradedDehomogenizationQuotient

/-! # The actual Veronese chart at b^D is the original homogeneous chart at b

The construction uses the literal dehomogenization maps and clears powers of
the denominator. It applies to arbitrary commutative coefficient algebras,
including rings with zero divisors.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseChart

open HomogeneousLocalization

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (D : ℕ) (hD : 0 < D)
  {b : A} (hb : b ∈ G 1)

def coordinate : GradedVeroneseAlgebra.veronese G D :=
  ⟨b ^ D, GradedVeroneseAlgebra.piece_mem G D 1 (by
    simpa only [one_mul, smul_eq_mul, mul_one] using SetLike.pow_mem_graded D hb)⟩

theorem coordinate_val : (coordinate G D hb : A) = b ^ D := rfl

theorem coordinate_mem : coordinate G D hb ∈ GradedVeroneseGrading.piece G D 1 := by
  change b ^ D ∈ G (1 * D)
  simpa only [one_mul, smul_eq_mul, mul_one] using SetLike.pow_mem_graded D hb

def toChart : GradedVeroneseAlgebra.veronese G D →+* Away G b :=
  (GradedDehomogenization.map G hb).comp (GradedVeroneseAlgebra.veronese G D).val.toRingHom

theorem toChart_coordinate : toChart G D hb (coordinate G D hb) = 1 := by
  change GradedDehomogenization.map G hb (b ^ D) = 1
  rw [map_pow, GradedDehomogenizationQuotient.map_variable G hb, one_pow]

def quotientMap :
    (GradedVeroneseAlgebra.veronese G D) ⧸ GradedDehomogenizationQuotient.ideal (coordinate G D hb) →+*
      Away G b :=
  Ideal.Quotient.lift _ (toChart G D hb) (by
    change GradedDehomogenizationQuotient.ideal (coordinate G D hb) ≤ RingHom.ker (toChart G D hb)
    rw [GradedDehomogenizationQuotient.ideal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    rw [map_sub, map_one, toChart_coordinate G D hb, sub_self])

def map :
    letI := GradedVeroneseGrading.grading G D hD
    Away (GradedVeroneseGrading.piece G D) (coordinate G D hb) →+* Away G b := by
  let := GradedVeroneseGrading.grading G D hD
  exact (quotientMap G D hb).comp
    (GradedDehomogenizationQuotient.equiv (GradedVeroneseGrading.piece G D)
      (coordinate_mem G D hb)).symm.toRingHom

theorem map_dehomogenization (x : GradedVeroneseAlgebra.veronese G D) :
    letI := GradedVeroneseGrading.grading G D hD
    map G D hD hb (GradedDehomogenization.map (GradedVeroneseGrading.piece G D)
      (coordinate_mem G D hb) x) = toChart G D hb x := by
  let := GradedVeroneseGrading.grading G D hD
  rw [map, RingHom.comp_apply, ← GradedDehomogenizationQuotient.equiv_mk]
  change (quotientMap G D hb)
    ((GradedDehomogenizationQuotient.equiv (GradedVeroneseGrading.piece G D)
      (coordinate_mem G D hb)).symm
        ((GradedDehomogenizationQuotient.equiv (GradedVeroneseGrading.piece G D)
          (coordinate_mem G D hb))
            (Ideal.Quotient.mk (GradedDehomogenizationQuotient.ideal (coordinate G D hb)) x))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem map_mk (n : ℕ) (x : GradedVeroneseAlgebra.veronese G D)
    (hx : x ∈ GradedVeroneseGrading.piece G D (n • (1 : ℕ))) :
    letI := GradedVeroneseGrading.grading G D hD
    map G D hD hb (Away.mk (GradedVeroneseGrading.piece G D) (coordinate_mem G D hb) n x hx) =
      Away.mk G hb (n * D) (x : A) (by
        change (x : A) ∈ G ((n • (1 : ℕ)) * D) at hx
        simpa only [smul_eq_mul, mul_one] using hx) := by
  let := GradedVeroneseGrading.grading G D hD
  rw [← GradedDehomogenization.map_homogeneous (GradedVeroneseGrading.piece G D)
    (coordinate_mem G D hb) n x (by simpa only [smul_eq_mul, mul_one] using hx),
    map_dehomogenization G D hD hb]
  exact GradedDehomogenization.map_homogeneous G hb (n * D) x
    (by
      change (x : A) ∈ G ((n • (1 : ℕ)) * D) at hx
      simpa only [smul_eq_mul, mul_one] using hx)

end PaperP1.GradedVeroneseChart
