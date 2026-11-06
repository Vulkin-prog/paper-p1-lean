module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.Hom

/-! # Every ring point over a nonzero ZMod base automatically fixes its scalars -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ZModPointEvaluations

theorem ringHom_scalars (p : ℕ) [NeZero p] (B : Type*) [CommRing B] [Algebra (ZMod p) B]
    (φ : B →+* ZMod p) (r : ZMod p) : φ (algebraMap (ZMod p) B r) = r := by
  calc
    φ (algebraMap (ZMod p) B r) = φ (algebraMap (ZMod p) B (r.val : ZMod p)) := by
      rw [ZMod.natCast_zmod_val]
    _ = φ (r.val : B) := by rw [map_natCast]
    _ = (r.val : ZMod p) := map_natCast φ r.val
    _ = r := ZMod.natCast_zmod_val r

def ringHomEquiv (p : ℕ) [NeZero p] (B : Type*) [CommRing B] [Algebra (ZMod p) B] :
    (B →+* ZMod p) ≃ (B →ₐ[ZMod p] ZMod p) where
  toFun φ := { toRingHom := φ, commutes' := ringHom_scalars p B φ }
  invFun ψ := ψ.toRingHom
  left_inv _ := rfl
  right_inv _ := rfl

end PaperP1.ZModPointEvaluations
