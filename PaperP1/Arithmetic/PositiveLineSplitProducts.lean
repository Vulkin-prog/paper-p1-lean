module

public import PaperP1.Arithmetic.PositiveSplitProducts

/-! # Integer scaling of split products on a rational line of positive slope -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveLineSplitProducts

open Finset PaperP1.LinearKernelFibres

def shifted (a b : ℕ) (c : ℤ) (P Q : Finset ℤ) : Finset ℤ :=
  P.image (fun u ↦ (a : ℤ) * u) ∪ Q.image (fun v ↦ c + (b : ℤ) * v)

def scale (a b : ℕ) (P Q : Finset ℤ) : ℤ := (a : ℤ) ^ P.card * (b : ℤ) ^ Q.card

theorem left_injective {a : ℕ} (ha : 0 < a) : Function.Injective (fun u : ℤ ↦ (a : ℤ) * u) :=
  fun _ _ hh ↦ mul_left_cancel₀ (by exact_mod_cast ha.ne') hh

theorem right_injective {b : ℕ} (hb : 0 < b) (c : ℤ) :
    Function.Injective (fun v : ℤ ↦ c + (b : ℤ) * v) :=
  fun _ _ hh ↦ mul_left_cancel₀ (by exact_mod_cast hb.ne') (add_left_cancel hh)

theorem factor_left (a x : ℕ) (u : ℤ) : ((a * x : ℕ) : ℤ) + (a : ℤ) * u = (a : ℤ) * ((x : ℤ) + u) := by
  push_cast
  ring

theorem factor_right (a b x y : ℕ) (c v : ℤ) (hline : (b : ℤ) * y = (a : ℤ) * x + c) :
    ((a * x : ℕ) : ℤ) + (c + (b : ℤ) * v) = (b : ℤ) * ((y : ℤ) + v) := by
  push_cast
  linear_combination -hline

theorem shifted_card {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (c : ℤ) (P Q : Finset ℤ)
    (hdisj : Disjoint (P.image fun u ↦ (a : ℤ) * u) (Q.image fun v ↦ c + (b : ℤ) * v)) :
    (shifted a b c P Q).card = P.card + Q.card := by
  rw [shifted, card_union_of_disjoint hdisj,
    card_image_of_injective P (left_injective ha), card_image_of_injective Q (right_injective hb c)]

theorem scale_ne_zero {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (P Q : Finset ℤ) : scale a b P Q ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ha.ne')) (pow_ne_zero _ (by exact_mod_cast hb.ne'))

theorem product_identity {a b x y : ℕ} (ha : 0 < a) (hb : 0 < b) (c : ℤ) (P Q : Finset ℤ)
    (hline : (b : ℤ) * y = (a : ℤ) * x + c)
    (hdisj : Disjoint (P.image fun u ↦ (a : ℤ) * u) (Q.image fun v ↦ c + (b : ℤ) * v)) :
    (∏ t ∈ shifted a b c P Q, (((a * x : ℕ) : ℤ) + t)) =
      scale a b P Q * ((∏ u ∈ P, ((x : ℤ) + u)) * (∏ v ∈ Q, ((y : ℤ) + v))) := by
  rw [shifted, prod_union hdisj, prod_image (left_injective ha).injOn, prod_image (right_injective hb c).injOn]
  simp_rw [factor_left, factor_right a b x y c _ hline]
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const]
  unfold scale
  ring

theorem square_transfer {a b x y : ℕ} (ha : 0 < a) (hb : 0 < b) (c D : ℤ) (P Q : Finset ℤ)
    (hline : (b : ℤ) * y = (a : ℤ) * x + c)
    (hdisj : Disjoint (P.image fun u ↦ (a : ℤ) * u) (Q.image fun v ↦ c + (b : ℤ) * v))
    (hsquare : IsSquare (D * ((∏ u ∈ P, ((x : ℤ) + u)) * (∏ v ∈ Q, ((y : ℤ) + v))))) :
    IsSquare ((D * scale a b P Q) * ∏ t ∈ shifted a b c P Q, (((a * x : ℕ) : ℤ) + t)) := by
  obtain ⟨w, hw⟩ := hsquare
  refine ⟨scale a b P Q * w, ?_⟩
  rw [product_identity ha hb c P Q hline hdisj]
  calc
    _ = (scale a b P Q * scale a b P Q) *
        (D * ((∏ u ∈ P, ((x : ℤ) + u)) * (∏ v ∈ Q, ((y : ℤ) + v)))) := by ring
    _ = _ := by rw [hw]; ring

theorem value_left (a x : ℕ) (u : ℤ) : value (a * x) ((a : ℤ) * u) = a * value x u := by
  unfold value
  rw [factor_left, Int.natAbs_mul, Int.natAbs_natCast]

theorem value_right (a b x y : ℕ) (c v : ℤ) (hline : (b : ℤ) * y = (a : ℤ) * x + c) :
    value (a * x) (c + (b : ℤ) * v) = b * value y v := by
  unfold value
  rw [factor_right a b x y c v hline, Int.natAbs_mul, Int.natAbs_natCast]

end PaperP1.PositiveLineSplitProducts
