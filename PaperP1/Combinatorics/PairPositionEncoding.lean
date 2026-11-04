module

public import PaperP1.Combinatorics.FiniteFamilyEnumeration
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Nodup

/-! # A pair in two chosen positions and its chronological remaining coordinates

The complementary positions are enumerated increasingly. A reverse chronological
branch path is reversed before its coordinates are placed there.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairPositionEncoding

open Finset PaperP1.FiniteFamilyEnumeration

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem complement_card {k : ℕ} (P : Finset (Fin (k + 2))) (hP : P.card = 2) : Pᶜ.card = k := by
  rw [card_compl, Fintype.card_fin, hP]
  omega

def tail {k : ℕ} (xs : List ℕ) (hlen : xs.length = k) : Fin k → ℕ :=
  fun i ↦ xs.reverse.get ⟨i.val, by simpa only [List.length_reverse, hlen] using i.isLt⟩

theorem tail_mem {k : ℕ} (xs : List ℕ) (hlen : xs.length = k) (i : Fin k) :
    tail xs hlen i ∈ xs.toFinset := by
  apply List.mem_toFinset.mpr
  have hh := xs.reverse.get_mem ⟨i.val, by simpa only [List.length_reverse, hlen] using i.isLt⟩
  simpa only [List.mem_reverse, tail] using hh

theorem tail_support {k : ℕ} (xs : List ℕ) (hlen : xs.length = k) : tupleSet (tail xs hlen) = xs.toFinset := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp hx
    exact tail_mem xs hlen i
  · intro x hx
    have hm : x ∈ xs.reverse := by simpa only [List.mem_reverse] using List.mem_toFinset.mp hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    refine mem_image.mpr ⟨⟨i.val, by simpa only [List.length_reverse, hlen] using i.isLt⟩, mem_univ _, ?_⟩
    exact hi

theorem tail_eq {k : ℕ} (xs ys : List ℕ) (hx : xs.length = k) (hy : ys.length = k)
    (heq : tail xs hx = tail ys hy) : xs = ys := by
  apply List.reverse_injective
  apply List.ext_getElem (by simp only [List.length_reverse, hx, hy])
  intro n hnx _hny
  have hn : n < k := by simpa only [List.length_reverse, hx] using hnx
  exact congrFun heq ⟨n, hn⟩

def place {k : ℕ} (P : Finset (Fin (k + 2))) (hP : P.card = 2)
    (source : Fin 2 → ℕ) (xs : List ℕ) (hlen : xs.length = k) : Fin (k + 2) → ℕ := fun j ↦
  if hj : j ∈ P then source ((P.orderIsoOfFin hP).symm ⟨j, hj⟩)
  else tail xs hlen ((Pᶜ.orderIsoOfFin (complement_card P hP)).symm ⟨j, mem_compl.mpr hj⟩)

theorem source_value {k : ℕ} (P : Finset (Fin (k + 2))) (hP : P.card = 2)
    (source : Fin 2 → ℕ) (xs : List ℕ) (hlen : xs.length = k) (i : Fin 2) :
    place P hP source xs hlen (P.orderEmbOfFin hP i) = source i := by
  rw [place, dite_eq_left (P.orderEmbOfFin_mem hP i)]
  change source ((P.orderIsoOfFin hP).symm ((P.orderIsoOfFin hP) i)) = source i
  rw [OrderIso.symm_apply_apply]

theorem tail_value {k : ℕ} (P : Finset (Fin (k + 2))) (hP : P.card = 2)
    (source : Fin 2 → ℕ) (xs : List ℕ) (hlen : xs.length = k) (i : Fin k) :
    place P hP source xs hlen (Pᶜ.orderEmbOfFin (complement_card P hP) i) = tail xs hlen i := by
  rw [place, dite_eq_right (mem_compl.mp (Pᶜ.orderEmbOfFin_mem (complement_card P hP) i))]
  change tail xs hlen ((Pᶜ.orderIsoOfFin (complement_card P hP)).symm
    ((Pᶜ.orderIsoOfFin (complement_card P hP)) i)) = tail xs hlen i
  rw [OrderIso.symm_apply_apply]

theorem source_image {k : ℕ} (P : Finset (Fin (k + 2))) (hP : P.card = 2)
    (source : Fin 2 → ℕ) (xs : List ℕ) (hlen : xs.length = k) :
    P.image (place P hP source xs hlen) = tupleSet source := by
  calc
    _ = (univ.image (P.orderEmbOfFin hP)).image (place P hP source xs hlen) :=
      congrArg (fun Q : Finset (Fin (k + 2)) ↦ Q.image (place P hP source xs hlen))
        (P.image_orderEmbOfFin_univ hP).symm
    _ = _ := by
      rw [image_image]
      exact image_congr fun i _ ↦ source_value P hP source xs hlen i

theorem tail_image {k : ℕ} (P : Finset (Fin (k + 2))) (hP : P.card = 2)
    (source : Fin 2 → ℕ) (xs : List ℕ) (hlen : xs.length = k) :
    Pᶜ.image (place P hP source xs hlen) = xs.toFinset := by
  rw [← Pᶜ.image_orderEmbOfFin_univ (complement_card P hP), image_image, ← tail_support xs hlen]
  exact image_congr fun i _ ↦ tail_value P hP source xs hlen i

theorem support {k : ℕ} (P : Finset (Fin (k + 2))) (hP : P.card = 2)
    (source : Fin 2 → ℕ) (xs : List ℕ) (hlen : xs.length = k) :
    tupleSet (place P hP source xs hlen) = tupleSet source ∪ xs.toFinset := by
  have hh := congrArg (fun Q : Finset (Fin (k + 2)) ↦ Q.image (place P hP source xs hlen)) (union_compl P)
  rw [image_union, source_image, tail_image] at hh
  exact hh.symm

theorem injective {k : ℕ} (P : Finset (Fin (k + 2))) (hP : P.card = 2)
    (source : Fin 2 → ℕ) (hs : Function.Injective source) (xs : List ℕ) (hlen : xs.length = k)
    (hnodup : xs.Nodup) (hdis : Disjoint (tupleSet source) xs.toFinset) :
    Function.Injective (place P hP source xs hlen) := by
  have hsource : (tupleSet source).card = 2 := by
    rw [tupleSet, card_image_of_injective _ hs, card_univ, Fintype.card_fin]
  have hc : (univ.image (place P hP source xs hlen)).card = (univ : Finset (Fin (k + 2))).card := by
    rw [← tupleSet, support, card_union_of_disjoint hdis, hsource, List.toFinset_card_of_nodup hnodup,
      hlen, card_univ, Fintype.card_fin, Nat.add_comm]
  exact fun i j hij ↦ (card_image_iff.mp hc) (mem_univ i) (mem_univ j) hij

theorem positions_eq {k : ℕ} (P Q : Finset (Fin (k + 2))) (hP : P.card = 2) (hQ : Q.card = 2)
    (source target : Fin 2 → ℕ) (xs ys : List ℕ) (hx : xs.length = k) (hy : ys.length = k)
    (hinj : Function.Injective (place P hP source xs hx)) (hseed : tupleSet source = tupleSet target)
    (heq : place P hP source xs hx = place Q hQ target ys hy) : P = Q := by
  apply (image_inj hinj).mp
  calc
    _ = tupleSet source := source_image P hP source xs hx
    _ = tupleSet target := hseed
    _ = Q.image (place Q hQ target ys hy) := (source_image Q hQ target ys hy).symm
    _ = _ := by rw [heq]

theorem source_eq {k : ℕ} (P : Finset (Fin (k + 2))) (hP : P.card = 2)
    (source target : Fin 2 → ℕ) (xs ys : List ℕ) (hx : xs.length = k) (hy : ys.length = k)
    (heq : place P hP source xs hx = place P hP target ys hy) : source = target := by
  funext i
  have hh := congrFun heq (P.orderEmbOfFin hP i)
  simpa only [source_value] using hh

theorem path_eq {k : ℕ} (P : Finset (Fin (k + 2))) (hP : P.card = 2)
    (source target : Fin 2 → ℕ) (xs ys : List ℕ) (hx : xs.length = k) (hy : ys.length = k)
    (heq : place P hP source xs hx = place P hP target ys hy) : xs = ys := by
  apply tail_eq xs ys hx hy
  funext i
  have hh := congrFun heq (Pᶜ.orderEmbOfFin (complement_card P hP) i)
  simpa only [tail_value] using hh

end PaperP1.PairPositionEncoding
