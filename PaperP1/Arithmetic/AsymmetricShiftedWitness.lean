module

public import PaperP1.Arithmetic.AsymmetricEvenLoss
public import PaperP1.Arithmetic.CompressedTargetAlignment

/-! # An exact shifted rational family for checking the asymmetric alignment radius

For L=3k, the old raw interval [x,x+3(L+1)] contains k actual values
matching target values above every prime cutoff H>=3. This test retains
the original, unenlarged definition of alignment as a separate predicate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricShiftedWitness

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.AsymmetricEvenLoss

def width (k : ℕ) : ℕ := 3 * k + 1

def source (t : ℕ) : ℕ := 2 * t

def target (t k : ℕ) : ℕ := 3 * t + 3 * width k

def oldValues (x k : ℕ) : Finset ℕ := Icc x (x + 3 * width k)

def index (k : ℕ) : Fin k ↪ Fin (3 * k + 1) where
  toFun j := ⟨3 * j.val + 1, by have hh := j.isLt; omega⟩
  inj' := by intro i j hh; apply Fin.ext; have he := congrArg Fin.val hh; dsimp at he; omega

def selected (k : ℕ) : Finset (Fin (3 * k + 1)) := univ.map (index k)

theorem selected_card (k : ℕ) : (selected k).card = k := by
  rw [selected, card_map, card_univ, Fintype.card_fin]

theorem source_target_separated (t k : ℕ) : source t + 3 * k < target t k := by
  dsimp [source, target, width]
  omega

theorem old_interval (x k n : ℕ) (hn : n ∈ oldValues x k) :
    ∃ h : ℤ, |h| ≤ (3 * width k : ℕ) ∧ (n : ℤ) = (x : ℤ) + h := by
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
  refine ⟨(n : ℤ) - x, abs_le.mpr ⟨?_, ?_⟩, by ring⟩
  · have hh : (x : ℤ) ≤ n := by exact_mod_cast hlo
    have hz : (0 : ℤ) ≤ (3 * width k : ℕ) := Nat.cast_nonneg _
    omega
  · have hh : (n : ℤ) ≤ (x : ℤ) + ((3 * width k : ℕ) : ℤ) := by exact_mod_cast hhi
    omega

theorem matched_label (t k : ℕ) (j : Fin k) :
    startCompleteVertexLabel (target t k) (3 * k) (index k j) = 3 * (t + width k + j.val) := by
  have hz : 0 < target t k := by dsimp [target, width]; omega
  rw [startCompleteVertexLabel_eq_offset hz]
  dsimp [target, width, index]
  omega

theorem matched_old (t k : ℕ) (j : Fin k) :
    2 * (t + width k + j.val) ∈ oldValues (source t) k := by
  rw [oldValues, mem_Icc]
  have hj := j.isLt
  dsimp [source, width]
  omega

theorem loss_lower {H : ℕ} (hH : 3 ≤ H) (t k : ℕ) :
    k - 1 ≤ loss H (oldValues (source t) k) (target t k) (3 * k) := by
  calc
    k - 1 = (selected k).card - 1 := by rw [selected_card]
    _ ≤ _ := by
      apply AsymmetricEvenLoss.selected_lower
      intro u hu
      obtain ⟨j, _hj, rfl⟩ := mem_map.mp hu
      refine ⟨2 * (t + width k + j.val), matched_old t k j, ?_⟩
      rw [newData, matched_label]
      exact (scaled_two_three hH (by dsimp [width]; omega)).symm

end PaperP1.AsymmetricShiftedWitness
