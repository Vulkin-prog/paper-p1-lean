module

public import PaperP1.Arithmetic.DyadicTargetInterior
public import PaperP1.Arithmetic.FixedChannelGamma
public import PaperP1.Model.RegularStarts

/-! # Interior target fractions from actual dyadic source labels -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.ActualDyadicInterior

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.DyadicTargetInterior

theorem source_parameter_bounds {N L x a t : ℕ} (hN : 0 < N) (hx : x ∈ dyadicBlock N)
    (i : Fin (L + 1)) (hbase : startCompleteVertexLabel x L i = a * t) :
    (N : ℤ) - ((L + 1 : ℕ) : ℤ) ≤ (a : ℤ) * t ∧
      (a : ℤ) * t ≤ 2 * N + ((L + 1 : ℕ) : ℤ) := by
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
  have hxpos : 0 < x := hN.trans_le hxlo
  have hlabel := mem_Ico.mp ((values_eq_interval hxpos).symm ▸ (mem_values.mpr ⟨i, rfl⟩))
  have hlo : N ≤ a * t + (L + 1) := by rw [← hbase]; omega
  have hhi : a * t ≤ 2 * N + (L + 1) := by rw [← hbase]; omega
  have hloZ : (N : ℤ) ≤ (a : ℤ) * t + ((L + 1 : ℕ) : ℤ) := by exact_mod_cast hlo
  exact ⟨by linarith only [hloZ], by exact_mod_cast hhi⟩

theorem parameter_large {N L x a t H : ℕ} (hN : 0 < N) (hx : x ∈ dyadicBlock N)
    (i : Fin (L + 1)) (hbase : startCompleteVertexLabel x L i = a * t)
    (hsize : a * (2 * H * ((L + 1) + 1)) + (L + 1) < N) :
    2 * H * ((L + 1) + 1) < t := by
  have hsource := (source_parameter_bounds hN hx i hbase).1
  have hsourceN : N ≤ a * t + (L + 1) := by
    have h : (N : ℤ) ≤ (a : ℤ) * t + ((L + 1 : ℕ) : ℤ) := by linarith only [hsource]
    exact_mod_cast h
  by_contra hnot
  have ht : t ≤ 2 * H * ((L + 1) + 1) := by omega
  have hmul := Nat.mul_le_mul_left a ht
  omega

theorem ratio_interior {N L x y z a b c d t H : ℕ} {h : ℤ} (hN : 0 < N)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hd : 0 < d) (hdH : d ≤ H) (hh : |h| ≤ H)
    (i j : Fin (L + 1)) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (hbaseY : startCompleteVertexLabel y L j = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hsize : a * (2 * H * ((L + 1) + 1)) + (L + 1) < N)
    (hawayA : ((L + 1 : ℕ) : ℤ) + 2 * H < |(a : ℤ) * t - N|)
    (hawayB : ((L + 1 : ℕ) : ℤ) + 2 * H < |(b : ℤ) * t - 2 * N|) :
    (b : ℚ) / 2 < (c : ℚ) / d ∧ (c : ℚ) / d < 2 * a := by
  have hsrcA := (source_parameter_bounds hN hx i hbaseX).1
  have hsrcB := (source_parameter_bounds hN hy j hbaseY).2
  have ht := parameter_large hN hx i hbaseX hsize
  have hratio := strict_interior_of_no_endpoints hd hsrcA hsrcB (mem_Ico.mp hz).1
    (Nat.le_of_lt (mem_Ico.mp hz).2) hdH hh htarget ht hawayA hawayB
  exact (FixedChannelGamma.ratio_conditions hd).mpr hratio

end PaperP1.ActualDyadicInterior
