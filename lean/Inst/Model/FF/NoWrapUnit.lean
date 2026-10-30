-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/NoWrapUnit.lean: no wrap-around (the term: the head of Inst/Model/FF/NoWrap.lean) in
  a feed-forward segment: the hidden units.

  The gate without its rounding, on all hidden units, and the two roundings, on the units of a dense
  layer and of the shared expert. The work for one hidden unit at one position is done in
  Inst/Model/Common/Unit.lean (`gate_sound`, `unit_sound`). In Cm/TargetInstFFUnit.lean the eight
  looked-up values (keys) of a hidden unit x of layer ℓ at position i are taken from the field
  relation (Inst/Model/FF/Cast.lean: `RFraw`, `key_inLut`), and condition (1) (every valid cell is
  below 2^18 in absolute value) gives the bounds of the seven values.
    `uv`, `small`, `gate`, `keys`
                          the values of a unit; condition (1); the four keys G0, F, CG, UT, which
                          read no accumulator; all eight keys
    `gate_facts`          `Part1.g0`, `ghR`, `gc`, `sl`, `upR` (`Part1`: Inst/Model/FF/Trace.lean)
    `unit_facts`          the whole unit against the program's `UNIT`: see its docstring
    `shared_facts`        `Part1.gwS`, `upS`: the units that are not routed, with the input m
  Here: `uv`, `Sz`, `abs_dot_le`, `acc_le`, `acc_shared`. The others: Cm/TargetInstFFUnit.lean.
  `small`, `gate`, `keys` and the last three are under `RFraw` over `ZMod p` (`Big p`); the last
  three also under `tb.OK` and `Sz`: at most 5,120 channels, and scales whose shifts kg, kg', ku,
  ku' are at most 24 in every layer. (not all hypotheses are named here: see their statements)

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale. (U1) to (U6): `UNIT`, Inst/Model/Program.lean; labels
  such as "Step L7" link docstrings of Cm/TargetInstFFUnit.lean and Inst/Model/Common/Unit.lean.
  Notation, for this file and for Cm/TargetInstFFUnit.lean, whose head points here:
    g0, gh, gc, sl, up, rg, ru: the seven values (`Unit.UnitV`, Inst/Model/Common/Unit.lean): "the
      balanced low byte and the high part of the gate, its clamp, the activation, the up projection,
      and the high digits of the two roundings"; `gw`: "gw = g0 + 256 gh"; `hh`: "hh_j = sl_j up_j"
      (Inst/Model/FF/Trace.lean).
    `Ag`, `Au`: the accumulators: "Ag_x = (m W_g)_x; on the routed expert Ag_(fe+x) = Σ_e sel_e (xr
      W_g^e)_x"; "Au: the same with W_u and W_u^e" (Inst/Model/FF/Trace.lean); m: the array `.m`
      (`Arr`, Inst/Model/FF/Index.lean), named after the program's "(PL8) m = NORM(x')"
      (Inst/Model/Program.lean).
    G0, F, CG, UT, G, GH, U, UH: eight of "The families of keys." (`Fam`, Inst/Model/FF/Index.lean);
      as numbers: `keyG0` .. `keyUH` (Inst/Model/Common/Unit.lean).
    `kG D l x`, `kU D l x`: "the shift of the gate at the hidden unit x", "the shift of the up
      projection at the hidden unit x": kg', ku' at a routed unit, else kg, ku
      (Inst/Model/FF/Trace.lean).
    `rhu a k`: "rhu(a, k) = ⌊(a + 2^(k−1)) / 2^k⌋, the quotient by 2^k rounded to the nearest
      integer, halves up"; k ≥ 1; `lowByte a`: "the balanced low byte of a is ((a + 128) mod 256) −
      128" (Inst/Model/Program.lean).
-/
import Inst.Model.FF.Cast
import Inst.Model.Common.Unit

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset

namespace NWU

/-- what is used of the sizes and the scales -/
structure Sz (D : Dim) : Prop where
  kg : ∀ l, (D.Pl l).kg ≤ 24
  kg' : ∀ l, (D.Pl l).kg' ≤ 24
  ku : ∀ l, (D.Pl l).ku ≤ 24
  ku' : ∀ l, (D.Pl l).ku' ≤ 24
  d : D.d ≤ 5120

theorem Sz.kG {D : Dim} (S : Sz D) (l x : ℕ) : kG D l x ≤ 24 := by
  unfold FFSeg.kG
  split_ifs
  · exact (S.kg' _)
  · exact (S.kg _)

theorem Sz.kU {D : Dim} (S : Sz D) (l x : ℕ) : kU D l x ≤ 24 := by
  unfold FFSeg.kU
  split_ifs
  · exact (S.ku' _)
  · exact (S.ku _)

omit scl in
/-- a sum of n products of numbers bounded by A and B -/
theorem abs_dot_le {n : ℕ} {a b : Vec} {A B : ℤ}
    (ha : ∀ j < n, |a j| ≤ A) (hb : ∀ j < n, |b j| ≤ B) : |dot n a b| ≤ n * (A * B) := by
  unfold dot
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_card_nsmul (range n) (fun j => |a j * b j|) (A * B) fun j hj => by
    show |a j * b j| ≤ A * B
    rw [abs_mul]
    exact mul_le_mul (ha j (mem_range.mp hj)) (hb j (mem_range.mp hj)) (abs_nonneg _)
      ((abs_nonneg _).trans (ha j (mem_range.mp hj)))
  rwa [card_range, nsmul_eq_mul] at this

omit scl in
/-- an accumulator over at most 5,120 channels, of values up to 2,047 and weights up to 2^12 -/
theorem acc_le {n : ℕ} (hn : n ≤ 5120) {a b : Vec}
    (ha : ∀ j < n, |a j| ≤ 2047) (hb : ∀ j < n, |b j| ≤ 2 ^ 12) :
    |dot n a b| ≤ 5120 * 2 ^ 11 * 2 ^ 12 := by
  refine (abs_dot_le ha hb).trans ?_
  have : (n : ℤ) ≤ 5120 := by exact_mod_cast hn
  nlinarith

/-- The values of the hidden unit x of layer ℓ at position i. -/
def uv (t : Cell → ℤ) (l x i : ℕ) : Unit.UnitV :=
  ⟨val t .g0 l x i, val t .gh l x i, val t .gc l x i, val t .sl l x i, val t .up l x i,
    val t .rg l x i, val t .ru l x i⟩

section
variable {D : Dim} {w : ℕ → LayerW} {t : Cell → ℤ}

variable {l x i : ℕ}

omit scl in
/-- the accumulators of a unit that is not routed -/
theorem acc_shared (hr : routed D l x = false) :
    Ag D t (fun l => LW.ofInt ℤ (w l)) l x i =
      dot D.d (fun j => val t .m l j i) (fun j => (w l).Wg j x) ∧
    Au D t (fun l => LW.ofInt ℤ (w l)) l x i =
      dot D.d (fun j => val t .m l j i) (fun j => (w l).Wu j x) := by
  unfold Ag Au
  rw [hr]
  exact ⟨rfl, rfl⟩

end

end NWU

end Inst.Model.FFSeg
