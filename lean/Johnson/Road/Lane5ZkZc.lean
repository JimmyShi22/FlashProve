-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5ZkZc.lean

The verifier's key point of a lookup call, read, IS the library's key point of that call.

The verifier's lookup sets the key point of call c to (the last iota_c coordinates of zy | zx)
(OnBytes/Model/Look.lean:411, in the body of Forest.pad). The library has zC c z := (the last e
coordinates of the tree part of z | the part of z inside a tree), for z = (inside | tree part)
(Inst/Model/Att/Points.lean). With z := (zx | zy), read, and the numbers callsOf fs
(Lane5CallsOf.lean), the two agree at every coordinate below a c.

Main theorems: "readV_append", "readV_extractAt" (reading a joined array, a cut array);
**"zk_eq_zC"**.
"zk_eq_zC_of_fit": the same with the three premises on numbers from CallsFit (Lane5CallsOf.lean), a
test that is run at both configurations.
Premises of zk_eq_zC: zx has dT and zy rK coordinates; iota of call c is the library's e c; e c is
at most rK; Dk is at most a c. The array on the left is typed here as Look.lean:411 has it: that a
record which Forest.pad returns holds it under zk is by that body's text; no theorem says it.
-/
import Johnson.Road.Lane5CallsOf
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes OnBytes.Slice
open Inst.Model.AttSeg

/-- Reading a joined array. -/
theorem readV_append (a b : Array E) (i : ℕ) :
    readV (a ++ b) i = if i < a.size then readV a i else readV b (i - a.size) := by
  unfold readV
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split_ifs <;> rfl

/-- Reading a cut array. -/
theorem readV_extractAt (a : Array E) (s e i : ℕ) (h : i < min e a.size - s) :
    readV (a.extract s e) i = readV a (s + i) := by
  unfold readV
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract, if_pos h]

/-- **The verifier's key point of call c, read, is the library's.** -/
theorem zk_eq_zC (fs : Model.Forest.Shape) (zx zy : Array E) (hx : zx.size = fs.dT)
    (hy : zy.size = fs.rK) (c : Fin 4) (hi : fs.iota.getD c.val 0 = (callsOf fs).e c)
    (hle : (callsOf fs).e c ≤ fs.rK) (hD : (callsOf fs).Dk ≤ (callsOf fs).a c) (t : ℕ)
    (ht : t < (callsOf fs).a c) :
    readV (zy.extract (fs.rK - fs.iota.getD c.val 0) zy.size ++ zx) t =
      (callsOf fs).zC c (readV (zx ++ zy)) t := by
  have hDk : (callsOf fs).Dk = fs.dT := rfl
  have hsg : (callsOf fs).sg = fs.rK := rfl
  have he : (callsOf fs).e c = (callsOf fs).a c - (callsOf fs).Dk := rfl
  have hs : (zy.extract (fs.rK - (callsOf fs).e c) zy.size).size = (callsOf fs).e c := by
    rw [Array.size_extract, hy]
    omega
  rw [hi, readV_append, hs]
  unfold Calls.zC
  by_cases h : t < (callsOf fs).e c
  · rw [if_pos h, if_pos h, readV_extractAt _ _ _ _ (by rw [hy]; omega), readV_append, hx, hDk, hsg,
      if_neg (by omega)]
    congr 1
    omega
  · rw [if_neg h, if_neg h, readV_append, hx, if_pos (by omega)]

/-- **The same, with the numbers' premises from CallsFit.** -/
theorem zk_eq_zC_of_fit {S : Attention.Shape} {fs : Model.Forest.Shape} (h : CallsFit S fs)
    (zx zy : Array E) (hx : zx.size = fs.dT) (hy : zy.size = fs.rK) (c : Fin 4) (t : ℕ)
    (ht : t < (callsOf fs).a c) :
    readV (zy.extract (fs.rK - fs.iota.getD c.val 0) zy.size ++ zx) t =
      (callsOf fs).zC c (readV (zx ++ zy)) t :=
  zk_eq_zC fs zx zy hx hy c (callsFit_iota h c).1 (callsFit_iota h c).2 (h.2.1 c) t ht

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.zk_eq_zC
#print axioms OnBytes.Road.L5.zk_eq_zC_of_fit
