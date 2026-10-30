-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysLookP.lean: the lengths of the lookup's two points, from the verifier's own
lines and one of its tests.

The theorems of Johnson/Road/FormsKeysLook.lean and Johnson/Road/FormsKeysLookT.lean ask that the
lookup's point inside a tree has dT coordinates and its point over the trees' numbers rK. The
verifier's Forest.pad (OnBytes/Model/Look.lean) cuts both from one array of challenges, rho: the
first dT members, and the rest. It does not test the length of rho. It tests that each call's point,
which it makes from the two, has as many coordinates as the call's record says. This file shows that
the two lengths follow from these lines and that test at one call that has more than one tree.

Every statement is on the verifier's side alone.

Main theorems: sizes_of_pad; sizes_of_pad_one (what follows at a call with one tree).

The hypotheses. hzx, hzy, hzk: three lines of Forest.pad, in its letters. hpt: its test at call c,
as an equation. hn: the call has 2^(dT + iota) keys, which is the text of Forest.shape where dT is
at most the call's logarithm. hio: pad's other test at that call. hpos: the call has more than one
tree. All stand inside a routine that reads messages, or follow from Forest.shape; they are asked
here. At
the made-up shape hR8 and at both shipped examples some call has more than one tree
(Johnson/Road/FormsKeysRunZ.lean holds the numbers).

What is not claimed. With one tree in every call the test does not see the length of the point over
the trees' numbers from below: sizes_of_pad_one has "at most rK" alone. That the verifier's arrays
are made by these lines is asked. The program does not import this file.
-/
import Johnson.Road.FormsKeysLook

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

variable {fo : Model.Forest.Shape} {rho zx zy : Array E} {zk : Array (Array E)} {c : ℕ}

/-- The length of the point of call c, from the three lines of Forest.pad. -/
theorem size_of_pad (hzx : zx = rho.extract 0 fo.dT) (hzy : zy = rho.extract fo.dT rho.size)
    (hzk : zk = (Array.range fo.NC).map fun c =>
      zy.extract (fo.rK - fo.iota.getD c 0) zy.size ++ zx) (hc : c < fo.NC) :
    (zk.getD c #[]).size =
      (rho.size - fo.dT - (fo.rK - fo.iota.getD c 0)) + min fo.dT rho.size ∧
      zx.size = min fo.dT rho.size ∧ zy.size = rho.size - fo.dT := by
  have h1 : zx.size = min fo.dT rho.size := by
    rw [hzx, Array.size_extract]
    omega
  have h2 : zy.size = rho.size - fo.dT := by
    rw [hzy, Array.size_extract]
    omega
  refine ⟨?_, h1, h2⟩
  rw [hzk, range_map_getD' _ _ _ hc, Array.size_append, Array.size_extract, h1, h2]
  omega

/-- THE TWO LENGTHS. If the point of a call with more than one tree has as many coordinates as the
call's record says, the point inside a tree has dT coordinates and the point over the trees' numbers
has rK. -/
theorem sizes_of_pad (hzx : zx = rho.extract 0 fo.dT) (hzy : zy = rho.extract fo.dT rho.size)
    (hzk : zk = (Array.range fo.NC).map fun c =>
      zy.extract (fo.rK - fo.iota.getD c 0) zy.size ++ zx) (hc : c < fo.NC) {n : ℕ}
    (hpt : (zk.getD c #[]).size = n) (hn : n = fo.dT + fo.iota.getD c 0)
    (hio : fo.iota.getD c 0 ≤ fo.rK) (hpos : 0 < fo.iota.getD c 0) :
    zx.size = fo.dT ∧ zy.size = fo.rK := by
  obtain ⟨h0, h1, h2⟩ := size_of_pad hzx hzy hzk hc
  rw [h1, h2]
  rw [h0, hn] at hpt
  generalize fo.iota.getD c 0 = i at *
  omega

/-- At a call with one tree the same test gives the first length, and for the second an upper bound
alone. -/
theorem sizes_of_pad_one (hzx : zx = rho.extract 0 fo.dT)
    (hzy : zy = rho.extract fo.dT rho.size)
    (hzk : zk = (Array.range fo.NC).map fun c =>
      zy.extract (fo.rK - fo.iota.getD c 0) zy.size ++ zx) (hc : c < fo.NC)
    (hpt : (zk.getD c #[]).size = fo.dT) (h0 : fo.iota.getD c 0 = 0) :
    zx.size = fo.dT ∧ zy.size ≤ fo.rK := by
  obtain ⟨e0, h1, h2⟩ := size_of_pad hzx hzy hzk hc
  rw [h1, h2]
  rw [e0, h0] at hpt
  omega

#print axioms sizes_of_pad
#print axioms sizes_of_pad_one

end OnBytes.Road
