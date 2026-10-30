-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/CornerKit.lean: a corner of the cube as a point; small laws.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the makers lay a point
at the bits of a token's number (bitsOf, Johnson/Desc/K4/Honest/Cells.lean). Here that function has
a name of its own, since under the namespace OnBytes.Road the bare name bitsOf is another
function's (Johnson/Road/FormsKeysWm.lean); and the laws on it that this folder's files share.
Statements and proofs.

  `cornerPt`        the makers' bitsOf.
  `cornerPt_size`   a corner has as many coordinates as the cube has variables.
  `bits_pt`         a coordinate of a corner, read into the field.
  `ext_corner`      an extension at a corner is the entry.
  `envOf_y`, `envOf_g`   the makers' environment has the plan's layout and group.

Not shown here. Nothing on the cells, on a world or on a verifier.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Cells
import Johnson.Road.FormsKeysFac
import Johnson.Road.FormsKeysLook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env)
open Blocks (ext)
open OnBytes.Desc.First.K4.Honest (K4Pub Pts)

/-- The makers' corner number x of the cube in n variables, as a point (bitsOf,
Johnson/Desc/K4/Honest/Cells.lean), under a name of its own: the library has another bitsOf. -/
abbrev cornerPt (n x : ℕ) : Array E := OnBytes.Desc.First.K4.Honest.bitsOf n x

/-- A corner has as many coordinates as the cube has variables. -/
theorem cornerPt_size (n x : ℕ) : (cornerPt n x).size = n := by
  unfold cornerPt OnBytes.Desc.First.K4.Honest.bitsOf
  rw [Array.size_map, Array.size_range]

/-- The coordinates of a corner, read into the field. -/
theorem bits_pt (n x s : ℕ) (hs : s < n) :
    pt Reading.gl (cornerPt n x) (0 + s) = if x.testBit (n - 1 - s) then 1 else 0 := by
  unfold pt cornerPt Desc.First.K4.Honest.bitsOf
  rw [Nat.zero_add, range_map_getD' _ _ _ hs]
  by_cases h : x.testBit (n - 1 - s) = true
  · rw [if_pos h, if_pos h]
    exact Reading.gl.one
  · rw [if_neg h, if_neg h]
    exact Reading.gl.zero

/-- **An extension at a corner is the entry.** -/
theorem ext_corner (g : ℕ) (f : ℕ → Cb.Gl.E) {i : ℕ} (hi : i < 2 ^ g) :
    ext g f (pt Reading.gl (cornerPt g i)) = f i := by
  unfold Blocks.ext
  rw [Finset.sum_eq_single i]
  · rw [eqN_bool g 0 _ hi hi (fun s hs => bits_pt g i s hs), if_pos rfl, one_mul]
  · intro X hX hne
    rw [eqN_bool g 0 _ hi (mem_range.mp hX) (fun s hs => bits_pt g i s hs), if_neg hne, zero_mul]
  · intro h
    exact absurd (mem_range.mpr hi) h

/-- The makers' environment has the plan's layout. -/
theorem envOf_y {Q : K4Pub} {p : Pts} {v : Env}
    (hv : OnBytes.Desc.First.K4.Honest.envOf Q p = some v) : v.y = Q.P.y := by
  unfold OnBytes.Desc.First.K4.Honest.envOf at hv
  obtain ⟨iU3, _, h⟩ := Option.bind_eq_some_iff.mp hv
  obtain ⟨⟨tab, a, b⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  rfl

/-- The makers' environment has the plan's group. -/
theorem envOf_g {Q : K4Pub} {p : Pts} {v : Env}
    (hv : OnBytes.Desc.First.K4.Honest.envOf Q p = some v) : v.g = Q.g := by
  unfold OnBytes.Desc.First.K4.Honest.envOf at hv
  obtain ⟨iU3, _, h⟩ := Option.bind_eq_some_iff.mp hv
  obtain ⟨⟨tab, a, b⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.cornerPt_size
#print axioms OnBytes.Road.K4.C.bits_pt
#print axioms OnBytes.Road.K4.C.ext_corner
#print axioms OnBytes.Road.K4.C.envOf_y
#print axioms OnBytes.Road.K4.C.envOf_g
