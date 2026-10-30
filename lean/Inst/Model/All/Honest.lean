-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/All/Honest.lean: the honest trace of the whole model, at the reference parameters. y is
what the head reads of a request (`Head.Req`).
This file does not prove that the cells of the honest trace satisfy the field relation of all 25
segments, or that they are at most 128 in absolute value.

The honest traces of the three kinds are terms (`FFSeg.hon`, `AttSeg.hon`, `Head.honCells`),
functions of the weights and of the program's stream. `honT` puts them side by side. A borrowed cell
is written by its owner, and the borrower's rule writes the same number: `vFF_honT`, `vAtt_honT`,
`vHead_honT`. So each segment reads its own honest trace.
Notation:
  `tb`: a `Tables`, "The five table functions that the program reads." (Inst/Model/Program.lean)
  `W`: a `Mat` (`ℕ → ℕ → ℤ`); `Layout.weightsOf ppref kRef W`: "The weights that the layout reads
    from W." (Inst/Model/Layout.lean).
  g, l, s: natural numbers: a group of four layers ("Groups are counted from 0 here (g < 12; the
    first layer of group g is 4 g)": the comment at the top of Inst/Model/All/Trace.lean), a layer
    of the group, an index of the stream in the group.
  `8 * g + s`, `4 * g + l`, `2 * l`: that index and that layer, counted in the whole model, and the
    index before layer l; `X` (Inst/Model/Program.lean): "X_{2L} enters layer L, X_{2L+1} follows
    its attention block, X_{2L+2} follows its feed-forward block".
  the arguments 11 8: the last index of the last group: "x of the head is x8 of the last
    feed-forward segment" (the comment at the top of Inst/Model/All/Trace.lean).
  `cellW n a l`: an integer, "The widened cell rule: cell l of the value a in an array of n cells:
    balanced low bytes, and the rest in the top cell." (Inst/Model/Widened.lean).
  lam: a natural number, a layer λ of the segment (Inst/Model/Att/Index.lean).
-/
import Inst.Model.All.NoWrap
import Inst.Model.Att.Honest
import Inst.Model.Head.Honest
import Inst.Model.Sanity
import Inst.Model.FF.Honest
import Inst.Model.FF.Cast

set_option autoImplicit false

namespace Inst.Model.All

open Finset
open Layout (kRef hRef)

section Hon
variable (tb : Tables) (W : Mat) (prompt : Fin ppref.T → Fin ppref.V) (y : Head.Req)

/-- the program's stream at index s of group g -/
def xs (g s : ℕ) : ℕ → Vec := X ppref tb (Layout.weightsOf ppref kRef W) prompt (8 * g + s)
/-- the program's output of attention in layer l of group g -/
def os (g l : ℕ) : ℕ → Vec := Att.o ppref tb (wOf W g l) (4 * g + l) (xs tb W prompt g (2 * l))

/-- The honest trace. -/
def honT : Trace where
  ff := fun g => FFSeg.hon DF tb (wOf W g) (4 * g) (xs tb W prompt g) (os tb W prompt g)
  att := fun g =>
    AttSeg.hon DA AttSeg.refP tb (wOf W g) (4 * g) fun lam => xs tb W prompt g (2 * lam)
  hf := (Head.honCells (xs tb W prompt 11 8) (Layout.weightsOf ppref kRef W).H y).hf
  hd := (Head.honCells (xs tb W prompt 11 8) (Layout.weightsOf ppref kRef W).H y).hd
  hr := (Head.honCells (xs tb W prompt 11 8) (Layout.weightsOf ppref kRef W).H y).hr

/-- x0 of a later group: the segment before writes what the rule of this segment writes. -/
theorem vFF_honT (g : ℕ) :
    (honT tb W prompt y).vFF g =
      FFSeg.hon DF tb (wOf W g) (4 * g) (xs tb W prompt g) (os tb W prompt g) := by
  funext c
  unfold Trace.vFF
  by_cases hc : c.X = .x0 ∧ 0 < g
  · rw [if_pos hc]
    obtain ⟨X, k, inst, j, i⟩ := c
    obtain ⟨h1, h2⟩ := hc
    obtain rfl : X = .x0 := h1
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    show cellW 5 (xs tb W prompt g 8 i j - 0) k = cellW 5 (xs tb W prompt (g + 1) 0 i j - 0) k
    unfold xs
    rw [show 8 * (g + 1) + 0 = 8 * g + 8 by ring]
  · rw [if_neg hc]
    rfl

/-- qry, key, val, out: the feed-forward segment writes what the rule of the attention segment
writes. -/
theorem vAtt_honT (g : ℕ) :
    (honT tb W prompt y).vAtt g =
      AttSeg.hon DA AttSeg.refP tb (wOf W g) (4 * g) fun lam => xs tb W prompt g (2 * lam) := by
  funext c
  unfold Trace.vAtt AttSeg.join
  cases c with
  | qry k b g' i n =>
    show cellW 2 (_ - 0) k = cellW 2 _ k
    rw [sub_zero]
    rfl
  | out k b g' i n =>
    show cellW 2 (_ - 0) k = cellW 2 _ k
    rw [sub_zero]
    rfl
  | key k lam g' j n =>
    show cellW 2 (_ - 0) k = cellW 2 _ k
    rw [sub_zero]
    rfl
  | val k lam g' j n =>
    show cellW 2 (_ - 0) k = cellW 2 _ k
    rw [sub_zero]
    rfl
  | c ρ jj b x => rfl
  | mx k b g' i => rfl
  | den k b g' i => rfl
  | ib k b g' i => rfl
  | qh b g' i n => rfl
  | qh' b g' i n => rfl

/-- x of the head: the last feed-forward segment writes what the rule of the head writes. -/
theorem vHead_honT :
    (honT tb W prompt y).vHead =
      Head.honCells (xs tb W prompt 11 8) (Layout.weightsOf ppref kRef W).H y := by
  have hx : (honT tb W prompt y).vHead.x =
      (Head.honCells (xs tb W prompt 11 8) (Layout.weightsOf ppref kRef W).H y).x := by
    funext φ i
    show cellW 5 (xs tb W prompt 11 8 i (φ % 5120) - 0) (φ / 5120) =
      cellW 5 (xs tb W prompt 11 8 i (φ % 5120)) (φ / 5120)
    rw [sub_zero]
  show (⟨_, _, _, _⟩ : Head.Cells ℤ) = _
  rw [show (fun φ i => (honT tb W prompt y).ff (nGr - 1) ⟨.x8, φ / 5120, 0, φ % 5120, i⟩) = _
      from hx]
  rfl

end Hon

end Inst.Model.All
