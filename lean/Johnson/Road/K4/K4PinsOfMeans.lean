-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsOfMeans.lean: THE BRIDGE BETWEEN TWO LEAN STRUCTURES OF EQUATIONS ON THE TABLE
OF JOINTS' MEANING: `K4Means Mg Dk` (Johnson/Road/K4/K4Means.lean: all that K4's files read of the
meaning, over the owners' data Dk) GIVES `K4MeanEqs` (Johnson/Road/K4/K4PinsEnd.lean: what the seven
lines of `k4_own_end` spend), under ties on Dk's letters. So `k4_own_end` can be spent where
`K4Means` stands. One abbreviation, one structure, one theorem: field by field; the three lines on
the item worth by `worth_lines` (Johnson/Road/K4/K4PinsEndFill.lean). No draw, no count.

  `sentOf Dk`: the lookups' data Dk.D3 with its codes set to Dk.cs (so that the two structures'
    letters smp, which are typed over the codes, are one by unfolding).
  `MeansTies Dk p m x s seat enc`: THE TIES: the lookups' data's codes are Dk's (as an equation of
    the whole data) · the lookups' letter arr is Dk's · `WorthTies` (seven equations on public
    letters) · the lookups' letter msgW is enc at the witness's cells · the list of group p.g that
    Dk.H reads off a witness is `Meaning.mgOf` of the segments' own lists.
  **`meanEqs_of_means`**: `K4Means Mg Dk` and `MeansTies` give `K4MeanEqs` at: D := `sentOf Dk` ·
    rad, oW, wOf := Dk.L3's · seatT j := Dk.L3.seat x.link false j · q := `pubAt X (m / stepOf X)` ·
    arr, ms, N, G, smp, decT, hd, put, H, headPart, digitsPart := Dk's.

STANDS OVER K4Means.lean with its cone, which stands in this tree; and as K4PinsEnd.lean and
K4PinsEndFill.lean.

OBJECT: none of its own. USER: Johnson/Road/K4/K04LawOf.lean; meant: the assembly of K4's law at all
places. LETTERS: Dk, Mg, p, m, x, s, seat, enc, Zt: free.

Limits. K04_law IS NOT PROVED BY THIS. `MeansTies` IS A PREMISE: its first three fields are
equations on public letters (none has run); the fourth is a choice of the lookups' letter msgW; THE
FIFTH IS A PROPERTY OF THE LETTER Dk.H: it holds by unfolding at `P5J.hidAtSeat` (`hid_seat_MG`,
Johnson/Road/K4/K4PinsConstr.lean) and is asked of whoever fills H. IT WILL TURN WHEN `K4Means`
TURNS. Of `K4Means`' fields nine are spent: pin, noColl, shown, held, pinW, decodes, constr, decIs,
worth.
-/
import Johnson.Road.K4.K4PinsEndFill
import Johnson.Road.K4.K4Means

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.First.Look (Sent pubAt stepOf)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (fillK3All worthK3)
open Cb.Pv.Tail (Size)

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Public}

/-- The lookups' data, with the codes set to Dk's. -/
abbrev sentOf (Dk : K4Data Xi P Tok rows cols nR kC X) : Sent := { Dk.D3 with codes := Dk.cs }

/-- **The ties on the data's letters.** -/
structure MeansTies (Dk : K4Data Xi P Tok rows cols nR kC X) (p : Par) (m : ℕ)
    (x : VerifiableInference.Desc.First.Look.Place) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (enc : CellsK rows cols → Dk.L3.oW.Msg) :
    Prop where
  sent : Dk.D3 = sentOf Dk
  arr : Dk.L3.arr = Dk.arr
  worth : WorthTies X Dk.L3 p m x
  msg : Dk.L3.msgW = fun w => enc w.cells
  hid : ∀ w, (Dk.H.hid w).MG p.g =
    _root_.Meaning.mgOf X.y (ownW Dk.arr Dk.ms Dk.N s seat Dk.cs w) p.g

/-- **`K4Means` gives `K4MeanEqs`**, under the ties. -/
theorem meanEqs_of_means {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)}
    {Dk : K4Data Xi P Tok rows cols nR kC X} (E : K4Means Mg Dk) {p : Par} {m : ℕ}
    {x : VerifiableInference.Desc.First.Look.Place} {s : ℕ → Size}
    {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {enc : CellsK rows cols → Dk.L3.oW.Msg}
    (T : MeansTies Dk p m x s seat enc) (Zt : P) :
    K4MeanEqs (X := X) (p := p) x (pubAt X (m / stepOf X)) (sentOf Dk) Dk.L3.rad
      (fun j => Dk.L3.seat x.link false j.1) Dk.L3.oW enc Dk.L3.wOf Dk.arr Dk.ms Dk.N m Dk.G
      Dk.smp Dk.decT Mg Zt s seat Dk.hd Dk.put Dk.H Dk.headPart Dk.digitsPart := by
  have hW : Mg.worth =
      (fillK3All X (sentOf Dk) Dk.L3 { Mg with worth := Dk.worthBase }).worth := by
    show Mg.worth = worthK3 X (sentOf Dk) Dk.L3 Dk.worthBase
    rw [← T.sent]
    exact E.worth
  have W := worth_lines X (sentOf Dk) Dk.L3 { Mg with worth := Dk.worthBase } Mg p m x enc Zt
    T.worth hW T.msg
  rw [T.arr] at W
  exact
    { pin := E.pin
      noColl := E.noColl
      shown := E.shown
      held := E.held
      pinW := E.pinW
      decodes := E.decodes
      constr := E.constr
      decIs := E.decIs
      hidIs := T.hid
      planes := W.1
      keys := W.2.1
      rider := W.2.2 }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.meanEqs_of_means
