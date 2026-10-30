-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawNamedRow.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS ROW OF THE TABLE OF
JOINTS WITH FOUR LETTERS FEWER: THE MEMBERS, THEIR SEATS, THE BOOK'S INVERSE AND THE STRETCH'S BASE
ARE FUNCTIONS WITH CODE.

`k08_row` (Johnson/Desc/First/K8/LawRow.lean) has as letters the list l of the members' shapes,
their seats seat', the map arr from a tree's tenant to a message's number, and the stretch's base,
with one premise that ties two of them: every seat's tree is below the base. Here:
  l := `Named.listOf rad S₀ book tl L`, seat' := `Named.seatFn …`, arr := `Named.arrOf book`
    (Johnson/Desc/First/K8/Named.lean: read off the smallness test's record, the link's record, the
    statement and the book by the running text's own reading);
  base := the number of trees that the first chain's rounds in front of the block's round send.
  `k08_row_named`: **the row there**: THE PREMISE ON THE SEATS IS GONE: it is paid by two tests with
    code: `Named.namedB` (every array that the matrix multiplies lies in a message whose tree the
    place names) and the file's test on the plan, at a block with `LikeP`
    (Johnson/Desc/First/K8/LawSeatedPlan.lean): so also at a guarded block.
Statement and proof: one call.
Limits. Those of LawRow.lean, Named.lean and LawSeatedPlan.lean. THE ROW SPEAKS OF THE PIECE OF THE
KIND'S OWN BLOCK (`piece … atS p`), as LawRow.lean's does: b, the block in the file's flat list, is
read for its rounds, its field `before` and its test on the plan alone. STILL LETTERS: rad, cs · J,
Y, entE, entW with the law hE that ties them · smpOf · tl0 against tl: nothing here says that the
record tl off which the members are read is tl0. THAT THE STRETCH'S BASE IS THAT NUMBER OF TREES is
the tiling's to say.

-/
import Johnson.Desc.First.K8.LawSeatedPlan
import Johnson.Desc.First.K8.LawRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Maker OnBytes.Road.Rows OnBytes.Tie.Pv.Tail
  OnBytes.Tie.Pv.Tail.Port KObj Johnson.Pack VerifiableInference.OnPublicFiles
  VerifiableInference.Desc.Sound

section
variable {J : Type} [Fintype J] (Y : Lay J) (tl0 : HTailF2) (cs : OnBytes.Codes)
  (rad : OracleShape → Nat) (S₀ : Statement) (book : TreeBook) (tl : HTailF2) (L : LinkCtx)

variable {Cells Tok : Type} (entE : (sigOf cs (Named.listOf rad S₀ book tl L)).Msg → J → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → J → Cb.Gl.E) {Xi : Type} (G : FileDescription Xi)
  (smpOf : S → (sigOf cs (Named.listOf rad S₀ book tl L)).Smp)
  (hs : ∀ (s : S) (t : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some t →
    smpOf (s.putTl { t with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : Par) (e : ℕ)
  {seat : Seat G.S₁} {b : Block G.S₁ G.Cl} (hb : LikeP seat p b) (pre post : List (Block G.S₁ G.Cl))
  (hflat : G.first.blocksInOrder = pre ++ b :: post) (hG : G.planOk = true)
  (hN : Named.namedB p S₀ book tl L = true)

include smpOf hs hb hflat hG hN in
/-- **The row, with the members, their seats, the book's inverse and the base as functions with
code.** -/
theorem k08_row_named
    (hE : ∀ w j, early tl0 (Y.addr j) = true → entE (msgsOf cs (Named.listOf rad S₀ book tl L)
        (Named.seatFn rad S₀ book tl L) (Named.arrOf book) w) j = entW w j)
    (hgt : tl0.NM ≤ tl0.gtTree.size) (hu : ∃ t, tl0.ix.U[2]? = some (some t))
    (hP : PlaceRec p tl0)
    (he : (Fintype.card (Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) /
      2 ^ (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e).ior.red.KeepsW
      (fun a => (layReads Y tl0 cs (Named.listOf rad S₀ book tl L)
          (Named.seatFn rad S₀ book tl L) (Named.arrOf book) entE entW G smpOf hs Cl F p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e
        (named_seats_below_P G hb pre post hflat hG rad S₀ book tl L hN)).onA a ∧ Extra a.1)
      (fun c => (layReads Y tl0 cs (Named.listOf rad S₀ book tl L)
          (Named.seatFn rad S₀ book tl L) (Named.arrOf book) entE entW G smpOf hs Cl F p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e
        (named_seats_below_P G hb pre post hflat hG rad S₀ book tl L hN)).onB c ∧ Extra c.1)
      (fun a w => PinsAt cs (Named.listOf rad S₀ book tl L)
          (Named.seatFn rad S₀ book tl L) (Named.arrOf book) G smpOf F a w ∧
        TieAt (fun w a r c => Y.cellAt (entW w) a r c) a.1 w)
      (fun c w => PinsAt cs (Named.listOf rad S₀ book tl L)
          (Named.seatFn rad S₀ book tl L) (Named.arrOf book) G smpOf F c w ∧
        SmallAt (fun w a r c => Y.cellAt (entW w) a r c) c.1 w ∧
        DigitsAt (fun w a r c => Y.cellAt (entW w) a r c) c.1 w)
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e).err :=
  k08_row Y tl0 cs (Named.listOf rad S₀ book tl L)
      (Named.seatFn rad S₀ book tl L) (Named.arrOf book) entE entW G smpOf hs Cl F p _ e
    (named_seats_below_P G hb pre post hflat hG rad S₀ book tl L hN) hE hgt hu hP he

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.k08_row_named
