-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/CellsOfAttReading.lean: CONDITIONAL.

What is here. THE FIRST STONE OF A BRIDGE TO THE HYPOTHESIS `CellIsList` (Law/W/CellsTieOf.lean) OF
THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4). `CellIsList` holds the honest side's cells
against the list of integers that the library's meaning reads off a witness for the group
(`(h.𝔇.H.hid w).MG g`). By `matsAre_head` (Law/W/MatsAreHead.lean) the images of that list are what
the caller of the lookup on a layers' link's calls reads off the witness. Here: that reading is, at
every triple of indices, the reading of the caller of the lookup on an attention link's calls
(`matsOfMsg` over `attMs`), at the same place, plan and letters; so `CellIsList` follows from one
sentence on that second reading, for which another house has laws (Honest/K5/Law/CellsQRaw.lean).
Two statements with their proofs. The first is by cases on whether the triple names a cell, and the
library's `layMs_some`; the second is a chain of calls.

  `lay_reads_as_att`   the two callers read one thing off a witness. No hypothesis.
  `cellIsList_of_att`   **`CellIsList` from the sentence E on the second reading**, at every
      witness.

Not shown here. E: THAT THE SECOND READING IS THE HONEST SIDE's CELL: a hypothesis; all that
`CellIsList` says of values is left in it. h: the library's hypothesis `P5J.AtMgA` on the public
files; Lh (`LaidK4`, Law/SeatedHead.lean) and hx: on public lists and numbers; both follow from h at
each of the twelve groups, as Law/W/MatsAreHead.lean's head says. No script, thread, state or prover
is named. Of h together with E no example is known to its writers. All limits of the heads of the
files that it imports hold here; among them: closed facts by evaluation in Lean's kernel lie
beneath; no independent checker that its writers know of has replayed them; through its imports it
stands over files under Johnson/Goal/. THE FULL SIZE ALONE, and the format's second hash function alone
(`OnBytes.secondHashFunction`), but for `lay_reads_as_att`, which is general. A LAW, NOT A PART: no file that
defines a part of the proof file's description may import this one. Nothing on soundness, on
completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MatsAreHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CellsTieOf
import Johnson.Desc.First.Att.K05CellsTie
import Johnson.Desc.First.Look.K3AttGoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (HTailF2 Reading)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In)
open OnBytes.Maker (WholeD)
open Cb.Pv.Tail (cellValS)
open VerifiableInference.Desc (Chain Block Wit)
open VerifiableInference.Desc.First.Look (layAt MatsAre Sent sigListCalls seatCalls szOf ownPart
  msgLay matsOfE lyCell cellJ enCell msgAtt symAt)
open VerifiableInference.Desc.First.Att.P (matsOfMsg)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (layMs layMs_some attMs)
open P5J (AtMgA TS)
open ProofFile.Honest.FirstThread (WtF)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- **The caller of the lookup on a layers' link's calls and the caller of the lookup on an
attention link's calls read one thing off a witness**, at one place, plan and letters: at every
triple of indices; 0 on both sides where the triple names no cell. No hypothesis. -/
theorem lay_reads_as_att {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place)
    (tl : HTailF2) (D : Sent) (rad : OnBytes.OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (msgW : Wit Cells Tok MsgT → oW.Msg) (w : Wit Cells Tok MsgT) :
    matsOfE (msgLay x tl D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w)) =
      matsOfMsg x tl D rad (attMs x D rad seatT arr w) := by
  have e : ownPart (layMs x D rad oW seatT arr msgW w) = attMs x D rad seatT arr w := by
    funext i
    exact layMs_some x D rad oW seatT arr msgW w i
  funext a r c
  show msgLay x tl D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w)
      (lyCell x.ns tl nr nc a r c) =
    msgAtt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl x.ns
      (attMs x D rad seatT arr w) (enCell x.ns tl a r c)
  unfold lyCell enCell
  cases cellJ (szOf tl) a r c with
  | none => rfl
  | some j =>
    show cellValS (symAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl
        (ownPart (layMs x D rad oW seatT arr msgW w))) j =
      cellValS (symAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl
        (attMs x D rad seatT arr w)) j
    rw [e]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, Lh, hx and E. **`CellIsList` AT THE LIST OF THE GROUP, FROM THE SENTENCE E ON
THE READING `matsOfMsg` OVER `attMs`.** xl: the lookup's place at the segment. w: any witness. wi:
any small input. Qp: read for the number of the planes' matrix alone. -/
theorem cellIsList_of_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (w : WtF) {Qp : K4Pub} {wi : K4In}
    (E : ∀ i a b, i < x.2.hp.tl.NM → i ≠ (OnBytes.Model.Layer.matIx Qp.P.y).iB →
      a < (x.2.hp.tl.mats.getD i {}).m → b < (x.2.hp.tl.mats.getD i {}).k →
      matsOfMsg xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad
          (attMs xl h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr w)
          i a b =
        Reading.gl.val (OnBytes.ofF (wi.cell i a b))) :
    CellIsList Qp wi ((h.𝔇.H.hid w).MG g) x.2.hp.tl := by
  intro i a b h1 h2 h3 h4
  have e := matsAre_head h Lh hx w
  unfold MatsAre at e
  rw [lay_reads_as_att] at e
  exact (E i a b h1 h2 h3 h4).symm.trans (congrFun (congrFun (congrFun e i) a) b)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.lay_reads_as_att
#print axioms ProofFile.Honest.K4.W.cellIsList_of_att
