-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawAtFrame.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS LETTERS FILLED AT THE
FIRST CHAIN'S CARRIED RECORD, OVER THE FRAME'S OWN ORACLE MESSAGES AND THE FILE'S ONE WITNESS.

The laws of LawPiece.lean, LawLost.lean, LawKeeps.lean and LawReads.lean stand under letters
(`Reads`): how the carried record and the frame's oracles are read as the proved block's statement,
and how a witness is read. Free letters can be filled so that the laws are true and empty: a reading
that is constant; a type of witnesses that is empty. Here four of them are filled with what the
chain itself has, by the readings of Johnson/Desc/Sound/MsgSig.lean, called, not typed anew: THE
SEAT: that of Johnson/Desc/First/K8/AtS.lean: the first chain's carried record. THE SIGNATURE:
`Johnson.Pack.sigOf cs l`: a function of the programs' codes and of a list of sampled messages'
shapes. THE WORDS: `wordsOf G cs l seat' (strsOf F y)`: read leaf by leaf OFF THE FRAME'S OWN
STRINGS y, at the trees and tenants that seat' names. THE WITNESS: the file's one witness (`Wit
Cells Tok MsgT`); a member's message is `msgsOf`: the message under the number that `arr` gives its
tree and tenant. THE MATRIX'S LIST: the field cfF of the record of the smallness test that lies in
the carried record. Main names:
  `frameReads`: the member. Its two laws are PROVED: the seat's laying lays that list; and a yes
    leaves the reading as it was: the words by `wordsStay`, WHICH ASKS THAT EVERY NAMED TREE IS SENT
    IN FRONT OF THE BLOCK'S STRETCH (`hseat`).
  `frame_onA`, `frame_relA`: what then stands in front of the draw, unfolded: no collision at the
    samples on these words; the pins (the library's decoder with the sample gives the witness's
    message, member by member); what rides; the proved block's first joint.
  `frame_keepsW`: the kind's law in the plain form there; the proved block's condition paid by
    `sizeOf_ok`.
  `frame_reads_are_true`: "the sent reads are the true ones" there; the no-wrap premise paid by
    `sizeOf_uniq`.
Definitions, statements and proofs.
Limits. STILL LETTERS: the record tl0 whose sizes the caller has (that it is the carried record's
own, with the list of tables closed, is not said; `Fits` at it is a premise, which `yes_atS` pays
only at the record that lies in the state) · Θ (the weights, symbols and reads as functions of
statement and messages) and rdm (a tuple of messages as Θ's) · xOf, eOf (the explicit statement off
the record) · smpOf (THE SAMPLES OFF THE RECORD: total here; MsgSig.lean has them partial, and no
text yet reads a sending's seed off the record) · wOf (the digits and what rides, off the witness) ·
the condition `on` · l, seat', arr (which members; where; under which number). xOf and smpOf must
not read the two fields that the block lays (the matrix's list; the first columns): `hx`, `hs`. ONE
signature is taken for all members, of whichever sending: the table of joints has a pin for each
sending. That every leaf is shown, and that the seats fit the plan (`ShownAt`, `SeatFits`), is not
asked here. Nothing says that what stands at a boundary holds.

-/
import Johnson.Desc.First.K8.LawBack
import Johnson.Desc.First.K8.LawKeeps
import Johnson.Desc.First.K8.LawReads
import Johnson.Desc.Sound.MsgSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Maker OnBytes.Tie.Pv.Tail KObj Johnson.Pack
  VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound

section
variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) {Cells Tok : Type}
  (tl0 : HTailF2) (Θ : TLetters Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl0))
  (rdm : (sigOf cs l).Msg → Θ.M) (on : Θ.X × Θ.E.Str → Prop)
  (xOf : S → Θ.X) (eOf : Θ.E.Str) (smpOf : S → (sigOf cs l).Smp)
  (wOf : Wit Cells Tok MsgT → Θ.W)
  (hx : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    xOf (s.putTl { tl with cfF := mm, cfFirst := f }) = xOf s)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : Par) (base e : ℕ) (hseat : ∀ i, (seat' i).1 < base)

/-- The letters, over the frame's own oracle messages. -/
def frameReads : Reads Cl (Wit Cells Tok MsgT) F atS p base e
    (callerAtRecord tl0 Θ (sigOf cs l) rdm on) where
  rd := fun a => ((xOf a.1, smpOf a.1), (eOf, wordsOf G cs l seat' (strsOf F a.2)))
  wit := fun w => (fun i => (msgsOf cs l seat' arr w i, fun _ => 0), wOf w)
  cf := fun s => (s.tl?.map (·.cfF)).getD #[]
  cf_lay := fun st st' mm f h => by
    obtain ⟨tl, ht, e1⟩ := atS_lay st st' mm f h
    subst e1
    rw [putTl_tl st tl _ ht]
    rfl
  keeps := fun st st' mm f y τ h => by
    obtain ⟨tl, ht, e1⟩ := atS_lay st st' mm f h
    subst e1
    have hw : wordsOf G cs l seat' (strsOf F (behind (Run.ckP .two) F base [rdt p] y τ)) =
        wordsOf G cs l seat' (strsOf F y) :=
      funext fun i => wordsStay G cs l seat' (Run.ckP .two) F base [rdt p] y τ i (hseat i)
    show ((xOf _, smpOf _), (eOf, wordsOf G cs l seat'
      (strsOf F (behind (Run.ckP .two) F base [rdt p] y τ)))) = _
    rw [hx st tl mm f ht, hs st tl mm f ht, hw]
    rfl

local notation "FR" =>
  frameReads G cs l seat' arr tl0 Θ rdm on xOf eOf smpOf wOf hx hs Cl F p base e hseat

/-- The condition in front, unfolded: no collision at the record's samples on the words that the
frame's own strings show; and the caller's condition. -/
theorem frame_onA (a : S × F.E.Str) :
    (FR).onA a ↔ (sigOf cs l).CF (smpOf a.1) (wordsOf G cs l seat' (strsOf F a.2)) ∧
      on (xOf a.1, eOf) :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2⟩⟩

/-- What stands in front, unfolded: the pins; what rides; the proved block's first joint at the
file's one witness's messages. -/
theorem frame_relA (a : S × F.E.Str) (w : Wit Cells Tok MsgT) :
    (FR).relA a w ↔
      (∀ i, (sigOf cs l).decs (smpOf a.1) (wordsOf G cs l seat' (strsOf F a.2)) i =
        some (msgsOf cs l seat' arr w i)) ∧
      Θ.ride (xOf a.1, eOf) (rdm (msgsOf cs l seat' arr w)) (wOf w) ∧
      relIn Θ.letters (xOf a.1) (rdm (msgsOf cs l seat' arr w)) :=
  Iff.rfl

/-- **The kind's law in the plain form, over the frame's own oracle messages.** -/
theorem frame_keepsW (hf : Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)
    (he : (Fintype.card (Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) /
      2 ^ (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).ior.red.KeepsW
      (FR).onA (FR).onB (FR).relA (FR).relB
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).err :=
  hear_keepsW (FR) hf (OnBytes.Tie.Pv.Tail.sizeOf_ok tl0) he

/-- **The sent reads are the true ones, there.** -/
theorem frame_reads_are_true (a : S × F.E.Str) (w : Wit Cells Tok MsgT) (h : (FR).relA a w) :
    CellsOK Θ.letters (xOf a.1) (rdm (msgsOf cs l seat' arr w))
      (cellsOf Θ.letters (rdm (msgsOf cs l seat' arr w))) :=
  cellsOK_cellsOf Θ.letters Cb.Gl.p (OnBytes.Tie.Pv.Tail.sizeOf_uniq tl0)
    ((frame_relA G cs l seat' arr tl0 Θ rdm on xOf eOf smpOf wOf hx hs Cl F p base e hseat a w).1
      h).2.2

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.frameReads
#print axioms VerifiableInference.Desc.First.K8.frame_relA
#print axioms VerifiableInference.Desc.First.K8.frame_keepsW
#print axioms VerifiableInference.Desc.First.K8.frame_reads_are_true
