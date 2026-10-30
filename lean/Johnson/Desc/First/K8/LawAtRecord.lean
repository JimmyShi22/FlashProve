-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawAtRecord.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS LETTERS WITH THE
EXPLICIT STATEMENT FILLED: THE RECORD OF THE SMALLNESS TEST THAT LIES IN THE CARRIED RECORD.

Johnson/Desc/First/K8/LawAtFrame.lean fills the signature, the words, the witness and the matrix's
list. Here four more letters are filled: THE EXPLICIT STATEMENT (`recOf`): the record of the
smallness test in the state, without the two fields that the draw lays. So it passes the block
unturned (`recOf_put`). THE WEIGHTS (`thetaRec`): a table's weights are read OFF THE STATEMENT's OWN
closed list of tables, as the library's `phiAt` reads them off a record (`record_w`). In the
protocol a table's weights hang on points that are drawn in front of the test: they differ from
statement to statement, and the proved block's count holds at each. THE CONDITION: the sizes of the
record in the state are the place's. NO FURTHER ORACLE (`noFurther`); NOTHING RIDES. Main names:
`recordReads`: the member · `record_onA`, `record_relA`: what then stands in front of the draw,
unfolded · `record_keepsW`: the kind's law in the plain form there.
Definitions, statements and proofs.
Limits. STILL LETTERS: tl0 (the place's public record: its sizes are the caller's) · sym, u3 (WHICH
ENTRY OF WHICH MEMBER's MESSAGE IS A SYMBOL OF A MATRIX OR AN ENTRY OF THE VECTOR OF READS: the lay)
· dig (the digits off the witness) · smpOf (the samples off the record) · l, seat', arr. With
nothing riding, what stands at the two boundaries says nothing beyond the pins and the proved
block's joints. `Fits` at tl0 is a premise. Nothing says that what stands at a boundary holds.

-/
import Johnson.Desc.First.K8.LawSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Maker OnBytes.Tie.Pv.Tail KObj Johnson.Pack
  VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound

/-- No further oracle. -/
@[reducible] def noFurther : ExtSpec := ⟨Unit, Empty, Unit, fun _ e => e.elim⟩

/-- A record of the smallness test without the two fields that the draw lays. -/
def blank (tl : HTailF2) : HTailF2 := { tl with cfF := #[], cfFirst := #[] }

/-- The explicit statement: the record of the smallness test that lies in the carried record,
without these two fields; tl0 where none lies there. -/
def recOf (tl0 : HTailF2) (s : S) : HTailF2 := blank (s.tl?.getD tl0)

theorem recOf_put (tl0 : HTailF2) (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat)
    (h : s.tl? = some tl) :
    recOf tl0 (s.putTl { tl with cfF := mm, cfFirst := f }) = recOf tl0 s := by
  unfold recOf
  rw [putTl_tl s tl _ h, h]
  rfl

section
variable (tl0 : HTailF2) (M W : Type) (sym : M → ℕ → ℕ → ℕ → Cb.Gl.E) (u3 : M → ℕ → Cb.Gl.E)
  (dig : W → Dig Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)

/-- Letters whose explicit statement is a record of the smallness test: A TABLE'S WEIGHTS ARE READ
OFF THE STATEMENT's OWN closed list of tables, as the library's `phiAt` reads them off a record. -/
@[reducible] def thetaRec : TLetters Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl0) where
  X := HTailF2
  M := M
  E := noFurther
  W := W
  phi := fun x => phiAt Reading.gl x
  sym := sym
  u3 := u3
  dig := dig
  ride := fun _ _ _ => True

end

section
variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) {Cells Tok : Type} (tl0 : HTailF2)
  (sym : (sigOf cs l).Msg → ℕ → ℕ → ℕ → Cb.Gl.E) (u3 : (sigOf cs l).Msg → ℕ → Cb.Gl.E)
  (dig : Wit Cells Tok MsgT → Dig Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)
  (smpOf : S → (sigOf cs l).Smp)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : Par) (base e : ℕ) (hseat : ∀ i, (seat' i).1 < base)

/-- The letters with the explicit statement filled: the record in the state; the condition: its
sizes are the place's. -/
def recordReads : Reads Cl (Wit Cells Tok MsgT) F atS p base e
    (callerAtRecord tl0 (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) sym u3 dig) (sigOf cs l)
      id
      (fun x => OnBytes.Tie.Pv.Tail.sizeOf x.1 = OnBytes.Tie.Pv.Tail.sizeOf tl0)) :=
  frameReads G cs l seat' arr tl0 (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) sym u3 dig) id
    (fun x => OnBytes.Tie.Pv.Tail.sizeOf x.1 = OnBytes.Tie.Pv.Tail.sizeOf tl0) (recOf tl0) () smpOf
    id
    (recOf_put tl0) hs Cl F p base e hseat

local notation "RR" => recordReads G cs l seat' arr tl0 sym u3 dig smpOf hs Cl F p base e hseat

/-- The condition in front: no collision at the record's samples on the words that the frame's own
strings show; and the sizes of the record in the state are the place's. -/
theorem record_onA (a : S × F.E.Str) :
    (RR).onA a ↔ (sigOf cs l).CF (smpOf a.1) (wordsOf G cs l seat' (strsOf F a.2)) ∧
      OnBytes.Tie.Pv.Tail.sizeOf (recOf tl0 a.1) = OnBytes.Tie.Pv.Tail.sizeOf tl0 :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2⟩⟩

/-- What stands in front: the pins, and the proved block's first joint AT THE WEIGHTS OF THE
STATEMENT's OWN LIST OF TABLES and the file's one witness's messages. -/
theorem record_relA (a : S × F.E.Str) (w : Wit Cells Tok MsgT) :
    (RR).relA a w ↔
      (∀ i, (sigOf cs l).decs (smpOf a.1) (wordsOf G cs l seat' (strsOf F a.2)) i =
        some (msgsOf cs l seat' arr w i)) ∧
      relIn (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) sym u3 dig).letters (recOf tl0 a.1)
        (msgsOf cs l seat' arr w) :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2⟩⟩

/-- The weight of a read, at these letters: off the statement's own list of tables. -/
theorem record_w (x : HTailF2) (μ : Fin (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.NM)
    (r : Fin ((OnBytes.Tie.Pv.Tail.sizeOf tl0).size.nr μ))
    (i : Fin ((OnBytes.Tie.Pv.Tail.sizeOf tl0).size.m μ)) :
    (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) sym u3 dig).letters.w x μ r i =
      wOf (OnBytes.Tie.Pv.Tail.sizeOf tl0) (phiAt Reading.gl x) μ r i := rfl

/-- **The kind's law in the plain form, there.** -/
theorem record_keepsW (hf : Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)
    (he : (Fintype.card (Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) /
      2 ^ (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).ior.red.KeepsW
      (RR).onA (RR).onB (RR).relA (RR).relB
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).err :=
  hear_keepsW (RR) hf (OnBytes.Tie.Pv.Tail.sizeOf_ok tl0) he

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.recordReads
#print axioms VerifiableInference.Desc.First.K8.record_onA
#print axioms VerifiableInference.Desc.First.K8.record_relA
#print axioms VerifiableInference.Desc.First.K8.record_w
#print axioms VerifiableInference.Desc.First.K8.record_keepsW
