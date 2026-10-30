-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7Pile.lean. riders_of_carry
follows Law/K7AtMgAll.lean, where
K7Riders' two fields take the table's promise in front and behind as premises: the debt hcarry has
them too (with them it is the weaker debt); pile_rides spends neither.

WHAT IT DOES NOT SHOW. No soundness. ONE OF THE TWO RIDERS OF THE NEXT TOKEN's LAW's CONDITION IS
PAID HERE (pile); THE OTHER (carry 23) STAYS A PREMISE. Nothing on whether "all rows on the table
are true" holds anywhere: only that it rides from behind the place to in front of it. No example.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on. "The pile": the
pending rows on the table (First/State.lean: S.rows). "pile" (the composed meaning's field;
K13/Law/FillK13.lean): all rows on the table are true of the witness, as the reader through the
state's own book reads it (K13/Law/ReaderByBook.lean: rwBook).
LETTERS. No "there is" in the conclusions.
OBJECT. The place "the entry of the head's link, then the next token's", in Law/ReplyRest.lean's
form; the piece at 338 (Law/K7AtMgAll.lean).
USER. Law/K07AtMg.lean: K7At's field riders: riders_of_carry makes it of the debt carry alone.
WHAT IT IS. THE PLACE LEAVES THE PILE, AND THE READER READS NEITHER THE FRESH GROUP NOR THE TOKEN:
SO "pile" RIDES.
place_rows: the rows on the table are the same in front and behind: in front the state stands
between the links, behind in the head's link: both read out.pending; the entry leaves "out" whole
(headFrontQ_rest), the next token's own sub-protocol leaves out.pending
(reply_rest).
reader_same: the reader's value at the state in front, at the witness with another token, is its
value at the state behind.
pile_rides: the first rider. riders_of_carry: K7Riders from its second debt alone.

-/
import Johnson.Desc.Kinds.Law.K7AtMgAll
import Johnson.Desc.Kinds.Law.TablesNotYet
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (HTailF2)
open OnBytes.Params (ReqLayout ReqShape)
open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc (Strs Place Block FileDescription Oracle KindName)
open VerifiableInference.Desc.First (S Numbers ModelPart Meaning PubData flatPlacesOf rowSegs sampledIn
  openSets start Item readsOpen pubHeld pubSets pubStep pubRowM pubOfItems stepOpen rowOf)
open VerifiableInference.Desc.K13 (indexIsC indexThereC)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_rest withFresh)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

/-- **The rows on the table are the same in front of the place and behind it.** -/
theorem place_rows (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
    (front : Block S Unit) (tl : HTailF2)
    (hfront : ∀ x rs gs x1, front.decide x rs gs = .ok x1 → headFrontQ tl x = .ok x1) :
    ∀ x rs gs t, (front.andThen name (Reply.blockOf W l)).decide x rs gs = .ok t →
      t.rows = x.rows := by
  intro x rs gs t h
  have h' : ((front.decide x (rs.take front.rounds.length) (gs.take front.openings)).bind fun s1 =>
      (Reply.blockOf W l).decide s1 (rs.drop front.rounds.length) (gs.drop front.openings))
      = .ok t := h
  cases hp : front.decide x (rs.take front.rounds.length) (gs.take front.openings) with
  | error e => rw [hp] at h'; cases h'
  | ok s1 =>
    rw [hp] at h'
    have hq := hfront _ _ _ _ hp
    obtain ⟨_, _, _, _, _, _, a7, _, _, a10⟩ := reply_rest l W.hS.V h'
    obtain ⟨o, ho, -⟩ := front_noTables hq
    obtain ⟨y, s₁, a, k⟩ := (VerifiableInference.Desc.First.K2.headFrontQ_iff tl x s1).1 hq
    have hx : x.here = .between := by
      have b := k.between
      unfold VerifiableInference.Desc.First.S.atBetween at b
      cases hh : x.here <;> rw [hh] at b <;> first | rfl | cases b
    unfold VerifiableInference.Desc.First.S.rows
    rw [a7, ho, hx, a10, (headFrontQ_rest hq).2.2.2.2.2.1]

variable {Xi P Tok Cl : Type} {rows cols nR : Nat} {Wp : OnBytes.Model.Verify.Public} {C : CK}
  {Fr : Frame} (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (c₀ : Fin rows → Fin cols → GE)
  (tab : Nat → Nat) (tokH : P × S → Fin ppref.V) (tokOf : P × S → Tok)
  (s : Nat → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat)
  (pl : Nat → Nat × Bool × Nat × Nat) (Rch : Nat → (P × S) × Fr.E.Str → Prop)

set_option quotPrecheck false in
/-- The reading, with the oracles' one decoder. -/
local notation "HID" => oneDec D.decT D.H

set_option quotPrecheck false in
/-- The filling of the letter headPart. -/
local notation "HP" => headPartK6 D.cs D.arr D.ms D.N s seat Wp pl tab D.put HID tokH

/-- The driver's list of places, at the full chain. -/
local notation "PS" => flatPlacesOf linksFull true

set_option quotPrecheck false in
/-- The piece over the verifier's state at 338 (Law/K7Seated.lean), before B, q and z. -/
local notation "PCW" =>
  pieceK7 D.cs D.arr D.N tokOf linksFull PS 338 D.G D.smp D.ms D.decT c₀

/-- The reader's value in front, at the witness with another token, is its value behind. -/
theorem reader_same (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
    (front : Block S Unit) (tl : HTailF2)
    (hfront : ∀ x rs gs x1, front.decide x rs gs = .ok x1 → headFrontQ tl x = .ok x1) (z : P) :
    ∀ x rs gs t, (front.andThen name (Reply.blockOf W l)).decide x rs gs = .ok t →
      ∀ (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (k : Tok),
        D.rw13 (z, x) ⟨w.cells, k, w.msg, w.pad⟩ = D.rw13 (z, t) w := by
  intro x rs gs t h w k
  obtain ⟨a1, a2, -⟩ := place_whole W l name front tl hfront x rs gs t h
  show VerifiableInference.Desc.K13.Law.rwBook D.arr D.mat13 (z, x) ⟨w.cells, k, w.msg, w.pad⟩ =
    VerifiableInference.Desc.K13.Law.rwBook D.arr D.mat13 (z, t) w
  unfold VerifiableInference.Desc.K13.Law.rwBook
  rw [a1, a2]
  rfl

/-- **THE FIRST RIDER.** -/
theorem pile_rides (B : Block S Cl)
    (q : Piece C Fr (P × S) Cl (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
    (tl : HTailF2)
    (hyes : ∀ x rs gs t, B.decide x rs gs = .ok t →
      ∃ rs' gs', (front.andThen name (Reply.blockOf W l)).decide x rs' gs' = .ok t)
    (hfront : ∀ x rs gs x1, front.decide x rs gs = .ok x1 → headFrontQ tl x = .ok x1) :
    ∀ (z : P) a τ b (w : Wit (Fin rows → Fin cols → GE) Tok MsgT),
      (PCW B q z).ior.red.out a τ = some b →
      (mgAll D Mg).pile (z, b.1) (strsOf Fr b.2) w →
      (mgAll D Mg).pile (z, a.1) (strsOf Fr a.2) ⟨w.cells, tokOf (z, b.1), w.msg, w.pad⟩ := by
  intro z a τ b w hb h
  obtain ⟨rs, gs, hy⟩ := Came.piece_yes hyes z a τ b hb
  have e1 := place_rows W l name front tl hfront _ _ _ _ hy
  have e2 := reader_same D W l name front tl hfront z _ _ _ _ hy w (tokOf (z, b.1))
  intro r hr
  have h0 := h r (by show r ∈ b.1.rows; rw [e1]; exact hr)
  show VerifiableInference.Desc.K13.Law.Holds _ (D.rw13 (z, a.1) _) r
  rw [e2]
  exact h0

/-- **The field riders, of its second debt alone.** -/
theorem riders_of_carry (B : Block S Cl)
    (q : Piece C Fr (P × S) Cl (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
    (tl : HTailF2)
    (hyes : ∀ x rs gs t, B.decide x rs gs = .ok t →
      ∃ rs' gs', (front.andThen name (Reply.blockOf W l)).decide x rs' gs' = .ok t)
    (hfront : ∀ x rs gs x1, front.decide x rs gs = .ok x1 → headFrontQ tl x = .ok x1)
    (hcarry : ∀ (z : P) a τ b (w : Wit (Fin rows → Fin cols → GE) Tok MsgT),
      (PCW B q z).ior.red.out a τ = some b → Rch 338 ((z, a.1), a.2) →
      onQ D.N (mgAll D Mg) linksFull PS (fun x => (z, x)) 338 a →
      onQ D.N (mgAll D Mg) linksFull PS (fun x => (z, x)) (338 + 1) b →
      (mgAll D Mg).carry 23 (z, b.1) (strsOf Fr b.2) w →
      (mgAll D Mg).carry 23 (z, a.1) (strsOf Fr a.2) ⟨w.cells, tokOf (z, b.1), w.msg, w.pad⟩) :
    K7Riders D Mg c₀ tokOf Rch B q :=
  ⟨fun z a τ b w hb _ _ _ h =>
      pile_rides D Mg c₀ tokOf B q W l name front tl hyes hfront z a τ b w hb h,
    hcarry⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.place_rows
#print axioms VerifiableInference.Desc.Kinds.Head.Law.reader_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.pile_rides
#print axioms VerifiableInference.Desc.Kinds.Head.Law.riders_of_carry
