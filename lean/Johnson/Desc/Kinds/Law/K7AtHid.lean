-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7AtHid.lean.
WHAT IT DOES NOT SHOW. No soundness. STILL A RULE UNDER A BILL: NO MEMBER, NO EXAMPLE. hall KEEPS:
that the piece at 338 holds a sub-protocol whose acceptance is "the entry of the head's link, then
the next token's" (SeatOf, q.b, yes, front) · book · told · the fence · Wp.hS = W.hS · THE TWO
RIDERS (pile, carry 23). hseg, hhead, hplan stay. THE FOUR EQUATIONS hput, hsmpIs, hdecIs, hHIs ARE
PREMISES ON THE STRUCTURE OF PARAMETERS D: that the table's files' closed structure meets them is
read in their texts (P5J/LettersAt.lean: H := hidAtList ..., which unfolds through hidAtPlan to
hidAtSeat at tokVOf, with req := fun a => (backReq (reqB a.1)).getD d₀) AND NOT SHOWN HERE.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on. "The reading":
how a witness is read (P5J/MeansQ.lean: HidAt, hidAtSeat).
LETTERS. No "there is" but hall's own. sH, seatH: the sizes and seats at which the reading is made
(they need not be s, seat, at which the head's part is filled). r: the request, as a function of the
public part. dec: the reading's own decoder (the composed meaning lays its one decoder over it).
OBJECT. Law/K7AtTerms.lean's k7_kindTied_terms; its premise hbase; the bill's fields req and tok.
USER. The next token's law at the table's files' closed constant.
WHAT IT IS. WHERE THE READING IS hidAtSeat AT THE TABLE's TOKEN TERMS, WITH A REQUEST OFF THE PUBLIC
PART: hbase, req AND tok ARE PAID: THE BILL's OTHER PART SHRINKS FROM SIX FIELDS TO FOUR.
  base_hidAtSeat    the reading's "base" does not read the witness's token.
  k7_kindTied_hid   the statement.
NEAREST RELATIVES: Law/K7TokTerms.lean: tok_terms (called in substance: by definition) ·
Law/K7AtTerms.lean: req_of_pub (called).

-/
import Johnson.Desc.Kinds.Law.K7AtTerms

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

variable {Xi P Cl : Type} {rows cols nR : Nat} {Wp : OnBytes.Model.Verify.Public} {C : CK}
  {Fr : Frame} (D : MgData Xi P Nat rows cols nR Wp) (c₀ : Fin rows → Fin cols → GE)
  (tab : Nat → Nat)
  (s : Nat → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat)
  (pl : Nat → Nat × Bool × Nat × Nat) (Rch : Nat → (P × S) × Fr.E.Str → Prop)

set_option quotPrecheck false in
/-- The reading, with the oracles' one decoder. -/
local notation "HID" => oneDec D.decT D.H

set_option quotPrecheck false in
/-- The filling of the letter headPart. -/
local notation "HP" => headPartK6 D.cs D.arr D.ms D.N s seat Wp pl tab D.put HID P5J.tokHOf

/-- The driver's list of places, at the full chain. -/
local notation "PS" => flatPlacesOf linksFull true

/-- The reading's "base" does not read the witness's token. -/
theorem base_hidAtSeat {P : Type} {rows cols : Nat} (Wp : OnBytes.Model.Verify.Public)
    (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (ms : List Mem) (N : Numbers)
    (sH : Nat → Cb.Pv.Tail.Size) (seatH : ∀ k, Fin (sH k).NM → Nat → Nat → Nat × Nat × Nat)
    (tokV : Nat → Fin ppref.V) (req : P × S → P5J.TReq)
    (dec : P × S → Strs → Option (Fin rows → Fin cols → GE)) (hSN : SeatsNamed arr N sH seatH)
    (hGS : GroupsSeated ms N) (k : Nat) (w : Wit (Fin rows → Fin cols → GE) Nat MsgT) (t : Nat)
    (h : (P5J.hidAtSeat Wp cs arr ms N sH seatH tokV req dec hSN hGS).base k w) :
    (P5J.hidAtSeat Wp cs arr ms N sH seatH tokV req dec hSN hGS).base k
      ⟨w.cells, t, w.msg, w.pad⟩ := h

/-- **THE NEXT TOKEN's KIND's SHARE, WHERE THE READING TOO IS WHAT THE CLOSED STRUCTURE LAYS.** -/
theorem k7_kindTied_hid (hseg : headLink Wp = 24) (hhead : D.headPart = HP)
    (hput : D.put = OnBytes.Flat.putReq) (hplan : (parOf Wp.hS (workOf Wp)).ok = true)
    (sts : List (Nat × Nat)) (hsmpIs : D.smp = smpNamed D.cs sts)
    (g : (Nat → Option (Nat × List UInt64)) → P → Option (Fin rows → Fin cols → GE))
    (hdecIs : D.decT = fun c x => g c x.1)
    (sH : Nat → Cb.Pv.Tail.Size) (seatH : ∀ k, Fin (sH k).NM → Nat → Nat → Nat × Nat × Nat)
    (r : P → P5J.TReq) (dec : P × S → Strs → Option (Fin rows → Fin cols → GE))
    (hSN : SeatsNamed D.arr D.N sH seatH) (hGS : GroupsSeated D.ms D.N)
    (hHIs : D.H = P5J.hidAtSeat Wp D.cs D.arr D.ms D.N sH seatH P5J.tokVOf (fun a => r a.1) dec
      hSN hGS)
    (row : List (Piece C Fr (P × S) Cl (Wit (Fin rows → Fin cols → GE) Nat MsgT)))
    (hall : ∀ q, row[338]? = some q →
      ∃ (B Bst : Block S Cl) (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
        (front : Block S Unit) (tl : HTailF2) (told : List (List Oracle)),
        SeatOf Bst B ∧ q.b = (Sound.below B).lift Prod.snd (fun t x => (t.1, x)) ∧
        (∀ x rs gs t, B.decide x rs gs = .ok t →
          ∃ rs' gs', (front.andThen name (Reply.blockOf W l)).decide x rs' gs' = .ok t) ∧
        (∀ x rs gs x1, front.decide x rs gs = .ok x1 → headFrontQ tl x = .ok x1) ∧
        First.bookFit D.N PS told = true ∧ told[338]? = some [] ∧
        (∀ x ∈ sampledIn D.N ((openSets linksFull PS (start linksFull))[338]?.getD []),
          x.1 < q.base) ∧
        Wp.hS = W.hS ∧ K7Riders D mgBase c₀ P5J.tokOfHeard Rch B q) :
    KindTiedR D.N (mgAll D mgBase) linksFull PS Rch
      (fun i => extQAt D.cs D.G D.arr D.smp D.ms D.decT c₀ P5J.tokOfHeard D.N linksFull PS
        (fun a => a) i)
      row .K7 := by
  refine k7_kindTied_terms D c₀ tab P5J.tokHOf P5J.tokOfHeard s seat pl Rch hseg hhead hput hplan
    ?_ sts hsmpIs g hdecIs row fun q hq => ?_
  · intro w t h
    rw [hHIs] at h ⊢
    exact base_hidAtSeat Wp D.cs D.arr D.ms D.N sH seatH P5J.tokVOf _ dec hSN hGS 24 w t h
  · obtain ⟨B, Bst, W, l, name, front, tl, told, h1, h2, hy, hf, hb, ht, hfe, hS, hR⟩ := hall q hq
    refine ⟨B, Bst, W, l, name, front, tl, told, h1, h2,
      ⟨hy, hf, hb, ht, req_of_pub D r (by rw [hHIs]; rfl), fun b w => ?_⟩, hfe, hS, hR⟩
    show (D.H.hid ⟨w.cells, P5J.tokOfHeard b, w.msg, w.pad⟩).tok = P5J.tokHOf b
    rw [hHIs]
    rfl

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.base_hidAtSeat
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k7_kindTied_hid
