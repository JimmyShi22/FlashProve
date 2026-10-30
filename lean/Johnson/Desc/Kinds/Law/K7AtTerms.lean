-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7AtTerms.lean.
WHAT IT DOES NOT SHOW. No soundness. STILL A RULE UNDER A BILL: NO MEMBER: hall is
Law/K7AtMgAll.lean's, untouched (K7Rest's six fields, the fence, Wp.hS = W.hS, the two riders);
hseg, hhead, hplan and hbase stay as there. THE THREE EQUATIONS hput, hsmpIs, hdecIs ARE PREMISES ON
THE STRUCTURE OF PARAMETERS D: that the table's files' closed structure meets them is read in their
texts (P5J/LettersAt.lean: put := putReq · smp := smpNamed (cs Zp) (seats Zp) · decT := dtK ...,
whose text hands the state's public part alone to the shared chain's decoder) AND NOT SHOWN HERE:
these files do not lie beneath this one. No example.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on. K7Leaves
(Law/K7AtMgAll.lean): what the next token's place leaves of it.
LETTERS. No "there is" but hall's own. sts: the list of seats at which the samples' reader is named.
g: what the decoder is, as a function of the committed table's cells and the public part.
OBJECT. Law/K7AtMgAll.lean's k7_kindTied_mgBase, and three of its seven premises on parameters: hK,
hsmp, hdecT.
USER. The next token's law at the table's files' closed constant (P5J/MgAtConst.lean: mgAt: mgAll
at the head's own structure of parameters, over mgBase).
WHAT IT IS. THREE PREMISES THAT SAID "THE PARAMETER DOES NOT READ WHAT THE PLACE TURNS" GIVE WAY TO
THREE EQUATIONS THAT SAY WHAT THE PARAMETER IS.
  fullLinks_is      the two spellings of the full chain's links' sorts are one (by definition).
  smpAt_of_oracles, smpNamed_of_oracles   the named reader of samples reads of the statement its
                    oracle messages alone.
  smpNamed_leaves   so it is the same at two states with K7Leaves.
  req_of_pub        a reading whose "req" reads the public part alone pays the bill's field req.
  k7_kindTied_terms the statement.
NEAREST RELATIVES: Law/HeadCutsK6.lean: Came.putReq_keeps (called) · Desc/Sound/SmpNamed.lean:
smpNamed_at, smpNamed_none (what the reader is at a seat; nothing on two states).

-/
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.Kinds.Law.K7AtMgAll

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

/-- The two spellings of the full chain's links' sorts are one. -/
theorem fullLinks_is : P5J.fullLinks = linksFull := rfl

/-- The kind's own reading of a sample reads of the statement its oracle messages alone. -/
theorem smpAt_of_oracles (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e : Nat)
    {St St' : OnBytes.Statement} (h : St'.oracles = St.oracles) (o : Nat) :
    Desc.K1.smpAt cs sh e St' o = Desc.K1.smpAt cs sh e St o := by
  obtain ⟨c, os, gr⟩ := St
  obtain ⟨c', os', gr'⟩ := St'
  obtain rfl : os' = os := h
  rfl

/-- So does the named reader of samples. -/
theorem smpNamed_of_oracles {P : Type} (cs : OnBytes.Codes) (sts : List (Nat × Nat)) (z : P)
    (x t : S) (h : t.st.oracles = x.st.oracles) :
    smpNamed cs sts (z, t) = smpNamed cs sts (z, x) := by
  funext sd i
  unfold smpNamed smp1At
  split
  · exact smpAt_of_oracles cs _ _ h _
  · rfl

/-- It is the same at two states that agree in what the next token's place leaves. -/
theorem smpNamed_leaves {P : Type} (cs : OnBytes.Codes) (sts : List (Nat × Nat)) (z : P)
    (x t : S) (h : K7Leaves x t) : smpNamed cs sts (z, t) = smpNamed cs sts (z, x) :=
  smpNamed_of_oracles cs sts z x t h.2.1

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

/-- A reading whose "req" reads the public part alone pays the bill's field req. -/
theorem req_of_pub (r : P → P5J.TReq) (hreqIs : D.H.req = fun a => r a.1) :
    ∀ (z : P) (x t : S), t.req = x.req → (HID).req (z, t) = (HID).req (z, x) := by
  intro z x t _
  show D.H.req (z, t) = D.H.req (z, x)
  rw [hreqIs]

/-- **THE NEXT TOKEN's KIND's SHARE, WHERE THREE PARAMETERS ARE WHAT THE CLOSED STRUCTURE LAYS.** -/
theorem k7_kindTied_terms (hseg : headLink Wp = 24) (hhead : D.headPart = HP)
    (hput : D.put = OnBytes.Flat.putReq) (hplan : (parOf Wp.hS (workOf Wp)).ok = true)
    (hbase : ∀ (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (t : Tok),
      D.H.base 24 w → D.H.base 24 ⟨w.cells, t, w.msg, w.pad⟩)
    (sts : List (Nat × Nat)) (hsmpIs : D.smp = smpNamed D.cs sts)
    (g : (Nat → Option (Nat × List UInt64)) → P → Option (Fin rows → Fin cols → GE))
    (hdecIs : D.decT = fun c x => g c x.1)
    (row : List (Piece C Fr (P × S) Cl (Wit (Fin rows → Fin cols → GE) Tok MsgT)))
    (hall : ∀ q, row[338]? = some q →
      ∃ (B Bst : Block S Cl) (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
        (front : Block S Unit) (tl : HTailF2) (told : List (List Oracle)),
        SeatOf Bst B ∧ q.b = (Sound.below B).lift Prod.snd (fun t x => (t.1, x)) ∧
        K7Rest D.N Wp HID tokH tokOf PS 338 B W l name front tl told ∧
        (∀ x ∈ sampledIn D.N ((openSets linksFull PS (start linksFull))[338]?.getD []),
          x.1 < q.base) ∧
        Wp.hS = W.hS ∧ K7Riders D mgBase c₀ tokOf Rch B q) :
    KindTiedR D.N (mgAll D mgBase) linksFull PS Rch
      (fun i => extQAt D.cs D.G D.arr D.smp D.ms D.decT c₀ tokOf D.N linksFull PS (fun a => a) i)
      row .K7 :=
  k7_kindTied_mgBase D c₀ tab tokH tokOf s seat pl Rch hseg hhead (hput ▸ Came.putReq_keeps) hplan
    hbase (fun z x t h => by rw [hsmpIs]; exact smpNamed_leaves D.cs sts z x t h)
    (fun c z x t _ => by rw [hdecIs]) row hall

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.fullLinks_is
#print axioms VerifiableInference.Desc.Kinds.Head.Law.smpNamed_of_oracles
#print axioms VerifiableInference.Desc.Kinds.Head.Law.req_of_pub
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k7_kindTied_terms
