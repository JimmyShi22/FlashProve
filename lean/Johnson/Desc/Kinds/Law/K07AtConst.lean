-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K07AtConst.lean.
WHAT IT DOES NOT SHOW. No soundness. STILL A RULE UNDER A BILL: NO MEMBER, NO EXAMPLE: NOTHING
COUNTS AS PROVED. carry 23 IS A NAMED PREMISE (one of hall's two riders): NOTHING HERE LEANS ON WHAT
THE CLOSED STRUCTURE LAYS AS ITS SENTENCE "carry".
NOT THE FORM IN WHICH A KIND's LAW ENDS (P5J/RowsAtMg.lean: AtMg.Kind):
the row of pieces, the reached-condition Rch and the committed table's start c₀ are still letters
here, and the links' sorts are spelt linksFull (Law/K7AtTerms.lean: fullLinks_is: the two spellings
are one). hall KEEPS: SeatOf, q.b, yes, front · book · told · the fence · Wp.hS = W.hS · THE TWO
RIDERS (pile, carry 23). hseg STAYS A PREMISE (its payer, headLink_in_scope,
stands in a file that does not lie beneath this one).
WORDS. "The closed constant": P5J/MgAtAll.lean: mgAtAll h: the composed meaning at the table's
files' structure of parameters with all 29 fields at terms, over the closed meaning beneath.
LETTERS. No "there is" but hall's own. dAt h (Law/DAtConst.lean): that structure of parameters,
under that file's name for it.
OBJECT. Law/K7AtHid.lean's k7_kindTied_hid; its five premises that say what a parameter is: hhead,
hput, hsmpIs, hdecIs, hHIs; and hplan.
USER. The next token's law in the counted form.
WHAT IT IS. AT THE CLOSED CONSTANT THE FIVE EQUATIONS HOLD BY DEFINITION: LEAN TAKES rfl FOR EACH;
AND hplan IS PAID IN SCOPE (Goal/Meaning/HeadCondScope.lean: ok_in_scope, at the head's own three
fields scope, reads, pubOne).
  decT_pub          the decoder, as a function of the cells and the public part alone.
  k07_at_const      the statement.

-/
import Johnson.Desc.Kinds.Law.DAtConst
import Johnson.Desc.Kinds.Law.K7AtHid
import Johnson.Goal.Meaning.HeadCondScope

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

open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Cl : Type} {C : CK} {Fr : Frame}

/-- The driver's list of places, at the full chain. -/
local notation "PS" => flatPlacesOf linksFull true

/-- The decoder, as a function of the cells and the public part alone. -/
noncomputable def decT_pub (h : P5J.AtMgA o Z D r Zp Np cF x) :
    (Nat → Option (Nat × List UInt64)) → ProofFile.InstPub →
      Option (Fin OnBytes.Flat.numsFull.rows → Fin (P5J.colsAt OnBytes.Flat.numsFull) → GE) :=
  fun c z =>
    Desc.K14.Law.decK (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0 2852142980
      (Desc.K14.Law.rankLib (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S.fold)
      (Desc.K14.Law.heldFull (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
        (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
        (Desc.K14.Law.full_index (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
          h.plan.shape) OnBytes.Flat.numsFull _ (P5J.At.EAt Z))
      c ((P5J.F0T o Zp Np cF).start₂ z)

/-- **THE NEXT TOKEN's KIND's SHARE AT THE CLOSED CONSTANT.** -/
theorem k07_at_const (h : P5J.AtMgA o Z D r Zp Np cF x)
    (c₀ : Fin OnBytes.Flat.numsFull.rows → Fin (P5J.colsAt OnBytes.Flat.numsFull) → GE)
    (Rch : Nat → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (hseg : headLink (P5J.At.X Zp) = 24)
    (row : List (Piece C Fr (ProofFile.InstPub × S) Cl
      (Wit (Fin OnBytes.Flat.numsFull.rows → Fin (P5J.colsAt OnBytes.Flat.numsFull) → GE) Nat
        MsgT)))
    (hall : ∀ q, row[338]? = some q →
      ∃ (B Bst : Block S Cl) (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
        (front : Block S Unit) (tl : HTailF2) (told : List (List Oracle)),
        SeatOf Bst B ∧ q.b = (Sound.below B).lift Prod.snd (fun t y => (t.1, y)) ∧
        (∀ y rs gs t, B.decide y rs gs = .ok t →
          ∃ rs' gs', (front.andThen name (Reply.blockOf W l)).decide y rs' gs' = .ok t) ∧
        (∀ y rs gs y1, front.decide y rs gs = .ok y1 → headFrontQ tl y = .ok y1) ∧
        First.bookFit (dAt h).N PS told = true ∧ told[338]? = some [] ∧
        (∀ y ∈ sampledIn (dAt h).N ((openSets linksFull PS (start linksFull))[338]?.getD []),
          y.1 < q.base) ∧
        (P5J.At.X Zp).hS = W.hS ∧ K7Riders (dAt h) mgBase c₀ P5J.tokOfHeard Rch B q) :
    KindTiedR (dAt h).N (P5J.mgAtAll h) linksFull PS Rch
      (fun i => extQAt (dAt h).cs (dAt h).G (dAt h).arr (dAt h).smp (dAt h).ms (dAt h).decT c₀
        P5J.tokOfHeard (dAt h).N linksFull PS (fun a => a) i)
      row .K7 :=
  k7_kindTied_hid (dAt h) c₀ (P5J.At.tabH x) (_root_.Meaning.sizesOf (P5J.At.X Zp))
    (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)) (plAt (P5J.At.num Zp 24 0) 0) Rch
    hseg rfl rfl (InScope.ok_in_scope h.scope h.reads h.pubOne _) (P5J.At.seats Zp) rfl
    (decT_pub h) rfl
    (_root_.Meaning.sizesOf (P5J.At.X Zp))
    (_root_.Meaning.seatBy (_root_.Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp)
      (_root_.Meaning.sizesOf (P5J.At.X Zp)))
    (fun z => (_root_.Meaning.backReq (P5J.At.reqB z)).getD P5J.At.d₀)
    (fun a y => (dAt h).decT y.cell a) h.plan.hN h.plan.hG rfl row hall

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07_at_const
