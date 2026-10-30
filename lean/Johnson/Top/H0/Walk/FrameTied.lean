-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameTied.lean: what the link's frame's blocks owe in the chain of promises, in
the letters of the table of joints (Johnson/Desc/First/Borders.lean: onAt;
Johnson/Desc/Sound/BordersQ.lean: onQ; Johnson/Desc/Sound/ChainOfPromises.lean: TiedAt).
Definitions of Props alone: no theorem stands here. The proofs: FrameTiedLaid.lean,
FrameTiedCleared.lean. What the steps do to the record: FrameGives.lean.

  (Stays base y y': of the oracles' strings: the stored table's cells, and every column of a tree
                   whose number is below base, are in y' what they are in y: Stays.lean)
  Sits get q f     the piece q's step on the first chain's state is f: a yes of q from a to b is
                   f's yes from a's state to b's; what was handed to the chain is unturned; the
                   oracles' strings stay, as far as they were sent in front of q (Stays q.base)
  LaysNothing q    q's extractor is the identity (the table's rows: lays := false)
  NoneBetween      the plan's numbers of trees and of messages are the same at the two borders of a
                   block
  DoorIdle         the promise's row at the block's place, with the door's filling, makes nothing:
                   no premise of a tie: a help for whoever pays LettersRide's field "pub"
                   (FrameTiedStep.lean: pub_of_kept)
  LaidTied         "link m: laid": TiedAt, under Sits at layFront m, NoneBetween, and LettersRide
                   at "the record is handed on"
  FrontTied        the chain's front, where it is the block that asks nothing: the like. That block
                   is no text of the frame's
  LettersRide      what is asked of the table's letters at a step rel of the record, the strings
                   staying below base: forward: decodes; and, FROM THE WHOLE PROMISE IN FRONT
                   (FrontAt): inOrder, the open public items' Bools and what they say beside, held,
                   shown, noColl; backward: every open item
  PileGivesWo      the pile behind gives the claim on the weights in front
  ClearedTiedAtt   "link m: cleared", an attention segment: TiedAt, under Sits, NoneBetween and
                   LettersRide
  ClearedTiedRow   "link m: cleared", a layers' or the head's segment: the like, with PileGivesWo

The flag "a row is left" (X.fv) is no premise of the two: no proof of a tie spends it. It is spent
by whoever pays PileGivesWo (a row is laid only where the flag says so: ClearedRec) and, at an
attention segment, LettersRide's field "items" at the pile (it is unturned only where the flag says
no).

Limits. EVERY TIE RESTS ON PREMISES THAT ARE SHOWN NOWHERE: Sits and LaysNothing of no piece of any
description (but see `sits_lift`, Johnson/P1L20R/FrameSits.lean: Sits at a piece that holds a block
which says yes only where the frame's does); NoneBetween at no plan's numbers (but see
FrameFit.lean); LettersRide and PileGivesWo at no filling of the table's letters (but see
FrameWo.lean). N, Mg, links, ps and get are letters. No soundness statement.

-/
import Johnson.Desc.Sound.ChainOfPromises
import Johnson.Top.H0.Walk.Stays
import Johnson.Top.H0.Walk.FrameGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers Pub Stand standAt standOf mayWait
  shift openSets pubSets pubRowM pubOfItems sampledIn start onAt)
open VerifiableInference.Desc.First.Pend (pendingRowO)

/-! ### how a block of the frame stands as a piece -/

/-- A yes of q from a to b is f's yes from a's state to b's; what was handed to the chain is
unturned; the strings stay below q's base. -/
def Sits {A Cl P W : Type} {C : CK} {Fr : Frame} (get : A → P × S) (q : Piece C Fr A Cl W)
    (f : S → Except String S) : Prop :=
  ∀ a τ b, q.ior.red.out a τ = some b →
    (get b.1).1 = (get a.1).1 ∧ f (get a.1).2 = .ok (get b.1).2 ∧
      Stays q.base (strsOf Fr a.2) (strsOf Fr b.2)

/-- The extractor is the identity. -/
def LaysNothing {A Cl W : Type} {C : CK} {Fr : Frame} (q : Piece C Fr A Cl W) : Prop :=
  ∀ a τ w, q.ext a τ w = w

/-- The plan's numbers of trees and of messages are the same in front of block k and behind it. -/
def NoneBetween (N : Numbers) (ps : List Place) (k : Nat) : Prop :=
  N.treesAt ps[k + 1]? = N.treesAt ps[k]? ∧ N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?

/-- The promise's row at the place, with the door's filling, makes no public item. -/
def DoorIdle {P W : Type} (Mg : Meaning P W) (links : List ModelPart) (p : Place) : Prop :=
  (pubRowM Mg.more links p).makes = []

/-- The step's own yes, as a relation on the record. -/
def Yes (f : S → Except String S) : S → S → Prop := fun s t => f s = .ok t

/-- **What is asked of the table's letters** at a step rel of the record (the ties hand in: THE
STEP's OWN YES: so its payer has every law of the step in hand), the strings staying below base.
In : WHAT IS KNOWN IN FRONT OF THE BLOCK (the ties hand in: the table's whole promise at the border
in front): every field but "decodes" may spend it: so a clause behind may be earned from ANOTHER
clause in front; every field but "decodes" is asked at a verifier's state without a mark alone
(where a mark is borne the promise says nothing but "decodes", and a tie asks nothing else). O, Q:
the items and the public items that are open BEHIND the block, as the promise reads them (lists);
Op: the items that are open behind it, as the relation reads them. -/
structure LettersRide {P W : Type} (N : Numbers) (Mg : Meaning P W) (rel : S → S → Prop)
    (base : Nat) (In : P × S → VerifiableInference.Desc.Strs → Prop) (O : List Item)
    (Q : List Pub) (Op : Item → Prop) : Prop where
  decodes : ∀ p s t y y', rel s t → Stays base y y' → Mg.decodes (p, s) y → Mg.decodes (p, t) y'
  inOrder : ∀ p s t y, rel s t → s.failed = none → In (p, s) y → Mg.inOrder (p, t) = true
  pub : ∀ p s t y q, rel s t → s.failed = none → In (p, s) y → q ∈ Q ++ pubOfItems O →
    Mg.pub q (p, t) = true
  pubP : ∀ p s t y q, rel s t → s.failed = none → In (p, s) y → q ∈ Q → Mg.pubP q (p, t)
  held : ∀ p s t y x, rel s t → s.failed = none → In (p, s) y → x ∈ sampledIn N O →
    Mg.held x.1 x.2 (p, t) = true
  shown : ∀ p s t y y' x, rel s t → Stays base y y' → s.failed = none → In (p, s) y →
    x ∈ sampledIn N O → Mg.shown x.1 x.2 y'
  noColl : ∀ p s t y y' x, rel s t → Stays base y y' → s.failed = none → In (p, s) y →
    x ∈ sampledIn N O → Mg.noColl x.1 x.2 (p, t) y'
  items : ∀ p s t y y' w i, rel s t → Stays base y y' → s.failed = none → In (p, s) y → Op i →
    i.holds N Mg (p, t) y' w → i.holds N Mg (p, s) y w

/-- What the ties hand to LettersRide as known in front of block k: the table's promise at border k.
-/
def FrontAt {P W : Type} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
    (k : Nat) : P × S → VerifiableInference.Desc.Strs → Prop :=
  fun a y => onAt N Mg links ps[k]? ((openSets links ps (start links))[k]?.getD [])
    ((pubSets Mg.more links ps)[k]?.getD []) a y

/-! ### «laid», and the chain's front -/

/-- **«link m: laid».** k: its number in the flat list; p': the place of the link's first block. -/
def LaidTied : Prop :=
  ∀ (A Cl P W : Type) (C : CK) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × S) (k m : Nat) (p' : Place) (q : Piece C Fr A Cl W),
    ps[k]? = some ⟨1, some m, 0, KindName.frame⟩ → ps[k + 1]? = some p' → p'.link = some m →
    p'.piece = 1 → NoneBetween N ps k →
    Sits get q (layFront m) → LaysNothing q →
    LettersRide N Mg (Yes (layFront m)) q.base (FrontAt N Mg links ps k)
      ((openSets links ps (start links))[k + 1]?.getD [])
      ((pubSets Mg.more links ps)[k + 1]?.getD [])
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1)) →
    TiedAt N Mg links ps get k q

/-- **The chain's front**, where it is the block that asks nothing. -/
def FrontTied : Prop :=
  ∀ (A Cl P W : Type) (C : CK) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × S) (q : Piece C Fr A Cl W),
    ps[0]? = some ⟨1, none, 0, KindName.frame⟩ → ps[1]? = some ⟨1, some 0, 0, KindName.frame⟩ →
    NoneBetween N ps 0 →
    Sits get q .ok → LaysNothing q →
    LettersRide N Mg (Yes .ok) q.base (FrontAt N Mg links ps 0)
      ((openSets links ps (start links))[1]?.getD []) ((pubSets Mg.more links ps)[1]?.getD [])
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) 1) →
    TiedAt N Mg links ps get 0 q

/-! ### «cleared» -/

/-- The pile behind gives the claim on the weights in front. -/
def PileGivesWo {P W : Type} (Mg : Meaning P W) (m : Nat) (rel : S → S → Prop) (base : Nat)
    (In : P × S → VerifiableInference.Desc.Strs → Prop) : Prop :=
  ∀ p s t y y' w, rel s t → Stays base y y' → In (p, s) y → Mg.pile (p, t) y' w →
    Mg.wo m (p, s) y w

/-- **«link m: cleared», an attention segment.** -/
def ClearedTiedAtt : Prop :=
  ∀ (A Cl P W : Type) (C : CK) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × S) (k m : Nat) (p' : Place) (q : Piece C Fr A Cl W)
    (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut) (lay : WsLay)
    (lin : Params.LinShape),
    links[m]? = some ModelPart.attention → ps[k]? = some ⟨1, some m, 13, KindName.frame⟩ →
    mayWait links ⟨1, some m, 13, KindName.frame⟩ = false →
    ps[k + 1]? = some p' → standAt links p' = Stand.between →
    NoneBetween N ps k →
    Sits get q (clearWith X counts left fun im w n os => pendingRowO lay im w n lin os) →
    LaysNothing q →
    LettersRide N Mg (Yes (clearWith X counts left fun im w n os => pendingRowO lay im w n lin os))
      q.base (FrontAt N Mg links ps k)
      ((openSets links ps (start links))[k + 1]?.getD [])
      ((pubSets Mg.more links ps)[k + 1]?.getD [])
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1)) →
    TiedAt N Mg links ps get k q

/-- **«link m: cleared», a layers' or the head's segment.** -/
def ClearedTiedRow : Prop :=
  ∀ (A Cl P W : Type) (C : CK) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × S) (k m : Nat) (sub : ModelPart) (p' : Place)
    (q : Piece C Fr A Cl W) (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (lay : WsLay) (lin : Params.LinShape),
    links[m]? = some sub → sub ≠ ModelPart.attention →
    ps[k]? = some ⟨1, some m, 13 + 2 * shift sub, KindName.frame⟩ →
    mayWait links ⟨1, some m, 13 + 2 * shift sub, KindName.frame⟩ = false →
    ps[k + 1]? = some p' → standAt links p' = Stand.between →
    NoneBetween N ps k →
    Sits get q (clearWith X counts left fun im w n os => pendingRowO lay im w n lin os) →
    LaysNothing q →
    LettersRide N Mg (Yes (clearWith X counts left fun im w n os => pendingRowO lay im w n lin os))
      q.base (FrontAt N Mg links ps k)
      ((openSets links ps (start links))[k + 1]?.getD [])
      ((pubSets Mg.more links ps)[k + 1]?.getD [])
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1)) →
    PileGivesWo Mg m (Yes (clearWith X counts left fun im w n os => pendingRowO lay im w n lin os))
      q.base (FrontAt N Mg links ps k) →
    TiedAt N Mg links ps get k q

end Johnson.Desc.First.Walk.Tied
