-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K07AtMg.lean.
K7Cond's field riders is
Law/K7AtMgAll.lean's K7Riders, which
takes, beside "reached", in each of its two debts: the table's promise at the state in front and at
the state behind.
pile IS PAID (Law/K7Pile.lean:
pile_rides; riders_of_carry makes the field of carry 23 alone).
WHAT IT DOES NOT SHOW. No soundness. A RULE UNDER ONE NAMED CONDITION, K7Cond: NO MEMBER OF IT IS
SHOWN IN LEAN: NOTHING COUNTS AS PROVED. What speaks for each field's being payable at the release's
own files stands on a page of this project that is not in this repository, field by field, not here.
carry 23 IS A DEBT OF THE CONDITION: nothing here leans on what the closed structure lays as that
sentence. THE CONDITION AND THE LAW
HAVE CONTENT ONLY AT AN L WHOSE THREE LISTS ARE THE IOP's OWN (AtMg.ofDesc's q₁, q₂, q₃): never
"for all L". THE FULL SIZE ALONE (338 and 24 are literals).
WORDS. "The closed constant": P5J/MgAtAll.lean: mgAtAll h. "The counted form": P5J/RowsAtMg.lean:
AtMg.Kind: the form in which a kind's files end their law. "Tells" (Desc/Sound/PieceFence.lean:
toldOf): the oracle messages beneath the roots that a sub-protocol sends.
LETTERS. "There is" in K7Cond, at the piece q that stands at 338: B, Bst: the sub-protocol that q
holds beneath the lift over the public part, and what the seat lays · W, l, name, front, tl: the
letters of "the entry of the head's link, then the next token's" · numD, bs: the maker's numbering
of declared sources and the chain's list of sub-protocols, at which q is the 338th piece. None is
pinned by the statement; each is pinned by the field that names it.
OBJECT. The next token's place, number 338 of the first chain, at the closed constant.
USER. The join of the kinds' laws (P5J/RowsAtMg.lean: good_of_kinds, rows_at_mg).
WHAT IT IS. THE NEXT TOKEN's LAW IN THE COUNTED FORM, UNDER ONE NAMED CONDITION.
  K7At              the condition at the piece: eleven fields, twelve debts (riders holds two).
  K7Cond            at whatever piece stands at 338.
  k07_of_cond       the rule at letters c₀, Rch, row.
  k07_law           **K7Cond ... → h.toAtMg.Kind (dAt h) L .K7.**
WHAT THE TWELVE DEBTS ARE. ON THE PIECE AND ITS SUB-PROTOCOL: seat, lift, yes, front, shape, more.
THREE TESTS WITH CODE ON PUBLIC DATA: blocks, book, fenceT (the names and forms of the condition of
the other kind, K6: Law/K6LawAtMgAll.lean). ONE EQUATION
ON PUBLIC DATA: told. TWO IN THE FIELD riders (Law/K7AtMgAll.lean: K7Riders): pile, carry.
HOW MUCH OF THE CONCLUSION THE CONDITION HOLDS: THE FIELD riders IS
THE CONCLUSION's FIFTH TIE AT TWO OF THE TEN ITEMS THAT ARE OPEN AT 338 (pile, carry 23), with the
extractor unfolded: SO THE KIND's SHARE IS SHOWN HERE FOR EIGHT OF THE TEN; with Law/K7Pile.lean's
pile_rides: for nine; carry 23 stays. The other ten fields hold nothing of the conclusion.
PAID HERE, NOT ASKED: the head's segment's number (headLink_in_scope) ·
the fence on trees (Sound/PieceFence.lean: fenced_at, from more, blocks, book, fenceT).

-/
import Johnson.P5J.RowsAtMg
import Johnson.Desc.Sound.PieceFence
import Johnson.Desc.Kinds.Law.K07AtConst

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

/-- The witness's type at the closed constant. -/
local notation "WT" =>
  Wit (Fin OnBytes.Flat.numsFull.rows → Fin (P5J.colsAt OnBytes.Flat.numsFull) → GE) Nat MsgT

/-- **THE CONDITION AT THE PIECE, ONE FIELD A DEBT.** -/
structure K7At (h : P5J.AtMgA o Z D r Zp Np cF x)
    (c₀ : Fin OnBytes.Flat.numsFull.rows → Fin (P5J.colsAt OnBytes.Flat.numsFull) → GE)
    (Rch : Nat → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (q : Piece C Fr (ProofFile.InstPub × S) Cl WT) (B Bst : Block S Cl)
    (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
    (tl : HTailF2) (numD : Fmt.TreeSource → Nat) (bs : List (Block (ProofFile.InstPub × S) Cl)) :
    Prop where
  /-- the piece holds, beneath the lift over the public part, what the seat lays -/
  seat : SeatOf Bst B
  lift : q.b = (Sound.below B).lift Prod.snd (fun t y => (t.1, y))
  /-- its acceptance is one of "the entry of the head's link, then the next token's" -/
  yes : ∀ y rs gs t, B.decide y rs gs = .ok t →
    ∃ rs' gs', (front.andThen name (Reply.blockOf W l)).decide y rs' gs' = .ok t
  front : ∀ y rs gs y1, front.decide y rs gs = .ok y1 → headFrontQ tl y = .ok y1
  /-- the head's shape is the public parameters' -/
  shape : (P5J.At.X Zp).hS = W.hS
  /-- the maker's piece: its sub-protocol, no rounds behind, the declared rounds, its base -/
  more : PieceMore numD 0 bs 338 q
  /-- three tests with code: the sub-protocols'; the table's numbers against what they tell -/
  blocks : blocksOk bs = true
  book : First.bookFit (dAt h).N PS (toldOf bs) = true
  fenceT : First.fenceFit (dAt h).N linksFull PS = true
  /-- the place tells no oracle message -/
  told : (toldOf bs)[338]? = some []
  /-- two sentences of other kinds ride past the place, from behind to in front, where the
      table's promise holds on both sides and the state in front is reached -/
  riders : K7Riders (dAt h) mgBase c₀ P5J.tokOfHeard Rch B q

/-- **THE ONE NAMED CONDITION.** -/
def K7Cond (h : P5J.AtMgA o Z D r Zp Np cF x)
    (c₀ : Fin OnBytes.Flat.numsFull.rows → Fin (P5J.colsAt OnBytes.Flat.numsFull) → GE)
    (Rch : Nat → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (row : List (Piece C Fr (ProofFile.InstPub × S) Cl WT)) : Prop :=
  ∀ q, row[338]? = some q →
    ∃ (B Bst : Block S Cl) (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
      (front : Block S Unit) (tl : HTailF2) (numD : Fmt.TreeSource → Nat)
      (bs : List (Block (ProofFile.InstPub × S) Cl)), K7At h c₀ Rch q B Bst W l name front tl numD bs

/-- The rule, at letters c₀, Rch, row. -/
theorem k07_of_cond (h : P5J.AtMgA o Z D r Zp Np cF x)
    (c₀ : Fin OnBytes.Flat.numsFull.rows → Fin (P5J.colsAt OnBytes.Flat.numsFull) → GE)
    (Rch : Nat → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (row : List (Piece C Fr (ProofFile.InstPub × S) Cl WT)) (K : K7Cond h c₀ Rch row) :
    KindTiedR (dAt h).N (P5J.mgAtAll h) linksFull PS Rch
      (fun i => extQAt (dAt h).cs (dAt h).G (dAt h).arr (dAt h).smp (dAt h).ms (dAt h).decT c₀
        P5J.tokOfHeard (dAt h).N linksFull PS (fun a => a) i)
      row .K7 :=
  k07_at_const h c₀ Rch (P5J.headLink_in_scope h.scope h.reads h.pubOne) row fun q hq => by
    obtain ⟨B, Bst, W, l, name, front, tl, numD, bs, A⟩ := K q hq
    exact ⟨B, Bst, W, l, name, front, tl, toldOf bs, A.seat, A.lift, A.yes, A.front, A.book,
      A.told, fenced_at A.more A.blocks (dAt h).N linksFull PS A.book A.fenceT
        (by decide +kernel), A.shape, A.riders⟩

/-- **THE NEXT TOKEN's LAW IN THE COUNTED FORM.** -/
theorem k07_law (h : P5J.AtMgA o Z D r Zp Np cF x)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T o Zp Np cF) P5J.At.Tok)
    (K : K7Cond h L.c₀ (Johnson.Desc.First.Walk.Tied.RchAt (P5J.F0T o Zp Np cF))
      (h.toAtMg.row L)) :
    h.toAtMg.Kind (dAt h) L .K7 :=
  k07_of_cond h L.c₀ _ _ K

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07_of_cond
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07_law
