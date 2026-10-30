-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7CondOfLaid.lean.
WHAT IT DOES NOT SHOW. No soundness. NOT A MEMBER OF K7Cond FOR NOTHING: SIX PREMISES STAY: q₁, q₂,
q₃ (L's three lists are the IOP's own) · TWO TESTS WITH CODE ON PUBLIC DATA, book and fenceT
(evaluated true at the release's full-size public files; no theorem) · K7Carry:
"carry 23" RIDES PAST THE PLACE: THE CONCLUSION's FIFTH TIE AT THAT ONE ITEM: other files make that
join; a closed fact is owed for it besides ((ProofFile.pAtK2 Zp 23).stands = .head). AT THE FORMAT's
SECOND HASH FUNCTION ITSELF (o := OnBytes.secondHashFunction) ALONE. The full size alone. A member of the head h
is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/).
WORDS. "The closed constant", "the counted form": as in Law/K07AtMg.lean. "Held": a sub-protocol as
a piece holds it.
LETTERS. No "there is" in the statement. Rch: free: so the payment serves the condition at bare
"reached" and at the join's own narrower one alike. The letters under K7Cond's "there is" are chosen
here: B := Bst := the sub-protocol at 338 of the first chain · W := the opening's public parameters
· l := 24 · name := "H:1" · front := P4.k7Front W · tl := W.H.tl · numD := the maker's numbering ·
bs := the chain's own list, held.
OBJECT. Law/K07AtMg.lean's K7Cond, at the table's files' head AtMgA and its own row.
USER. The kinds' join: Law/K07AtMg.lean: k07_of_cond, k07_law; the skeleton's bridge for this kind.
WHAT IT IS. OF K7Cond's TWELVE DEBTS NINE ARE PAID FROM THE HEAD ALONE; TWO BECOME TESTS AT THE
CHAIN's OWN LIST; ONE STAYS.
K7Carry: the debt that stays, by name. k7Cond_of_laid: the payment.
WHO PAYS WHAT: seat, yes, front: P4.k7_left_seat, at the opening that the head's own field
laid.opened hands out · shape: that opening's field W · lift, more, blocks: Law/RowAtConst.lean ·
the length that more wants: Law/RowLenAtConst.lean · told: P4.told_338 with
toldOf_held · pile: Law/K7Pile.lean.

-/
import Johnson.P4R.ReplyTiedN
import Johnson.P4R.Told338N
import Johnson.Desc.Kinds.Law.K07AtMg
import Johnson.Desc.Kinds.Law.K7Pile
import Johnson.Desc.Kinds.Law.RowAtConst
import Johnson.Desc.Kinds.Law.RowLenAtConst

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

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Cl : Type} {C : CK} {Fr : Frame}

/-- The driver's list of places, at the full chain. -/
local notation "PS" => flatPlacesOf linksFull true

/-- The witness's type at the closed constant. -/
local notation "WT" =>
  Wit (Fin OnBytes.Flat.numsFull.rows → Fin (P5J.colsAt OnBytes.Flat.numsFull) → GE) Nat MsgT

/-- **THE DEBT THAT STAYS**: "carry 23" rides past the place, from behind to in front, where the
table's promise holds on both sides and the state in front is reached (Law/K7AtMgAll.lean:
K7Riders' second field, to the letter, at the closed constant). -/
def K7Carry {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMgA o Z D r Zp Np cF x)
    (c₀ : Fin OnBytes.Flat.numsFull.rows → Fin (P5J.colsAt OnBytes.Flat.numsFull) → GE)
    (Rch : Nat → (ProofFile.InstPub × S) × Fr.E.Str → Prop) (B : Block S Cl)
    (q : Piece C Fr (ProofFile.InstPub × S) Cl WT) : Prop :=
  ∀ (z : ProofFile.InstPub) a τ b (w : WT),
    (pieceK7 (dAt h).cs (dAt h).arr (dAt h).N P5J.tokOfHeard linksFull PS 338 (dAt h).G (dAt h).smp
      (dAt h).ms (dAt h).decT c₀ B q z).ior.red.out a τ = some b → Rch 338 ((z, a.1), a.2) →
    onQ (dAt h).N (mgAll (dAt h) mgBase) linksFull PS (fun y => (z, y)) 338 a →
    onQ (dAt h).N (mgAll (dAt h) mgBase) linksFull PS (fun y => (z, y)) (338 + 1) b →
    (mgAll (dAt h) mgBase).carry 23 (z, b.1) (strsOf Fr b.2) w →
    (mgAll (dAt h) mgBase).carry 23 (z, a.1) (strsOf Fr a.2)
      ⟨w.cells, P5J.tokOfHeard (z, b.1), w.msg, w.pad⟩

/-- **THE PAYMENT.** -/
theorem k7Cond_of_laid (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (Rch)
    (book : First.bookFit (dAt h).N PS (toldOf cF.blocksInOrder) = true)
    (fenceT : First.fenceFit (dAt h).N linksFull PS = true)
    (carry : ∀ B q, cF.blocksInOrder[338]? = some B → (h.toAtMg.row L)[338]? = some q →
      K7Carry h L.c₀ Rch B q) :
    K7Cond h L.c₀ Rch (h.toAtMg.row L) := by
  intro q hq
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, e1, e2, -, hseat, hyes, hfront⟩ := P4.k7_left_seat h.scope h.reads O
  have f1 : cF.blocksInOrder[338]? = some b := by
    have q' := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope h.scope h.reads O (by decide) 0] at q'
  have hm := atRow_more h.toAtMg L q₁ q₂ q₃ 338 q hq (atRow_in h.toAtMg 338 (by omega))
  exact ⟨b, b, Bs.G₀.W, 24, "H:1", P4.k7Front Bs.G₀.W, Bs.G₀.W.H.tl, _, cF.blocksInOrder.map held,
    { seat := hseat
      lift := atRow_lift h.toAtMg L q₁ q₂ q₃ 338 q b hq f1
      yes := hyes
      front := hfront
      shape := by rw [O.W]; rfl
      more := hm.1
      blocks := atRow_blocks h.toAtMg
      book := by rw [toldOf_held]; exact book
      fenceT := fenceT
      told := by rw [toldOf_held]; exact P4.told_338 h.scope h.reads O
      riders := riders_of_carry (dAt h) mgBase L.c₀ P5J.tokOfHeard Rch b q Bs.G₀.W 24 "H:1"
        (P4.k7Front Bs.G₀.W) Bs.G₀.W.H.tl hyes hfront (carry b q f1 hq) }⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k7Cond_of_laid
