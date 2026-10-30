-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K5/TieAtJoinTop.lean: conditional: what the attention sub-protocol (K5) asks of the Script
(K5ScriptQ), stated at the joined Script (joinQ, Honest/Thread/Join.lean) and at the book A.B that the
maker onlineProverFromPublicFiles returns. No definition; two theorems; each is calls of the laws of TieAtJoin.lean and
TieAtJoinOpening.lean in this folder.

  k5ScriptQ_at_joinQ       K5ScriptQ at joinQ, at each group below 12, at the numbering P5J.At.arr Zp
  k5ScriptQ_at_joinQ_fit   the same from "the list is fit" (JoinFit) and "the share stands in what the
                           other senders hand in" (K2.Law.ShareIn): larger premises

The premises of k5ScriptQ_at_joinQ, all of them. h, the library's head · hA, the maker returns A at a
filling P · hFull, at every input that meets ReadyInput the trace is a full-size trace (TraceIsFull) · hg,
the group is below 12 · hm, all lots of one message in the joined list agree · hml, the message lots of
K2's share lie among those that the other senders hand in · hx, the opening's job stands in the list of
jobs at number 2 · hwit, the reader inside wit is the reader made of the trace, wt and the input's field rc · hBk, the
book's count at the opening's address covers the part's due · hSz, the sizes S give the reference planes ·
hv, at each switch into a link below 24 K2's public test says yes at every input that meets ReadyInput.
k5ScriptQ_at_joinQ_fit takes F for hm and hBk, and hin for hml: of F's fields msgs and coins are spent, of
hin's ml alone.

Limits.
  * Conditional. This file proves none of its premises of any list, reader, book, instance or filling.
  * K5ScriptQ speaks of the inputs that meet ReadyInput alone: where no input does, it says nothing.
  * The index type W₀ and its reader wt are letters, and so are the cells cq. Their values come from the
    caller's filling.
  * NOT IN FRONT OF A LAW OVER COINS. The full size alone, the first chain alone, at the
    earlier hash OnBytes.secondHashFunction, a fixed function.
  * Through its imports it stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
  * hm can be met where not every sender's share is laid yet; F cannot.
  * All limits of TieAtJoin.lean and TieAtJoinOpening.lean hold here.
-/
import AtFullSide.K5.TieAtJoinOpening

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K5
open ProofFile ProofFile.Honest ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head MsgLot PadLot TreeLot LotsAgree MsgsAgree Covers
  Others JoinFit joinQ joinMl joinPl joinTl)
open P5J (AtMgA TS CellsM)

variable {W₀ : Type} {wt : W₀ → Weights} {cellsOf : W₀ → P5J.CellsM OnBytes.Flat.numsFull}

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {S : OnBytes.HonestTrace.Sz} {X₀ X : Type}

section
variable {P : OnlineProverParts W₀ IndexCommitterCoins Cells X₀ X} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells X₀ X}

/-- **K5's premise on the `Script` holds at the joined `Script` and the maker's book, at each group
below 12.** Conditional: every premise stands, by name, in the file's head. It speaks of the inputs
that meet `ReadyInput` alone. NOT IN FRONT OF A LAW OVER COINS. -/
theorem k5ScriptQ_at_joinQ
    (cq : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → P5J.At.Tok)
    (hSz : planesAtRef S = Sz.ref) {g : ℕ} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hFull : TraceIsFull (P5J.At.X Zp) (ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H) (id : Cells → Cells))
    {Xo : Type}
    {wit : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → K1.PlaceIn ProofFile.Inst} {own₀ : Xo}
    {jobs : List (ℕ × K1.SendJob (K1.PlaceIn ProofFile.Inst) Xo)}
    {O : Others A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)}
    (hm : MsgsAgree (joinMl cF.blocksInOrder 0 (P5J.At.arr Zp) wit own₀ jobs O))
    {rest : ℕ → TreeLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)}
    (hml : ∀ L ∈ (K2.switchShareAt A.B cF.blocksInOrder 0 Zp A.G (K2.withSwitchData S (K1.lotData S) Zp A.G)
      (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) rest).ml, L ∈ O.ml)
    (hv : ∀ p ∈ K2.switchPlaces Zp A.G, p.link < 24 → ∀ w,
      ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H w →
      K2.publicOk (K2.withSwitchData S (K1.lotData S) Zp A.G) A.G.first.layout p
        ((K2.segmentsOf Zp A.G).take p.link) w.x = true)
    {first : ℕ}
    (hx : (2, (K1.placeJob (X := Xo) (K1.firstJob (X := Xo) S Zp A.G).P first (K1.firstFold A.G.first)
      (K1.lotData S Zp A.G))) ∈ jobs)
    (hwit : ∀ v, (wit v).R = ⟨v.trace, wt v.w₀, v.rc⟩)
    (hBk : K1.bookCovers A.B 0 ⟨(K1.firstJob (X := Xo) S Zp A.G).P.place, 0⟩
      (K1.dueR (K1.firstJob (X := Xo) S Zp A.G).P (K1.firstJob (X := Xo) S Zp A.G).ride) = true) :
    ∀ a x₁, (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h (joinQ cF.blocksInOrder 0 cq tok (P5J.At.arr Zp) wit own₀ jobs O)
        (ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H)
        (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (ProofFile.Honest.K5.seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs) :=
  k5ScriptQ_of_lists h cq tok (joinPl cF.blocksInOrder jobs O) (joinTl wit own₀ jobs O)
    (joinMl cF.blocksInOrder 0 (P5J.At.arr Zp) wit own₀ jobs O) A.G.first.layout hSz hg hA hFull
    (planSwitchLists_at_join h hA hm hml hv)
    (fun g0 Ad m hAd => by
      subst g0
      exact openingLot_at_join_head h hA hm hx hwit hBk hAd)

/-- The same from "the list is fit" and "the share stands in what the other senders hand in". Larger
premises: of F the fields msgs and coins are spent, of hin the field ml alone.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem k5ScriptQ_at_joinQ_fit
    (cq : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → P5J.At.Tok)
    (hSz : planesAtRef S = Sz.ref) {g : ℕ} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hFull : TraceIsFull (P5J.At.X Zp) (ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H) (id : Cells → Cells))
    {Xo : Type}
    {wit : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → K1.PlaceIn ProofFile.Inst} {own₀ : Xo}
    {jobs : List (ℕ × K1.SendJob (K1.PlaceIn ProofFile.Inst) Xo)}
    {O : Others A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)}
    {seats : List (ℕ × ℕ)} (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) seats wit own₀ jobs O)
    {rest : ℕ → TreeLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)}
    (hin : K2.Law.ShareIn (K2.switchShareAt A.B cF.blocksInOrder 0 Zp A.G (K2.withSwitchData S (K1.lotData S) Zp A.G)
      (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) rest) O)
    (hv : ∀ p ∈ K2.switchPlaces Zp A.G, p.link < 24 → ∀ w,
      ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H w →
      K2.publicOk (K2.withSwitchData S (K1.lotData S) Zp A.G) A.G.first.layout p
        ((K2.segmentsOf Zp A.G).take p.link) w.x = true)
    {first : ℕ}
    (hx : (2, (K1.placeJob (X := Xo) (K1.firstJob (X := Xo) S Zp A.G).P first (K1.firstFold A.G.first)
      (K1.lotData S Zp A.G))) ∈ jobs)
    (hwit : ∀ v, (wit v).R = ⟨v.trace, wt v.w₀, v.rc⟩) :
    ∀ a x₁, (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h (joinQ cF.blocksInOrder 0 cq tok (P5J.At.arr Zp) wit own₀ jobs O)
        (ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H)
        (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (ProofFile.Honest.K5.seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs) :=
  k5ScriptQ_at_joinQ h cq tok hSz hg hA hFull F.msgs hin.ml hv hx hwit (coins_at_opening F hx)

end

section
variable (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat)
  {P : OnlineProverParts W₀ IndexCommitterCoins Cells X₀ X} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells X₀ X}
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

end

end AtFullSide.K5

#print axioms AtFullSide.K5.k5ScriptQ_at_joinQ
#print axioms AtFullSide.K5.k5ScriptQ_at_joinQ_fit
