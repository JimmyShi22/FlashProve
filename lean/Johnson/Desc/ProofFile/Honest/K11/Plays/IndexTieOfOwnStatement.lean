-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexTieOfOwnStatement.lean: THE SECOND FIELD OF
`K11ScriptMsg`, `K11IndexTieF` (MaskBridgeStatement.lean of this folder), FROM `OwnMsgs`
(Honest/Thread/ScriptLots.lean) AT THE KIND's SECOND LOT `k11IndexLot` (MsgLotsStatement.lean of
this folder). A STATEMENT ALONE: one definition of a proposition; no definition of another kind.
NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals: a lemma's statement. An
implication at letters.

  `IndexTieOfOwn`   the head · what the maker's base returns · the kind's half found at the merge's
                    place · `OwnMsgs` at the lot ⊢ `K11IndexTieF` at the head's thread, at border
                    346

The binders and the first two premises are those of `MaskTieOfOwn` (MsgLotsStatement.lean), sign for
sign. The lot's three letters are laid at another group of authors' own terms
(Honest/K4/Lot/IndexNum.lean), as their `indexEntry_border` (Honest/K4/Law/W/IndexFactsThr.lean)
ends: the message's number in the witness `k4IndexNum` Zp; the row and the place: the number of
segments in front of segment 24 that leave a row, modulo and over the message's number of mask rows
`k4IndexRows` Zp.

WHAT IT IS NOT. `OwnMsgs` is met here at no Script; no lot is laid. Nothing says that this lot
agrees with the sender's. That no entry is spent twice is the book's own test, not this file's. That
`k4IndexRows` Zp is not 0 is not said here: at 0 the lot would lie at another row and at place 0,
and the implication would stand all the same. The field's own form holds of nothing where the ledger
of the index masks' message is not there behind the step, or hands out nothing. With `MaskTieOfOwn`
it gives both fields of `K11ScriptMsg` from `OwnMsgs` at the two lots.

NEAR. `indexEntry_thr` and the join over it (Honest/K4/Law/W/IndexOfOwn.lean, the same authors'):
the like at the feed-forward layers' twelve members.

Limits. The full size and the format's second hash function, as the head has them. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MsgLotsStatement
import Johnson.Desc.ProofFile.Honest.K4.Lot.IndexNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First.FillP1 (fvsAt)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open ProofFile.Honest.SumLaw (SumCoins)
open ProofFile.Honest.K4.Lot (k4IndexRows k4IndexNum)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- **The statement on the second join.** Not proved here; a lemma's statement, none of the
library's goals. THREE THINGS TO MIND. (1) ITS ONE PAYER. By the frame's authors' design no lot is
laid at a spender's place: so the premise, `OwnMsgs` at the text of `k11IndexLot`, is to be had as a
lemma on the SENDER's lot alone: from `OwnMsgs` at the whole-message text of the index masks'
sender, that text's equation at the entry, and a law on the book's SECOND spending entry for
⟨`IM.k11Place`, 1⟩: the like, at the end run, of `MaskRunIsOwners` and `MaskLotMeets`
(MaskLotOwnerStatement.lean of this folder). (2) c₀ IS A FREE LETTER: what `headMergeCoins`
(SeatFieldsStatement.lean of this folder) falls back on where the lending refuses. There the lot is
silent (`lotsSilent`, LotsRuns.lean), so the premise asks nothing; AND THERE THE END HOLDS OF
NOTHING TOO: it speaks behind a step of the member, and where a step has been played the row has
been lent (`StepsOfHalf`, AcceptedStatement.lean): so c₀ is never read where the end says something:
an idle way. (3) ONCE. Other kinds spend of the index masks' message too: that the one entry which
the merge spends is no other part's is the book's own test, not this file's. -/
def IndexTieOfOwn : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay)),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find? fun g =>
      g.place == IM.k11Place) =
        some (headMergeHalf claims weights (_root_.K11.parOf Zp Bs.G₀)) →
    OwnMsgs Q Vd 0 (k4IndexNum Zp) 0
      (k11IndexLot Bk (Rc := Rc) (Tr := Tr) X
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain IM.k11Place
        (_root_.K11.parOf Zp Bs.G₀) claims weights (k4IndexNum Zp)
        (rowsBefore (fvsAt Zp) 24 % k4IndexRows Zp)
        (rowsBefore (fvsAt Zp) 24 / k4IndexRows Zp)).txt →
    K11IndexTieF (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) claims weights IM.k11Place c₀)
      id id (dataAtHead h Q carryX) 24

end ProofFile.Honest.K11
