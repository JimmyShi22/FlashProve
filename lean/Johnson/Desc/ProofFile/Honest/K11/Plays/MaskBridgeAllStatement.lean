-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/MaskBridgeAllStatement.lean: THE BRIDGE `MaskTieOfOn`
(MaskBridgeStatement.lean of this folder) WITH ITS PREMISE AT THE VERY LETTERS AT WHICH THE FRAME's
AUTHORS' OWN ROAD ENDS (`maskTieOn_all`, Honest/Law/Rule/TiesAll.lean: the entry "maskOf a s w v
(slot a + j)", the coins `spentOf ps`, the bound "j < cnt"): STATEMENTS ALONE: two definitions of
propositions. NOTHING IS PROVED IN THIS FILE, and neither is one of the library's goals: they are
lemmas' statements.

  `SpentOfHalf`    at the parts of the kind's half, at every lent coins c, below 2 lk + 2: entry
                   number j of `spentOf` (Honest/Law/Rule/Spent.lean: what the row's parts spend,
                   part by part) is entry number j of the first run of the sumcheck's coins
                   (`firstRun c.2.1`)
  `MaskTieOfAll`   the base Bs · the prover's half found at `IM.k11Place` · `MaskTieOn` at the
                   stands behind the member's step, at that place, at the half's parts, at the entry
                   "the library's reader at the head's own codes, numbering, members and group of
                   segment 24, at 3531 + j", at `spentOf` of these parts, below 2 lk + 2:
                   `K11MaskTieF`, as `MaskTieOfOn` ends

How the letters of `maskTieOn_all` are to be laid for its end to be this premise: maskOf: the reader
of `readerReads_one` (Honest/Law/Rule/ReaderAt.lean) at cs, arr, ms the head's and own the group of
segment 24 · slot: THE CONSTANT 3531 · cnt: 2 lk + 2. THE SLOT MUST BE THE CONSTANT: at the stands
behind the step the open part's own ledger has moved on by 2 lk + 3 (the library's `merge_ledger`,
Johnson/Top/H0/MergeLaw/LedgerBehind.lean; `seg_at_merge`): 3531 is its next free slot IN FRONT of
the step.

Limits. `MaskTieOn` STAYS A PREMISE: SHOWN AT NO SCRIPT: `maskTieOn_all` HAS TEN PREMISES, AND IT IS
CALLED HERE AT NO LETTERS: THAT ITS END AT THE LETTERS ABOVE IS THIS PREMISE IS BY READING: NO LEAN
HAS SEEN THE TWO TOGETHER. All the limits of MaskBridgeStatement.lean. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskBridgeStatement
import Johnson.Desc.ProofFile.Honest.Law.Rule.Spent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (zeroE)
open OnBytes.Maker (WholeD)
open OnBytes.Model (Reading WsClaim)
open VerifiableInference.Desc (Chain Strs Place Wit)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (dataQ seatTab MsgT)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open ProofFile.Honest.SumLaw (SumCoins firstRun)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement on the coins. Not proved here; a lemma's statement, none of the library's goals.
-/
def SpentOfHalf : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights)
    (c : RowCoins (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).parts) (j : ℕ),
    j < 2 * P.lay.lk + 2 →
    (spentOf (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).parts c).getD j
        zeroE = (firstRun c.2.1).getD j zeroE

/-- The statement on the bridge. Not proved here; a lemma's statement, none of the library's goals.
-/
def MaskTieOfAll : Prop :=
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
    MaskTieOn (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (K11BehindAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346)
      IM.k11Place
      (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights
        (_root_.K11.parOf Zp Bs.G₀)).parts
      segAt?
      (fun a _ _ (v : Wit (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) j =>
        (dataQ (h.𝔇.N.group 24) a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)).mask (3531 + j))
      Reading.gl.val
      (spentOf (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights
        (_root_.K11.parOf Zp Bs.G₀)).parts)
      (fun _ j => j < 2 * (_root_.K11.parOf Zp Bs.G₀).lay.lk + 2) →
    K11MaskTieF (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) claims weights IM.k11Place c₀)
      id id (dataAtHead h Q carryX) 24

end ProofFile.Honest.K11
