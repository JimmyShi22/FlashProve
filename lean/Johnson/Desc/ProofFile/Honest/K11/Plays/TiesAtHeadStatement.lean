-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/TiesAtHeadStatement.lean: THE FIELD ties OF `K11SeatedS`
(ShareSStatement.lean of this folder) AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD, FROM FOUR
FACTS ON THE SCRIPT: THE KIND's NAMED PREMISE ON THE SCRIPT IN A SECOND FORM: two structures, and
STATEMENTS: two definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one of the
library's goals: they are lemmas' statements.

  `K11ScriptMsg`  what the kind asks of the Script's MESSAGES: the fields maskTie and indexTie of
                  `K11Script` (ScriptStatement.lean of this folder), in their own words; general in
                  the thread
  `K11CellsQ`     what the kind asks of the Script's CELLS: no thread, no state, no challenge:
                  AT THE INPUTS OF WHICH THE LETTER Vd HOLDS: inRange: they hold an index
                  (`InRange`, Johnson/Flat/LedgerClaim.lean) · entries: inside the layout they are
                  the prover's weights' entries
  `ScriptAtHead`  at the head's thread: the two give `K11Script`: ITS THIRD FIELD matTie FOLLOWS
                  FROM entries
  `TiesAtHead`    at the head's thread: the two give the field ties, in that field's own words, at
                  toP := id, toW := id, Dof := `dataAtHead`, seg := 24

Limits. THE TWO STRUCTURES ARE DEFINITIONS: PREMISES' FORMS: NOTHING IS CLAIMED OF THEM, AND NOTHING
SHOWS THAT THEY CAN BE MET: no Script is laid anywhere: whoever lays it pays them. BOTH FIELDS OF
`K11CellsQ` ARE ASKED UNDER Vd ALONE: they are spent at the run's input, of which the thread's last
clause says Vd; at a Vd that holds of no input they ask nothing. THE FIELD entries is payable where
the Script's cells at a valid input are made of that input's weights; a Script that reads its cells
off anything else cannot pay it. THE LETTER weights STANDS IN THE KIND's LOT OF HALVES TOO: all must
be laid alike. THE LETTER coins IS FREE: at an arbitrary one nobody can pay `K11ScriptMsg`: it is
meant at what the book lends the kind's row (`headMergeCoins`, SeatFieldsStatement.lean of this
folder). That the item .forms 24 4 "weights" is open at 346, which `ClaimTrueAtHead` takes as a
premise, is paid by an evaluation in Lean's kernel on the written lists (OpenAt346.lean of this
folder). `TiesAtHead` rests on `ClaimTrueAtHead` (ClaimTrueStatement.lean of this folder) and has
all its limits: among them: the claim's truth is taken out of the thread's own sentence; it is no
better than another team's file. ONE FIELD OF THIRTEEN. THAT THE PAIR HOLDS AT ANY STAND IS NOT
SAID. The head is a premise here, at the earlier hash, at the full size. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ClaimTrueStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (zeroE)
open OnBytes.Maker (WholeD)
open OnBytes.Model (Reading WsLay)
open VerifiableInference.Desc (Chain Strs Place Claim Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K13.Law (cellAtNo)
open VerifiableInference.Desc.Sound (dataQ MgData seatTab CellsQ MsgT)
open VerifiableInference.OnPublicFiles.Flat (InRange)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open ProofFile.Honest.SumLaw (SumCoins firstRun endRun)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- **What the kind asks of the Script's messages at the merge's member.** It is a definition: a
premise's form. Nothing is claimed of it, and nothing shows that it can be met. -/
structure K11ScriptMsg {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type} {rows cols nR : ℕ}
    {Xp : OnBytes.Model.Verify.Public}
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat)
    (P : HeadMergeP)
    (coins : Coins Bk → SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (toP : T.P → Pp) (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp) (seg : ℕ) : Prop where
  /-- under the slots that the sumcheck takes the segment's mask row holds the first run's coins. a:
  the head's own part in front; a9: the open segment's part behind -/
  maskTie : ∀ blk k s m E ds y cols s' a a9, ThrS T Said b k s m E →
    T.Stepped blk k s m E ds y cols s' → T.bs[b]? = some blk →
    s.here = .head a → segAt? s' = some a9 → ∀ ds' i, i < 2 * P.lay.lk + 2 →
      (dataQ ((Dof m.st.input).N.group seg) a9
        (seatTab (Dof m.st.input).cs (Dof m.st.input).arr (Dof m.st.input).ms
          (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds'))))).mask (a.F.next + i) =
        Reading.gl.val ((firstRun (coins k)).getD i zeroE)
  /-- at the entry that the ledger behind takes the index-mask message holds the one coin of the run
  "ends" -/
  indexTie : ∀ blk k s m E ds y cols s', ThrS T Said b k s m E →
    T.Stepped blk k s m E ds y cols s' → T.bs[b]? = some blk →
    ∀ ds' l c' l', ledgerAt s' = some l → takeEntry l = some (c', l') →
      ((Dof m.st.input).rw13 (toP (T.seat k y.2 s').1, s')
        (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
          ⟨s'.out.indexMasks, c'⟩ = Reading.gl.val ((endRun (coins k)).headD zeroE)

/-- **What the kind asks of the Script's cells.** It is a definition: a premise's form. Nothing is
claimed of it, and nothing shows that it can be met. -/
structure K11CellsQ {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (lay : WsLay) (weights : W₀ → Weights) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) : Prop where
  /-- at a valid input the cells hold an index -/
  inRange : ∀ v, Vd v → InRange (Q.cells v)
  /-- at a valid input, inside the layout, the cells are the prover's weights' entries -/
  entries : ∀ v, Vd v → ∀ r c, r < lay.m0 → c < 2 ^ lay.lk →
    cellAtNo (Q.cells v) r c = Reading.gl.val (eOfF ((weights v.w₀).entry r c))

/-- The statement on the first form. Not proved here; a lemma's statement, none of the library's
goals. -/
def ScriptAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (weights : W₀ → Weights)
    (coins : Coins Bk → SumCoins
      (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay)),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    K11ScriptMsg (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀) coins id id (dataAtHead h Q carryX) 24 →
    K11CellsQ Q (_root_.K11.parOf Zp Bs.G₀).lay weights Vd →
    K11Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀) weights coins id id (dataAtHead h Q carryX) 24

/-- The statement on the field. Its end is the field ties of `K11SeatedS`, in that field's own
words. Not proved here; a lemma's statement, none of the library's goals. -/
def TiesAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (weights : W₀ → Weights)
    (coins : Coins Bk → SumCoins
      (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay)),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    K11ScriptMsg (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀) coins id id (dataAtHead h Q carryX) 24 →
    K11CellsQ Q (_root_.K11.parOf Zp Bs.G₀).lay weights Vd →
    ∀ blk k s m E ds y cols s' a claim x0 b9 a9,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
        E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[346]? = some blk →
      s.here = .head a →
      a.claim = some claim → a.x = some x0 → segAt? s = some b9 → segAt? s' = some a9 →
      ∀ ds', MergeTiesAt (_root_.K11.parOf Zp Bs.G₀) (dataAtHead h Q carryX m.st.input) 24
        (id ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k y.2 s').1) s' a
        claim x0 b9 a9 (weights m.st.input.w₀) (coins k)
        (id ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k y.2.st.input
          (y.2.st.heard ++ ds')))

end ProofFile.Honest.K11
