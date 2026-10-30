-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/MaskBridgeStatement.lean: THE KIND K11's PREMISE ON THE
SCRIPT's MESSAGE WITH THE MASK ROW (the field maskTie of `K11ScriptMsg`, TiesAtHeadStatement.lean of
this folder), AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD, FROM THE FRAME's AUTHORS' OWN FORM
`MaskTieOn` (Honest/Law/Rule/TiesOn.lean); AND THEIR HYPOTHESIS `ReaderAt`
(Honest/Law/Rule/ReaderAt.lean) AT THE STANDS AT WHICH THAT FORM IS ASKED: four definitions, and
STATEMENTS: three definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one of
the library's goals: they are lemmas' statements.

  `K11MaskTieF` · `K11IndexTieF`  the two fields of `K11ScriptMsg`, each as a proposition of its
                                  own, at the structure's own letters
  `K11BehindAt T Said b`          the stands behind the member's step: (k, s', m') such that from a
                                  stand of the pair `ThrS` at b the member number b has stepped to
                                  s' and m' is where the prover's run stands behind it
  `k11MaskEntry Dof seg ν₀`       the reader: entry number ν₀ + j of the segment's mask row, read by
                                  the library's `dataQ` off the open part and the witness
  `ScriptMsgIff`                  the structure is its two fields
  `MaskTieOfOn`                   the base Bs · the prover's half found at `IM.k11Place` ·
                                  `MaskTieOn` at these stands, at that place, at the half's parts,
                                  at that reader from entry 3531 on, at the first run of the lent
                                  coins, below 2 lk + 2: `K11MaskTieF` at the kind's own coins
                                  (`headMergeCoins`), AT EVERY LETTER claims: so also at the one at
                                  which `K11SeatedAtHead` (SeatedAtHeadStatement.lean of this
                                  folder) takes `K11ScriptMsg`
  `ReaderAtBehind`                the base Bs · below the number "free" no entry of row 0 of the
                                  mask message's table is a pad's: at every such stand and its open
                                  part: `ReaderAt` at the head's codes, numbering, members and the
                                  group of segment 24, at the message's number `P5J.At.num Zp 24 0`,
                                  up to "free"

Why. The frame's authors supply the Script, and prove each kind's named hypothesis on it once. For a
kind that reads the mask row through the library's reader their road ends in `MaskTieOn` and starts
from `ReaderAt` at every stand and one equation on the Script. This file is the kind's two ends of
that road.

Limits. `MaskTieOn` STAYS A PREMISE: SHOWN AT NO SCRIPT. THE PREMISE ON THE PAD STAYS: a fact on the
public codes and the message's shape: not shown here at any number; "free" IS A LETTER: for the road
to reach all the entries that the field asks it must be at least 3531 + 2 * 18 + 2 = 3569; the
frame's authors' `noPad_free` (Honest/Law/Rule/ReaderPays.lean) has that premise's end below a
number of the mask code's: that 3569 lies below it at the head's codes is not shown. THE TWO
ENDS ARE NOT JOINED HERE: the middle of the road is the frame's authors': their reader stands at
constant codes, numbering, members and group and at entry ν; `k11MaskEntry` reads these four off the
data at the input (at the head's data they are the head's own) and at entry 3531 + j. THE FIELD
indexTie IS NOT TREATED. The prover's half is a premise. 3531 is the ledger's next free slot in
front of the merge (`nextAtRaw`, Johnson/Desc/K11/Front/LiveBehind.lean). The head is a premise
here, at the earlier hash, at the full size. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.TiesAtHeadStatement
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesOn
import Johnson.Desc.ProofFile.Honest.Law.Rule.ReaderAt
import Johnson.Desc.Sound.MgAt.K11Members
import Johnson.IMR.K11Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (zeroE)
open OnBytes.Maker (WholeD)
open OnBytes.Model (Reading WsClaim)
open VerifiableInference.Desc (Chain Strs Place Claim Wit padB)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (dataQ MgData seatTab CellsQ MsgT Mem xAt)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open ProofFile.Honest.SumLaw (SumCoins firstRun endRun)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- **The first field of `K11ScriptMsg`, as a proposition of its own.** A definition: a premise's
form. -/
def K11MaskTieF {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type} {rows cols nR : ℕ}
    {Xp : OnBytes.Model.Verify.Public}
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat)
    (P : HeadMergeP)
    (coins : Coins Bk → SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (_toP : T.P → Pp) (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp) (seg : ℕ) : Prop :=
  ∀ blk k s m E ds y cols s' a a9, ThrS T Said b k s m E →
    T.Stepped blk k s m E ds y cols s' → T.bs[b]? = some blk →
    s.here = .head a → segAt? s' = some a9 → ∀ ds' i, i < 2 * P.lay.lk + 2 →
      (dataQ ((Dof m.st.input).N.group seg) a9
        (seatTab (Dof m.st.input).cs (Dof m.st.input).arr (Dof m.st.input).ms
          (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds'))))).mask (a.F.next + i) =
        Reading.gl.val ((firstRun (coins k)).getD i zeroE)

/-- **The second field of `K11ScriptMsg`, as a proposition of its own.** A definition: a premise's
form. -/
def K11IndexTieF {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type} {rows cols nR : ℕ}
    {Xp : OnBytes.Model.Verify.Public}
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat)
    (P : HeadMergeP)
    (coins : Coins Bk → SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (toP : T.P → Pp) (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp) (_seg : ℕ) : Prop :=
  ∀ blk k s m E ds y cols s', ThrS T Said b k s m E →
    T.Stepped blk k s m E ds y cols s' → T.bs[b]? = some blk →
    ∀ ds' l c' l', ledgerAt s' = some l → takeEntry l = some (c', l') →
      ((Dof m.st.input).rw13 (toP (T.seat k y.2 s').1, s')
        (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
          ⟨s'.out.indexMasks, c'⟩ = Reading.gl.val ((endRun (coins k)).headD zeroE)

/-- **The stands behind the member's step.** A definition. -/
def K11BehindAt {Bk : ProverCoinCounts} {Cl V W X Pb : Type} (T : Thread Bk S Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) :
    Coins Bk → S → Mid W X → Env → Prop :=
  fun k s' m' _ => ∃ blk s m E ds y cols, ThrS T Said b k s m E ∧
    T.Stepped blk k s m E ds y cols s' ∧ T.bs[b]? = some blk ∧ m' = y.2

/-- **The reader of the segment's mask row, from entry ν₀ on.** A definition. -/
def k11MaskEntry {V Xi' Pp Tok : Type} {rows cols nR : ℕ} {Xp : OnBytes.Model.Verify.Public}
    (Dof : V → MgData Xi' Pp Tok rows cols nR Xp) (seg ν₀ : ℕ) :
    VerifiableInference.Desc.K9.Part → S → V → Wit (CellsQ rows cols) Tok MsgT → ℕ →
      OnBytes.Slice.GE :=
  fun a9 _ w v j =>
    (dataQ ((Dof w).N.group seg) a9 (seatTab (Dof w).cs (Dof w).arr (Dof w).ms v)).mask (ν₀ + j)

/-- The statement that the structure is its two fields. Not proved here; a lemma's statement, none
of the library's goals. -/
def ScriptMsgIff : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type) (rows cols nR : ℕ)
    (Xp : OnBytes.Model.Verify.Public)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat) (P : HeadMergeP)
    (coins : Coins Bk → SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (toP : T.P → Pp) (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp) (seg : ℕ),
    K11ScriptMsg T Said b P coins toP toW Dof seg ↔
      K11MaskTieF T Said b P coins toP toW Dof seg ∧ K11IndexTieF T Said b P coins toP toW Dof seg

/-- The statement on the bridge. Not proved here; a lemma's statement, none of the library's goals.
-/
def MaskTieOfOn : Prop :=
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
      segAt? (k11MaskEntry (dataAtHead h Q carryX) 24 3531) Reading.gl.val
      (fun c => firstRun c.2.1) (fun _ j => j < 2 * (_root_.K11.parOf Zp Bs.G₀).lay.lk + 2) →
    K11MaskTieF (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) claims weights IM.k11Place c₀)
      id id (dataAtHead h Q carryX) 24

/-- The statement on the reader's six facts. Not proved here; a lemma's statement, none of the
library's goals. -/
def ReaderAtBehind : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (free : ℕ),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∀ xM : Mem, xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM →
      ∀ ν, ν < free → padB h.𝔇.cs (xM.1.l.get xM.2).1 true 0 ν = false) →
    ∀ k s' m' En,
      K11BehindAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s'
        m' En →
      ∀ a9, segAt? s' = some a9 →
        ReaderAt h.𝔇.cs h.𝔇.arr h.𝔇.ms (h.𝔇.N.group 24) a9 (P5J.At.num Zp 24 0) free

end ProofFile.Honest.K11
