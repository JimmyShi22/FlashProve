-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/BehindAtHeadStatement.lean: THE FRAME's DEBT `BehindS`
(Honest/Thread/PaysS.lean) AT THE MERGE's MEMBER, NUMBER 346, AT THE FIRST CHAIN's THREAD AT THE
LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean) AND AT `SaidOk`: FROM TWO PREMISES ON
THE THREAD's FREE LETTERS: A STATEMENT ALONE: a definition of a proposition. NOTHING IS PROVED IN
THIS FILE, and it is none of the library's goals: it is a lemma's statement.

  `BehindSAtHead`  the head · what the maker's base returns · the kind's clause `K11Keeps`
                   (Johnson/Desc/K11/Returns/KeepsStatement.lean) gives the thread's keeps at 346 (a
                   premise on the letter Kp) · behind the member's step, with that clause in hand,
                   the thread's riders hold at 347 (a premise on the letters b₀ and Rd): `BehindS`
                   at 346: wherever the pair `ThrS … SaidOk` holds at 346, the challenges fit and
                   the member's step has returned: behind it the form at 347, the riders at 347, and
                   keeps at 346

Why. The kind's law `HeadMergeBehindS` (BehindSStatement.lean of this folder), general in the
thread, has five premises: the member · keeps · the two halves of "the form behind" · the riders. At
this thread the member is had under the head, and BOTH HALVES OF "THE FORM BEHIND" ARE THE FRAME's
OWN LEMMA `k11_form_behind` (Honest/Thread/K11FormBehind.lean). Here the two are set together.

Limits. THE TWO PREMISES ARE SHOWN AT NO FILLING OF THE LETTERS Kp, b₀, Rd. THE PROOF STANDS OVER
ANOTHER AUTHOR's UNSEALED FILES, three of which are in no issue of the frame's threads
(Honest/Thread/: K11FormBehind · FormXKFront · FormXK). THAT THE PAIR HOLDS AT ANY STAND IS NOT
SAID; that the member's step returns is a premise of the debt's own form. THE FULL SIZE ALONE; the
head is a premise, at the earlier hash: no example of it is shown here; the library's
`head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean) has one under four premises. ONE MEMBER OF
ONE CHAIN: nothing on a whole run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.BehindSStatement
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.ForkMerge.Returns (K11Keeps)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def BehindSAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∀ s s', K11Keeps (_root_.K11.parOf Zp Bs.G₀) s s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s') →
    (∀ blk k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
        E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      cF.blocksInOrder[346]? = some blk → K11Keeps (_root_.K11.parOf Zp Bs.G₀) s s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.rides 347 y.2.st.input
        s') →
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346

end ProofFile.Honest.K11
