-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/BehindOfRdStatement.lean: `BehindSAtHead`
(BehindAtHeadStatement.lean of this folder) WITH THE RIDER ON THE REPLY PAID: the frame's debt
`BehindS` at number 346, at the first chain's thread at the library's head and at `SaidOk`, where
the border b₀ from which the reply rides is at most 346: FROM THE PREMISE ON Kp AND A PREMISE ON Rd
ALONE: A STATEMENT ALONE: a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and it is
none of the library's goals: it is a lemma's statement.

  `BehindSAtHeadOfRd`  the head · what the maker's base returns · b₀ ≤ 346 · the kind's clause
                       `K11Keeps` gives the thread's keeps at 346 · behind the member's step, with
                       that clause in hand, the letter Rd holds at 347: `BehindS` at 346

Why. At this thread the riders at a border b are two: from b₀ on the verifier's state holds the
asked reply; and the letter Rd (Honest/Thread/FirstHead.lean). The merge writes neither the reply
nor the prover's input: so the first rides from 346 to 347. (The frame's own number for the letter
b₀ is 339: `b0Head_closed`, Honest/Thread/ReplyAt.lean.)

Limits. THE TWO PREMISES ON Kp AND Rd ARE SHOWN AT NO FILLING OF THESE LETTERS. All the limits of
BehindAtHeadStatement.lean. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.BehindAtHeadStatement

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
def BehindSAtHeadOfRd : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs → b₀ ≤ 346 →
    (∀ s s', K11Keeps (_root_.K11.parOf Zp Bs.G₀) s s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s') →
    (∀ blk k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
        E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      cF.blocksInOrder[346]? = some blk → K11Keeps (_root_.K11.parOf Zp Bs.G₀) s s' →
      Rd 347 y.2.st.input s') →
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346

end ProofFile.Honest.K11
