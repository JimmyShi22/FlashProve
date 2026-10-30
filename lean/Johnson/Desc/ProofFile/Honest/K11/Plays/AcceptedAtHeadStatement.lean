-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/AcceptedAtHeadStatement.lean: THE FRAME's DEBT `AcceptedS`
(Honest/Thread/PaysS.lean) AT THE MERGE's MEMBER, NUMBER 346, AT THE FIRST CHAIN's THREAD AT THE
LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean) AND AT `SaidOk`: FROM ONE PREMISE ON
THE PROVER: that its half at the merge's place is the kind's: A STATEMENT ALONE: a definition of a
proposition. NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals: it is a lemma's
statement.

  `AcceptedSAtHead`  the head · what the maker's base returns · among the prover's halves of the
                     first chain the one at the merge's place is `headMergeHalf claims weights` at
                     the kind's numbers (claims and weights: free letters): at every letter fall:
                     `AcceptedS` at 346: wherever the pair `ThrS … SaidOk` holds at 346, the
                     challenges fit, the prover's half does not stop, the letter fall is silent
                     there (fall 346 s ds = none), and the half has moved: the verifier's step at
                     the member returns

Limits. THAT THE PAIR HOLDS AT ANY STAND IS NOT SAID: it holds the accepts of the 346 sub-protocols
in front inside it. THE PREMISE ON THE PROVER IS NOT SHOWN OF ANY PROVER. That the half does not
stop is a premise of the debt's own form. THE STEP RETURNS AT EVERY claims AND EVERY weights: the
merge's decision hears and takes slots; it tests nothing of what the half's values say: so this is
no sign that what is played is true. THE FULL SIZE ALONE; the head is a premise, at the earlier
hash: no example of it is shown here; the library's `head_exists_at_name`
(Johnson/P5J/HeadExistsAtName.lean) has one under four premises. ONE MEMBER OF ONE CHAIN: nothing on
a whole run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ReadyWholeStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedSStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def AcceptedSAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (H.first.find? fun g => g.place == IM.k11Place) =
      some (headMergeHalf claims weights (_root_.K11.parOf Zp Bs.G₀)) →
    ∀ fall, AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk fall
      346

end ProofFile.Honest.K11
