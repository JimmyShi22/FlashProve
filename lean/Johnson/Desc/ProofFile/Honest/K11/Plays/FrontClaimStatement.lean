-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/FrontClaimStatement.lean: THE LAST CLAUSE OF THE FIELD front
OF `K11SeatedS` (ShareSStatement.lean of this folder): "the row's letter claims, at the input's
instance and the challenges heard, is the one claim that the state holds": AT THE FIRST CHAIN's
THREAD AT THE LIBRARY's HEAD, AT NUMBER 346, AT A WRITTEN TEXT FOR THAT LETTER: one definition, and
A STATEMENT: a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and it is none of the
library's goals: it is a lemma's statement.

  `headClaimsAt cF Zp G`  the text for the row's letter claims: the kind's own text of the asked
                          claims (`headMergeClaims`, Honest/K11/Claims.lean) at the four things that
                          the output head's rounds heard (`headFourOfK6`, ThreeTiesStatement.lean),
                          the key points by the lookups' authors' `headKeysOfK3 cF`
                          (Honest/K3/Law/Thread/HeadCallsTie.lean)
  `FrontClaimAtHead`      the head · the base Bs · b₀ ≤ 346 · the pair `ThrS` at 346 at `SaidOk` ·
                          the state stands in the head's link and holds a claim: `headClaimsAt cF Zp
                          Bs.G₀` at the input's instance and the challenges heard is the list of
                          that one claim

Limits. THAT THE PAIR HOLDS AT ANY STAND IS NOT SAID. Of the pair the second half is not spent: the
lemma holds at every letter Said; it is stated at `SaidOk`, where the field is wanted. THE LETTER
claims STANDS IN FOUR PLACES, AND ALL MUST BE LAID ALIKE: this clause; the field steps; the premise
on the prover's half; and the kind's lot of halves (`headMergeLot`, Honest/K11/Part.lean), whose
letter must then be `headClaimsAt cF`: THAT A FILLING's LOT IS LAID AT THIS TEXT IS SAID BY NOBODY.
b₀ ≤ 346 is a premise on a letter: from that border on the thread's rider says that the state's
reply is the one that the instance asks about. It rests on `HeadClaimIsOfK3`
(Honest/K11/ClaimIsOfK3Statement.lean) and has all its limits: among them: it is no better than the
lookups' authors' file, which they call a reading copy. The seven other clauses of the field:
FrontSAtHeadStatement.lean of this folder. The head is a premise, at the earlier hash, at the full
size: no example of it is shown here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimIsOfK3Statement
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (HeadOwn)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Honest (roundsAhead)
open ProofFile.Honest.K3.Law.AtThr (headKeysOfK3)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- **The text for the row's letter claims.** -/
def headClaimsAt (cF : Chain TS ProofFile.Cl) (Zp : ProofFile.Pub) (G : ProofFile.Ground) :
    ProofFile.Inst → List Fmt.Drawn → List WsClaim :=
  headMergeClaims (headFourOfK6 (headKeysOfK3 cF) (roundsAhead cF.blocksInOrder 341)) Zp G

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def FrontClaimAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (k : Coins Bk) (s : TS)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (Bs : ProofFile.PureBase) (a : HeadOwn)
    (claim : WsClaim),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs → b₀ ≤ 346 →
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
      E →
    s.here = .head a → a.claim = some claim →
    headClaimsAt cF Zp Bs.G₀ m.st.input.x m.st.heard = [claim]

end ProofFile.Honest.K11
