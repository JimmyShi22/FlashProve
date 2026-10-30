-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupOpenItemsRidePastTheCalls.lean: the kind "lookup" (K3):
the debt `RidesPastS` at each of the 25 lookups on the calls, at the first chain's letters at the
library's head. Two theorems.

What is shown.
  `lookupOpenItemsRidePastTheCallsOfALink`: `RidesPastS` at the calls of link l < 25.
  `lookupOpenItemsRidePastTheCalls`: **`RidesPastS` at the border of every site on the calls.**

Hypotheses that remain. `atHead`: `P5J.AtMgA`. `siteIsListed`, `onTheCalls`: the site is on the
calls. `keepsGivesTheLookupClause`: the letter f at the kind K3 implies `k3KeepsAt`. Every other
letter of the thread is free, and so is `Said`.

How the proof goes. `lookupOpenItemsRidePast` asks that every open item go back; at the calls they
are all plain (`openItemIsPlainAtTheCalls`), and the plain ones do (`plainItemGoesBack`).

Limits. At the calls alone. `RidesPastS` is a step law from the invariant: nothing here shows that
the invariant holds at any run. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupPlainItemsRidePast
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LinkLtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place Strs KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open ProofFile.Honest.K3.Law.AtThr (k3KeepsAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LK" => lettersHead atHead H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w

/-- **`RidesPastS` at the lookup on the calls of a link.** Conditional on the head, the link and the
arrow from the letter f to the lookups' clause. -/
theorem lookupOpenItemsRidePastTheCallsOfALink {l : Nat} (linkBelow : l < 25)
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    RidesPastS (LK).thread Said (borderOf l false) :=
  lookupOpenItemsRidePast atHead H Q test carryX item n₁ n₂ b₀ Vd Rd f w Said
    keepsGivesTheLookupClause linkBelow false 0 (Nat.zero_le _)
    fun input _ opened notShut notOwed =>
      plainItemGoesBack atHead H Q test carryX item n₁ n₂ b₀ Vd Rd f w 0 input
        (openItemIsPlainAtTheCalls linkBelow opened notShut notOwed)

/-- **`RidesPastS` AT THE BORDER OF EVERY SITE ON THE CALLS.** Conditional on the head, the site and
the arrow from the letter f to the lookups' clause. -/
theorem lookupOpenItemsRidePastTheCalls (s : Site) (siteIsListed : s ∈ lookSites Zp)
    (onTheCalls : s.digits = false)
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    RidesPastS (LK).thread Said (borderOf s.link s.digits) := by
  rw [onTheCalls]
  exact lookupOpenItemsRidePastTheCallsOfALink atHead H Q test carryX item n₁ n₂ b₀ Vd Rd f w
    (ProofFile.Honest.K3.Law.AtThr.link_lt_head atHead s siteIsListed) keepsGivesTheLookupClause Said

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupOpenItemsRidePastTheCallsOfALink
#print axioms ProofFile.Honest.K3.Term.lookupOpenItemsRidePastTheCalls
