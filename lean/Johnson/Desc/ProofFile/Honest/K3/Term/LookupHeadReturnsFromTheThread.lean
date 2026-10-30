-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupHeadReturnsFromTheThread.lean: the kind "lookup" (K3):
`HeadReturns` (Honest/K3/Law/Thread/SiteThr.lean), the hypothesis of the lookups' earlier lemmas that
is asked from the thread's relation alone, at the letters `lettersHead`
(Honest/Thread/FirstHead.lean), at every value of their arguments and at every site. One theorem: a
call of `lookupHeadReturnsAtLettersHead` (Honest/K3/Term/LookupHeadStepReturns.lean) at the Said that
always holds.

Hypotheses that remain. The head `P5J.AtMgA`; the site.

Limits. An implication from the thread's relation. Nothing shows that the relation holds at a run.
The full size alone: that limit comes with the head.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupHeadStepReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Law.AtThr

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`HeadReturns` at the letters `lettersHead`, at every site.** Conditional on the head alone. -/
theorem lookupHeadReturnsFromTheThreadAlone (s : Site) (hsite : s ∈ lookSites Zp) :
    HeadReturns (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      (borderOf s.link s.digits) Zp s :=
  fun hd hc k st m E F rs g G s' hA =>
    lookupHeadReturnsAtLettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (fun _ _ _ => True) s
      hsite hd hc k st m E F rs g G s' ⟨hA, trivial⟩

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupHeadReturnsFromTheThreadAlone
