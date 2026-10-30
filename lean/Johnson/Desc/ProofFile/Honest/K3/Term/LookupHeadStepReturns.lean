-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupHeadStepReturns.lean: the kind "lookup" (K3): the one
hypothesis of the lookups' acceptance that speaks at one border alone: behind the lookup on the
digits of the head's link stands a step without a round (`quietHead`), and it has to return at the
state that the lookup's own decision leaves (`LookupHeadReturns`,
Honest/K3/Term/LookupPlaysAndIsAccepted.lean). Here that hypothesis is shown at the first chain's
thread at the library's head, at every letter and every Said. Three theorems.

  `lookupHeadStepReturnsAtAState`    at ONE state at which the test on values `headVals`
                                     (Honest/K3/Law/Thread/ClaimReturns.lean) accepts: the step
                                     returns behind the lookup's decision
  `lookupHeadReturnsOfValues`        so `LookupHeadReturns` at any thread and any Said at whose
                                     stands that test accepts
  `lookupHeadReturnsAtLettersHead`   at the thread of `lettersHead` (Honest/Thread/FirstHead.lean),
                                     at every letter, every Said and every site: under the head
                                     alone

How. The first follows the proof of `headReturns_of_thr` (Honest/K3/Law/Thread/HeadReturnsOf.lean),
taken at one state. That lemma's hypothesis "the head's part of the state is opened" is not asked
here: the lookup's decision returns only where the state holds a ledger (`decideVia_whole`), and in
the head's link the state holds one only where that part is opened (`S.fork?`,
Johnson/Desc/First/State.lean). The last: off the digits of link 24 the hypothesis is idle
(`caller_head_iff`, Honest/K3/Law/Thread/CallerAtLink.lean); there the border is 345, the thread
gives the reach by the members' own steps (`thr_reach`, Honest/Thread/ReachFacts.lean), and at every
state so reached the test accepts (`headVals_reach`, Johnson/AtFull/Shape/HeadValsReach.lean).

Hypotheses that remain. The head `P5J.AtMgA`.

Limits. Implications from the thread's relation. Nothing shows that the relation holds at a run. The
full size alone: that limit comes with the head. It stands over
Johnson/AtFull/Shape/HeadValsReach.lean and three files beneath it.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupPlaysAndIsAccepted
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadReturnsThin
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadDigitsAtLink
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.AtFull.Shape.HeadValsReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf seatDigits)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF thr_reach head_len)
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Law.AtThr

local notation "FS" => VerifiableInference.Desc.First.S

/-- **At one state: the step without a round behind the lookup on the head's digits returns.** -/
theorem lookupHeadStepReturnsAtAState (Z : Pub) (s : Site) (hDigits : s.digits = true)
    (hOneClaim : (Z.p.X.H.NCL == 1) = true) {st s' : FS} {rs : List Fmt.RoundView}
    (hValues : headVals Z.p.X st = true)
    (hDecision : decideVia (seatOf K3Lot.ofForm s.digits) s.p st rs = .ok s') :
    ∃ t, HeadBehind Z.p.X s' t := by
  obtain ⟨a, ha, hx, ht⟩ := headVals_head hValues
  obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.1 hx
  obtain ⟨tt, ht'⟩ := Option.isSome_iff_exists.1 ht
  obtain ⟨cov, claim, hcov, hw⟩ := headVals_gives hValues ha hx' ht'
  rw [hDigits] at hDecision
  obtain ⟨F₁, H, G₁, a1, _, _, _, _, e⟩ :=
    decideVia_whole (seatDigits K3Lot.ofForm) s.p st s' rs hDecision
  have a1' : st.fork? = some F₁ := a1
  have ho : a.opened = true := by
    cases hop : a.opened with
    | true => rfl
    | false =>
      have hnone : st.fork? = none := by simp [S.fork?, ha, hop]
      rw [hnone] at a1'
      cases a1'
  obtain ⟨tl, htl⟩ := tl_of_fork st a1'
  rw [digits_put K3Lot.ofForm st htl a1' H G₁] at e
  simp only [S.putTl, S.putFork, ha, ho, if_true] at e
  refine ⟨_, quietHead_returns Z.p.X s' (a := _) (by rw [e]) ?_ ?_ ?_ ?_ hw hOneClaim⟩
  · rfl
  · rw [e]
    exact hcov
  · exact hx'
  · exact ht'

/-- **`LookupHeadReturns` at any thread and any Said at whose stands the test on values accepts.** -/
theorem lookupHeadReturnsOfValues {Bk : ProverCoinCounts} {V W X Pb : Type}
    (T : Thread Bk FS ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) (Z : Pub)
    (s : Site) (hOneClaim : (Z.p.X.H.NCL == 1) = true)
    (hStands : s.digits = true → s.caller = .head → ∀ (k : Coins Bk) (st : FS) (m : Mid W X)
      (E : Env), ThrS T Said b k st m E → headVals Z.p.X st = true) :
    LookupHeadReturns T Said b Z s := by
  intro hd hc k st m E _ rs _ _ s' hA _ _ _ hdv
  exact lookupHeadStepReturnsAtAState Z s hd hOneClaim (hStands hd hc k st m E hA) hdv

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`LookupHeadReturns` at the first chain's thread at the library's head, at every letter, every
Said and every site.** Conditional on the head alone. -/
theorem lookupHeadReturnsAtLettersHead
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (s : Site)
    (hsite : s ∈ lookSites Zp) :
    LookupHeadReturns (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (borderOf s.link s.digits) Zp s := by
  refine lookupHeadReturnsOfValues _ Said _ Zp s (ncl_head h) fun hd hc k st m E hA => ?_
  have hl : s.link = 24 := (caller_head_iff h s hsite).1 hc
  have hb : borderOf s.link s.digits = 345 := by rw [hl, hd]; rfl
  rw [hb] at hA
  exact Johnson.AtFull.Shape.headVals_reach h (a := (m.st.input.x.pub, st))
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [head_len h]; decide) hA.1)

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupHeadStepReturnsAtAState
#print axioms ProofFile.Honest.K3.Term.lookupHeadReturnsOfValues
#print axioms ProofFile.Honest.K3.Term.lookupHeadReturnsAtLettersHead
