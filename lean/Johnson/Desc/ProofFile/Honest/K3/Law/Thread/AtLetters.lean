-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtLetters.lean: the honest side of the kind "lookup"
(K3). Conditional, under the library's hypothesis `P5J.AtMgA`: two of the frame's sentences on a
member of the first chain (`Plays`, `Accepted`, Honest/Thread/Pays.lean) at the first chain's
letters set to the library's own (`lettersAt`, Honest/Thread/FirstAt.lean), at the border in front
of a lookup's member. Two theorems, each a call.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins.

What is shown.
  `plays_letters`: `Plays` at these letters, at the written number of the border in front of the
    lookup (`borderOf s.link s.digits`).
  `accepted_letters`: `Accepted` there, at every letter fall.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): the three public files in
    scope, the description laid, its tests on the plan passed.
  `hsite`: s is a site of the public part.
  `R`: `SiteRest` (Honest/K3/Law/Thread/SiteAtLetters.lean): a sub-protocol of the lookups' lot
    stands at the site's place; the list of halves holds the lookup's seated row there; four tests
    with code on public data.
  `hH`: (in `accepted_letters`) `HeadReturns` (Honest/K3/Law/Thread/SiteThr.lean) at these letters:
    other kinds' hypothesis on the thread; it is asked at the digits of the head's link alone.
The thread itself is a hypothesis inside the two sentences.

Imported. Files under Honest/Thread/.
These theorems also stand over
files under Honest/SumLaw/ and Honest/Member/.

How the proof goes. The theorems of SiteThr.lean, called at what SiteAtLetters.lean gives.

Users. Honest/K3/Law/Thread/LotAtSite.lean calls both; Honest/K3/Law/Thread/AtThreadBridges.lean
[not in this library] imports this file.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
No value of `P5J.AtMgA` is exhibited here, nothing is evaluated at the full size, and no thread of a
description is exhibited. At the full size alone: that limit comes with `P5J.AtMgA`. The two
sentences are forms of hypotheses of the frame's. The acceptance is said at any summands: it says
nothing on values.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt WtF Script)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **It plays, at the first chain's letters set to the library's own, at the written number of the
border in front of the lookup.** Conditional on `P5J.AtMgA`, the site and `SiteRest`. At the full
size alone. No instance of these hypotheses is exhibited in this file. -/
theorem plays_letters (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr Xo Wj : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (R : SiteRest Zp cF hs s lot J wit) :
    Plays (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (borderOf s.link s.digits) := by
  obtain ⟨_, hS⟩ := siteAt_lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps s
    hsite lot J
    wit R
  exact plays_site hS

/-- **It is accepted, there, at every letter fall.** Conditional on the same and on `HeadReturns` at
these letters. That the description can be opened is a field of `P5J.AtMgA`. At the full size alone.
No instance of these hypotheses is exhibited in this file. -/
theorem accepted_letters (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr Xo Wj : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (R : SiteRest Zp cF hs s lot J wit)
    (hH : HeadReturns (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
      (borderOf s.link s.digits) Zp s)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    Accepted (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread fall
      (borderOf s.link s.digits) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨_, hS⟩ := siteAt_lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps s
    hsite lot J
    wit R
  have hS' : SiteAt (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
      (borderOf s.link s.digits) Zp Bs cF s lot J wit h.𝔇.sent h.𝔇.l3 :=
        { hS with inLot := R.inLot }
  exact accepted_site _ _ _ _ _ base _ _ O hS' hH fall

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.plays_letters
#print axioms ProofFile.Honest.K3.Law.AtThr.accepted_letters
