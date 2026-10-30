-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HeadReturnsElse.lean: the hypothesis `HeadReturns`
(Honest/K3/Law/Thread/SiteThr.lean) is empty at every lookup but that on the digits of the head's
link; so there "it is accepted" stands without it. Conditional. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins. In this file: L is the structure of the first chain's letters (`Letters`,
Honest/Thread/First.lean), and b is a border's number. `HeadReturns` begins "the site is a lookup on
the digits, and its caller is the head". So it is empty at a lookup on the calls, and at a site
whose caller is not the head.

What is shown.
  `else_empty`: the same for a hypothesis of that form at any thread.
  `headReturns_onCalls`: s.digits = false → HeadReturns L b Z s. It also stands, under another name,
    in Honest/K3/Law/Thread/BehindSiteCalls.lean,
    which is not imported here.
  `headReturns_notHead`: s.caller ≠ .head → HeadReturns L b Z s.
  `headReturns_else`: s.digits = false ∨ s.caller ≠ .head → HeadReturns L b Z s.
  `accepted_of_k3Fits_else`: `accepted_of_k3Fits` (Honest/K3/Law/Thread/RestOfFits.lean) at such a
    site, without that hypothesis.

Hypotheses that remain, in `accepted_of_k3Fits_else`.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): the three public files in
    scope, the description laid, its tests on the plan passed.
  `hsite`, `hn`: s is a site of the public part; it is on the calls, or its caller is not the head.
  `hF`: `k3Fits` (Honest/K3/SeatFits.lean) accepts at the site.
  `ht`: the site's place stands in the written list of places (`P5J.At.ps`,
    Johnson/P5J/LettersAt.lean).
  `hh`: the list of halves holds the lookup's seated row at the site's place.
In the others: `hd`: (in `headReturns_onCalls`) the site is on the calls. `hc`: (in
`headReturns_notHead`) its caller is not the head.

Imported. Files under Honest/Thread/.

Users. Honest/K3/Law/Thread/CallerAtLink.lean imports this file.

Limits. At the digits of the head's link the hypothesis remains. At the full size alone: that limit
comes with `P5J.AtMgA`. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RestOfFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Letters lettersAt WtF Script)

/-- **Whatever is asked under "the site is a lookup on the digits, and its caller is the head" is
empty at every other site**: for a hypothesis of that form at any thread. -/
theorem else_empty {s : Site} (hn : s.digits = false ∨ s.caller ≠ .head) {P : Prop} :
    s.digits = true → s.caller = .head → P := fun h1 h2 =>
  hn.elim (fun h => by rw [h] at h1; cases h1) fun h => absurd h2 h

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok : Type}
  (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- The hypothesis on the head's digits is empty at a lookup on the calls. -/
theorem headReturns_onCalls (b : Nat) (Z : Pub) (s : Site) (hd : s.digits = false) :
    HeadReturns L b Z s := fun h1 => by
  rw [hd] at h1
  cases h1

/-- The hypothesis on the head's digits is empty at a site whose caller is not the head. -/
theorem headReturns_notHead (b : Nat) (Z : Pub) (s : Site) (hc : s.caller ≠ .head) :
    HeadReturns L b Z s := fun _ h2 => absurd h2 hc

/-- It is empty at every lookup but that on the digits of the head's link. -/
theorem headReturns_else (b : Nat) (Z : Pub) (s : Site)
    (hn : s.digits = false ∨ s.caller ≠ .head) : HeadReturns L b Z s :=
  hn.elim (headReturns_onCalls L b Z s) (headReturns_notHead L b Z s)

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr Xo Wj : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **At every lookup but that on the digits of the head's link it is accepted, at every letter
fall.** Conditional on `P5J.AtMgA`, the site, `k3Fits`, the place's test and the half. At the full
size alone. No instance of these hypotheses is exhibited in this file. -/
theorem accepted_of_k3Fits_else (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (hF : k3Fits Zp cF.blocksInOrder s = true)
    (ht : P5J.At.ps.contains s.at_.place = true)
    (hh : hs.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_))
    (hn : s.digits = false ∨ s.caller ≠ .head)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    Accepted (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread fall
      (borderOf s.link s.digits) :=
  accepted_of_k3Fits h hs Q stored ans test carryX item n₁ n₂ valid rides keeps s hsite J wit hF ht
    hh (headReturns_else _ _ Zp s hn) fall

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.else_empty
#print axioms ProofFile.Honest.K3.Law.AtThr.headReturns_onCalls
#print axioms ProofFile.Honest.K3.Law.AtThr.headReturns_notHead
#print axioms ProofFile.Honest.K3.Law.AtThr.headReturns_else
#print axioms ProofFile.Honest.K3.Law.AtThr.accepted_of_k3Fits_else
