-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RestOfFits.lean: conditional: at the first chain's
letters set to the library's own, the test `k3Fits` (Honest/K3/SeatFits.lean) at the seat gives four
of the six hypotheses that remain. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins. In this file: `SiteRest'` (Honest/K3/Law/Thread/LotAtSite.lean) has six fields: the
site's place stands in the written list; the list of halves holds the lookup's seated row at that
place; four tests with code on public data. The four are among the tests of `k3Fits`, asked at the
description's own first chain. So the sentences "it plays" and "it is accepted" carry `k3Fits` as
one named public hypothesis.

What is shown.
  `rest_of_k3Fits`: `SiteRest'` from `k3Fits`, the place's test and the half.
  `plays_of_k3Fits`, `accepted_of_k3Fits`: the two sentences (`Plays`, `Accepted`,
    Honest/Thread/Pays.lean) under it.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): the three public files in
    scope, the description laid, its tests on the plan passed.
  `hsite`: s is a site of the public part.
  `hF`: `k3Fits` accepts at the first chain's own list.
  `ht`: the site's place stands in the written list of places (`P5J.At.ps`,
    Johnson/P5J/LettersAt.lean).
  `hh`: the list of halves holds the lookup's seated row there.
  `hH`: (in `accepted_of_k3Fits`) `HeadReturns` (Honest/K3/Law/Thread/SiteThr.lean).

Imported. Files under Honest/Thread/.

Users. Honest/K3/Law/Thread/HeadReturnsElse.lean calls `accepted_of_k3Fits`.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
At the full size alone: that limit comes with `P5J.AtMgA`.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LotAtSite
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatFitsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt WtF Script)

/-- **`SiteRest'`.** Conditional on an acceptance of `k3Fits` at the first chain's own list, the
site's place standing in the written list, and the list of halves holding the seated row there.
No instance of these hypotheses is exhibited in this file. -/
theorem rest_of_k3Fits {W₀ Rc Xi Tr Xo Wj : Type} (Zp : Pub) (cF : Chain TS ProofFile.Cl)
    (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xo)) (s : Site) (J : LookJobs Wj)
    (wit : Local W₀ Rc Xi Tr → Wj) (hF : k3Fits Zp cF.blocksInOrder s = true)
    (ht : P5J.At.ps.contains s.at_.place = true)
    (hh : hs.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_)) : SiteRest' Zp cF hs s J wit := by
  obtain ⟨a1, _, a3, _, _, a6, a7, _⟩ := fits_gives Zp cF.blocksInOrder s hF
  exact ⟨ht, hh, a1, a3, a6, a7⟩

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

/-- **It plays.** Conditional on `P5J.AtMgA`, the site, `k3Fits`, the place's test and the half. At
the full size alone. No instance of these hypotheses is exhibited in this file. -/
theorem plays_of_k3Fits (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (hF : k3Fits Zp cF.blocksInOrder s = true)
    (ht : P5J.At.ps.contains s.at_.place = true)
    (hh : hs.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_)) :
    Plays (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (borderOf s.link s.digits) :=
  plays_lettersAt' h hs Q stored ans test carryX item n₁ n₂ valid rides keeps s hsite J wit
    (rest_of_k3Fits Zp cF hs s J wit hF ht hh)

/-- **It is accepted, at every letter fall.** Conditional on the same and on `HeadReturns`. At the
full size alone. No instance of these hypotheses is exhibited in this file. -/
theorem accepted_of_k3Fits (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (hF : k3Fits Zp cF.blocksInOrder s = true)
    (ht : P5J.At.ps.contains s.at_.place = true)
    (hh : hs.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_))
    (hH : HeadReturns (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
      (borderOf s.link s.digits) Zp s)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    Accepted (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread fall
      (borderOf s.link s.digits) :=
  accepted_lettersAt' h hs Q stored ans test carryX item n₁ n₂ valid rides keeps s hsite J wit
    (rest_of_k3Fits Zp cF hs s J wit hF ht hh) hH fall

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.rest_of_k3Fits
#print axioms ProofFile.Honest.K3.Law.AtThr.plays_of_k3Fits
#print axioms ProofFile.Honest.K3.Law.AtThr.accepted_of_k3Fits
