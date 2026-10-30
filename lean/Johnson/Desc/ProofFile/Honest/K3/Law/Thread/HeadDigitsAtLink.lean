-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HeadDigitsAtLink.lean: the kind "lookup" (K3): the
lookup on the digits of the head's link, at the link's number, under the library's hypothesis
`P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): three theorems of other files of this folder, stated without
three of their public hypotheses (`hq`, `hN`, `hc`), which are shown here. Theorems: each is a
composition of earlier ones; no definition, no new argument.

Terms. Honest/K3/GLOSSARY.md. In this file: the head's link is link 24. `Carries` and `Returns` are
definitions of Honest/Thread/Shape.lean; `LaysAt` and `riderHead` are definitions of
Honest/Thread/Riders.lean. The thread is that of `lettersHead` (Honest/Thread/FirstHead.lean), with
"keeps" given by the place's kind (`kpBy`, Honest/Thread/KeepsBy.lean).

What is shown.
  `ncl_head`: there is one claim on the weights. It calls the library's `LT28.K11Tests.public_H_ncl`
    (Johnson/Desc/Sound/K11Tests/NclHeadInScope.lean).
  `caller_head_site`: a site at link 24 has the caller "head", by `site_facts` and `caller_head`
    (Honest/K3/Law/MemberSite.lean) and `isHead_head` (Honest/K3/Law/Thread/QuietAtHeadLink.lean).
  `carries_headDigits_link`: `carries_headDigits` (Honest/K3/Law/Thread/CarriesHeadDigits.lean)
    without `hq`.
  `returns_headDigits_link`: `returns_headDigits` (CarriesHeadDigits.lean) without `hN` and `hc`.
  `lays_foldDrawn_thread`: `lays_foldDrawn_head` (Honest/K3/Law/Thread/LaysFold.lean) at the thread
    above, without `hq`; the description's return, the lot's place and `K3MemberAt`
    (Honest/K3/Law/Thread/K3KeepsStep.lean) are shown by `memberAt_thread`
    (Honest/K3/Law/Thread/KeepsThread.lean).
The hypothesis `e`, s.link = 24, stands for both ways in which these theorems say "the head's
digits": the equation on `quietAt` (`quiet_head_site`, QuietAtHeadLink.lean) and the site's caller.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA`.
  `hs`, `e`, `hd`: s is a site of the public part; its link is 24; it is on the digits.
  `hL`: `layoutOk` (Honest/K3/Law/Thread/ClaimSizes.lean) passes. It is public; it is assumed here
    and shown in no theorem of this file.
  `hok`: the face's test passes. It is public. (`face_ok_site`,
    Johnson/AtFull/Shape/FaceAtSites.lean, a file that is not imported here, states it at every site
    of every public
    part.)
  `hg`, `hv`: the letters g and vals of the shape at this border are `headDigitsG` and give
    `headVals`.
  `hF`: in front of the lookup foldDrawn is 0. It is another kind's rider; it is assumed here and
    shown in no theorem of this file.

Imported: Honest/Thread/Shape.lean, Honest/Thread/Riders.lean, Honest/Thread/FirstHead.lean and
Honest/Thread/KeepsBy.lean.

Users. Honest/K3/Law/Thread/LaysNextLight.lean calls `caller_head_site`.

Limits. At the full size alone: that limit comes with `P5J.AtMgA`. `Carries` and `LaysAt` speak from
an acceptance alone. `Returns` says that the member's decision returns, not that its step accepts.
No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CarriesHeadDigits
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LaysFold
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.KeepsThread
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietAtHeadLink
import Johnson.Desc.Sound.K11Tests.NclHeadInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LK" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w

/-! ## 1 Two public facts -/

include h in
/-- **One claim on the weights.** -/
theorem ncl_head : (Zp.p.X.H.NCL == 1) = true := by
  have e : Zp.p.X.H.NCL = 1 := LT28.K11Tests.public_H_ncl h.pubOne
  rw [e]
  rfl

include h in
/-- **A site at link 24 has the caller "head".** -/
theorem caller_head_site (s : Site) (hs : s ∈ lookSites Zp) (e : s.link = 24) : s.caller = .head
    := by
  unfold lookSites at hs
  obtain ⟨y, -, hy⟩ := List.mem_filterMap.1 hs
  obtain ⟨-, -, f3, -, -, -, f7, -⟩ := site_facts _ _ y s hy
  rw [f7, ← f3, e]
  exact caller_head _ 24 (isHead_head h)

/-! ## 2 On the chain's shape -/

include h in
/-- **`carries_headDigits` without `hq`.** Conditional on `P5J.AtMgA`, the site, `hL` and `hg`.
No instance of these hypotheses is exhibited in this file. -/
theorem carries_headDigits_link (s : Site) (hs : s ∈ lookSites Zp) (e : s.link = 24)
    (hd : s.digits = true) (hL : layoutOk Zp.p.X.HLy Zp.p.X.layers.wsLay = true) (ft : Nat)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → TS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g (borderOf s.link true) = headDigitsG s.shape s.p.first Zp.p.X) :
    Carries cF.blocksInOrder ft ⟨ChainSh, chainSh, g, vals⟩ (borderOf s.link true) := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs (by omega)
  rw [hd] at hm
  exact carries_headDigits _ _ _ _ Fd Zp Bs base cF A B O s hs hd lot hb hbs (quiet_head_site h s e)
    hL cF.blocksInOrder ft _ hm g vals hg

include h in
/-- **`returns_headDigits` without `hN` and `hc`.** Conditional on `P5J.AtMgA`, the site, `hok`,
`hg` and `hv`. No instance of these hypotheses is exhibited in this file. -/
theorem returns_headDigits_link (s : Site) (hs : s ∈ lookSites Zp) (e : s.link = 24)
    (hd : s.digits = true) (hok : s.at_.face.ok = true) (ft : Nat)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → TS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g (borderOf s.link true) = headDigitsG s.shape s.p.first Zp.p.X)
    (hv : ∀ st rs cols, vals (borderOf s.link true) st rs cols = true →
      headVals Zp.p.X st = true) :
    Returns cF.blocksInOrder ft ⟨ChainSh, chainSh, g, vals⟩ (borderOf s.link true) := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs (by omega)
  rw [hd] at hm
  exact returns_headDigits _ _ _ _ Fd Zp Bs base cF A B O s hs hd (caller_head_site h s hs e) lot hb
    hbs hok (ncl_head h) cF.blocksInOrder ft _ hm g vals hg hv

/-! ## 3 The rider on foldDrawn, at the thread of `lettersHead` -/

/-- **`lays_foldDrawn_head` at the thread of `lettersHead`, without `hq`.** Conditional on
`P5J.AtMgA`, the site and `hF`. No instance of these hypotheses is exhibited in this file. -/
theorem lays_foldDrawn_thread (s : Site) (hs : s ∈ lookSites Zp) (e : s.link = 24)
    (hd : s.digits = true)
    (hF : ∀ (k : Coins Bk) (st : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
      Thr (LK).thread (borderOf s.link true) k st m E →
      ∀ a, st.here = .head a → a.tl.foldDrawn = 0) (hi : Nat) :
    LaysAt (LK).thread (borderOf s.link true)
      (riderHead (borderOf s.link true + 1) hi fun a => a.tl.foldDrawn = 1) := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hp, hM⟩ :=
    memberAt_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w s.link (by omega) true
  have hlp : lot.place = s.at_.place := by
    have e' := site_place_head h s hs
    rw [hd] at e'
    exact hp.trans e'.symm
  exact lays_foldDrawn_head (LK).thread _ _ _ _ Fd base A B O hs hlp hM hd (quiet_head_site h s e)
    hF hi

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.ncl_head
#print axioms ProofFile.Honest.K3.Law.AtThr.caller_head_site
#print axioms ProofFile.Honest.K3.Law.AtThr.carries_headDigits_link
#print axioms ProofFile.Honest.K3.Law.AtThr.returns_headDigits_link
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_foldDrawn_thread
