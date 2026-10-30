-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RidersAtHeadForm.lean: the kind "lookup" (K3): THE DEBT
`Behind` AT A LOOKUP'S MEMBER, AT THE FRAME'S LETTERS AT THE LIBRARY'S HEAD (`lettersHead`,
Honest/Thread/FirstHead.lean), WITH "THE FORM BEHIND" PAID TOO: from one record of premises
(FormRest.lean). So all three conjuncts of the debt come from payers, under premises none of which
is a conjunct of the debt.

  `behind_headDigits`    `Behind` at the digits, of whatever link
  `behindS_headDigits`   `BehindS … SaidOk` there: from the pair and the lighter record
  `behindS_headCalls`    `BehindS … SaidOk` at the calls: from the pair

AGAINST RidersAtHeadSite.lean's TWO: GONE: hFormOf. IN ITS STEAD: F: the record `FormRestDigits`,
`FormRestDigitsS` or `FormRestCalls` AT THESE LETTERS.
THE PREMISES THAT STAY, BY NAME: the head h (it rides in the notation LH); the site; R (`SiteRest`
at the prover's own halves); hKp (below); hH (at the digits); hb₀ (public); F; hst; hl.
IT IS NOT "Behind IS PAID": F'S FIELDS ARE PREMISES HERE. FormRest.lean's head names, field by
field, the library's law that would pay it at these letters' meaning where such a law's statement
was read, and says where none was. THAT LIST RULES; it is not summed up here. Some of these laws are
called in this folder since: FormRestAtHead.lean and its fellows (FormRestAtHeadFacts.lean,
FormRestAtHeadFill.lean [not in this library], FormRestAtHeadRest.lean [not in this library]).

THE FULL SIZE ALONE. No instance of the hypotheses beside the head is exhibited in this file.

THE FRAME'S LETTER FOR "keeps" BY PLACE IS A VARIABLE, Kp. hKp: at the site's own place it is the
lookups' clause `k3KeepsAt` (K3KeepsAt.lean), both ways: so the theorems hold at every laying of
that letter that has the lookups' clause there; at the frame's `kpBy`: KeepsAtKind.lean
[not in this library].

Conditional on the head `P5J.AtMgA`. That it holds at the goals' two named sets of public files is a
sealed theorem (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own
limits; this file does not call it.

`SiteRest` has the field half: the list of halves holds, at the site's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. Who pays the field, each at the fast summands and under hypotheses on
the list: where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot`
(HalfAtSite.lean [not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean
[not in this library]); where it holds a lot with the halves of `theLotInst` at the public part:
`half_like_ok`, `half_field_like` (HalfOfLotLike.lean [not in this library]). A lot of rows that
pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean) lays another term there: no file shows
the field at such a lot, so the theorems of this file that bear it cannot be called there as they
stand. Honest/K3/Law/Keep/ carries plays and runs from the one row to the other (`lotsPlayed_whole`,
`chain_lots`, `run_same`); no file carries these sentences over.

Limits. Nothing shows that the thread holds at any run, or that the record can be had. Nothing on
soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RidersAtHeadSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.FormRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn Oracle Strs)
open VerifiableInference.Desc.First (ModelPart)
open VerifiableInference.Desc.Sound (MsgT Frame)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X Wj : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LH" =>
  lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

/-- **THE DEBT `Behind` AT THE DIGITS, OF WHATEVER LINK.** No instance of the hypotheses beside the
head is exhibited in this file. ITS RECORD ASKS THREE FIELDS FROM THE THREAD ALONE: where their
payer wants the library's "reached": CALL `behindS_headDigits`.
-/
theorem behind_headDigits (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (R : SiteRest Zp cF H.first s lot J wit)
    (hKp : ∀ t t', Kp s.at_.place t t' ↔ k3KeepsAt Zp s.at_.place t t')
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (hdg : s.digits = true)
    (hb₀ : b₀ ≠ borderOf s.link s.digits + 1) (Fr : Frame) (y₀ : Fr.E.Str) {a' : Place}
    {sub : ModelPart} {xl : PlaceL} {told : List (List Oracle)}
    (F : FormRestDigits (LH) (borderOf s.link s.digits) Zp s a' sub xl told)
    (hst : ∀ c ∈ cs, c.lo ≤ borderOf s.link s.digits → borderOf s.link s.digits + 1 ≤ c.hi →
      StaysBy (LH).thread (borderOf s.link s.digits) c)
    (hl : ∀ c ∈ cs, c.lo = borderOf s.link s.digits + 1 →
      LaysAt (LH).thread (borderOf s.link s.digits) c) :
    Behind (LH).thread (borderOf s.link s.digits) := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, O, hS⟩ :=
    siteAt_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot J wit R
  exact behind_headSite h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot J wit R hKp hH hb₀
    (fun blk hb k st m E ds y cols s' hA hd hSt _ _ =>
      formOf_digits o pol lay KL Fd base A B O hS hH hdg Fr y₀ F blk hb k st m E ds y cols s' hA hd
        hSt)
    hst hl

/-- **THE DEBT `BehindS` AT THE DIGITS, OF WHATEVER LINK, FROM THE PAIR AND THE LIGHTER RECORD.** No
instance of the hypotheses beside the head is exhibited in this file. -/
theorem behindS_headDigits (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (R : SiteRest Zp cF H.first s lot J wit)
    (hKp : ∀ t t', Kp s.at_.place t t' ↔ k3KeepsAt Zp s.at_.place t t')
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (hdg : s.digits = true)
    (hb₀ : b₀ ≠ borderOf s.link s.digits + 1) (Fr : Frame) (y₀ : Fr.E.Str) {a' : Place}
    {sub : ModelPart} {xl : PlaceL} {told : List (List Oracle)}
    (F : FormRestDigitsS (LH) (borderOf s.link s.digits) Zp s a' sub xl told)
    (hst : ∀ c ∈ cs, c.lo ≤ borderOf s.link s.digits → borderOf s.link s.digits + 1 ≤ c.hi →
      StaysBy (LH).thread (borderOf s.link s.digits) c)
    (hl : ∀ c ∈ cs, c.lo = borderOf s.link s.digits + 1 →
      LaysAtS (LH).thread SaidOk (borderOf s.link s.digits) c) :
    BehindS (LH).thread SaidOk (borderOf s.link s.digits) := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, O, hS⟩ :=
    siteAt_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot J wit R
  exact behindS_headSite h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot J wit R hKp hH hb₀
    SaidOk
    (fun blk hb k st m E ds y cols s' hA hd hSt _ _ =>
      formOf_digitsS o pol lay KL Fd base A B O hS hH hdg Fr y₀ F blk hb k st m E ds y cols s' hA
        hd hSt)
    hst hl

/-- **THE DEBT `BehindS` AT THE CALLS, FROM THE PAIR.** No instance of the hypotheses beside the
head is exhibited in this file. -/
theorem behindS_headCalls (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (R : SiteRest Zp cF H.first s lot J wit)
    (hKp : ∀ t t', Kp s.at_.place t t' ↔ k3KeepsAt Zp s.at_.place t t')
    (hdg : s.digits = false)
    (hb₀ : b₀ ≠ borderOf s.link s.digits + 1) {Fr : Frame} (y₀ : Fr.E.Str) {a' : Place}
    {sub : ModelPart} {xl : PlaceL} {nsOf : Nat → Option Nat} {told : List (List Oracle)}
    (F : FormRestCalls (LH) (borderOf s.link s.digits) Zp s Fr a' sub xl nsOf told)
    (hst : ∀ c ∈ cs, c.lo ≤ borderOf s.link s.digits → borderOf s.link s.digits + 1 ≤ c.hi →
      StaysBy (LH).thread (borderOf s.link s.digits) c)
    (hl : ∀ c ∈ cs, c.lo = borderOf s.link s.digits + 1 →
      LaysAtS (LH).thread SaidOk (borderOf s.link s.digits) c) :
    BehindS (LH).thread SaidOk (borderOf s.link s.digits) := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, O, hS⟩ :=
    siteAt_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot J wit R
  exact behindS_headSite h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot J wit R hKp
    (fun h1 => by rw [hdg] at h1; exact nomatch h1) hb₀ SaidOk
    (fun blk hb k st m E ds y cols s' hA hd hSt _ _ =>
      formOf_calls o pol lay KL Fd base A B O hS hdg y₀ F blk hb k st m E ds y cols s' hA hd hSt)
    hst hl

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.behind_headDigits
#print axioms ProofFile.Honest.K3.Law.AtThr.behindS_headDigits
#print axioms ProofFile.Honest.K3.Law.AtThr.behindS_headCalls
