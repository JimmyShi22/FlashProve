-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RidersAtHeadSite.lean: the kind "lookup" (K3): `Behind`
(Honest/Thread/Pays.lean) at a lookup's member, at the letters `lettersHead` under the library's
hypothesis `P5J.AtMgA`, with the structure `K3AtSite` (Honest/K3/Law/Thread/AtThreadSite.lean) shown
there from the lookups' own smaller hypotheses. The theorems conclude `Behind` only from a
hypothesis (`hFormOf`) that is itself one of its three conjuncts: they do not show `Behind`
outright. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: `Behind T b` (Honest/Thread/Pays.lean) is a form of
hypothesis at the member number b, with three conjuncts behind the member's accepted step: the form
behind, the rider behind, and keeps. `BehindS` (Honest/Thread/PaysS.lean) is the same from the pair:
the thread's relation with a sentence Said beside it. `lettersHead` (Honest/Thread/FirstHead.lean)
is `lettersAt` (Honest/Thread/FirstAt.lean) at values of its letters, by its definition; and
`siteAt_lettersAt` (Honest/K3/Law/Thread/SiteAtLetters.lean) is stated for arbitrary values of these
letters.

What is shown.
  `atSite_lettersHead`: the structure `K3AtSite`, with the description's return at the same values.
  `headReturns_lettersHead`: `hH` below, from the three hypotheses of
    Honest/K3/Law/Thread/HeadReturnsOf.lean.
  `behind_headSite`, `behindS_headSite`: the two theorems of Honest/K3/Law/Thread/RidersAtHead.lean
    at the site's own border.

Hypotheses that remain. Against the two theorems of RidersAtHead.lean three hypotheses are gone: the
description's return (a field of `P5J.AtMgA` gives it); `hS`, the structure; `hb`, "the member is
there" (where it is not, `Behind` is empty). In their place stand:
  `R`: `SiteRest` (Honest/K3/Law/Thread/SiteAtLetters.lean) at the prover's own halves: a
    sub-protocol of the lookups' lot stands at the site's place (inLot, lotPlace); the prover's list
    of halves holds the lookup's seated row there (half); four tests with code on public data (fits,
    ok, shapeIs, usedIs).
  `hH`: `HeadReturns` (Honest/K3/Law/Thread/SiteThr.lean). It says nothing unless the site is on the
    digits and its caller is the head; there: `headReturns_lettersHead`.
These stay: `h`, the library's hypothesis; `hsite`, the site; `hKp`; `hb₀` (on public data);
`hFormOf`, the form behind: one of the three conjuncts of `Behind`; `hst`; `hl`. The letter for
"keeps" by place, Kp, is a variable. `hKp`: at the site's own place it is the lookups' clause
`k3KeepsAt` (Honest/K3/Law/Thread/K3KeepsAt.lean), in both directions; it is handed on to the two
theorems of RidersAtHead.lean, whose proofs use one direction alone. So the theorems hold at every
value of that letter that has the lookups' clause there. At `kpBy` (Honest/Thread/KeepsBy.lean):
`hKp_kind` (Honest/K3/Law/Thread/KeepsKind.lean [not in this library]) shows `hKp`, where f at the
kind K3 is the lookups' clause; see also Honest/K3/Law/Thread/KeepsAtKind.lean [not in this
library].
In `headReturns_lettersHead`: `hHead`, `hN`, `hRest`: those of `headReturns_of_thr`
(Honest/K3/Law/Thread/HeadReturnsOf.lean), at this thread.

Imported, through Honest/K3/Law/Thread/RidersAtHead.lean. Files under Honest/Thread/.

Users. `plays_headSite` and `accepted_headSite` (Honest/K3/Law/Thread/PlaysAtHead.lean
[not in this library]) call `atSite_lettersHead`.

Limits. At the full size alone. That the four tests of `R` accept there is not shown in this file.
Nothing here shows that the thread's relation holds at any run. No instance of these hypotheses is
exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RidersAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn Strs)
open VerifiableInference.Desc.K3 (k3OnOut)
open VerifiableInference.Desc.First.Look (weightsClaim)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

local notation "FS" => VerifiableInference.Desc.First.S

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

/-- **The structure `K3AtSite` at the letters `lettersHead` under `P5J.AtMgA`**, with the
description's return at the same values. -/
theorem atSite_lettersHead (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (R : SiteRest Zp cF H.first s lot J wit)
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s) :
    ∃ o pol lay KL Fd Bs base A B, IM.Open o pol lay KL Fd Zp Bs base cF A B ∧
      K3AtSite (LH).thread (borderOf s.link s.digits) Zp Bs cF s lot J wit := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨_, hS⟩ : ∃ Bs', SiteAt (LH) (borderOf s.link s.digits) Zp Bs' cF s lot J wit h.𝔇.sent
      h.𝔇.l3 := siteAt_lettersAt h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite lot J wit R
  have hS' : SiteAt (LH) (borderOf s.link s.digits) Zp Bs cF s lot J wit h.𝔇.sent h.𝔇.l3 :=
    { hS with inLot := R.inLot }
  exact ⟨_, _, _, _, _, Bs, base, _, _, O, atSite_of_site hS' hH⟩

/-- **`HeadReturns` at these letters, from the thread's relation in front, one public test and two
returns that are for other kinds' files to show** (Honest/K3/Law/Thread/HeadReturnsOf.lean): for
`hH` at the digits of the head's link. -/
theorem headReturns_lettersHead (b : Nat) (s : Site)
    (hHead : ∀ (k : Coins Bk) (st : FS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
      Thr (LH).thread b k st m E →
      ∃ a, st.here = .head a ∧ a.opened = true ∧ a.x.isSome = true ∧ a.t.isSome = true)
    (hN : (Zp.p.X.H.NCL == 1) = true)
    (hRest : ∀ (k : Coins Bk) (st : FS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) a x tt,
      Thr (LH).thread b k st m E → st.here = .head a → a.x = some x → a.t = some tt →
      ∃ cov claim, st.covered Zp.p.X.T Zp.p.X.P.h.V = .ok cov ∧ weightsClaim
        { h := Zp.p.X.hS, L := Zp.p.X.HLy, b := OnBytes.Model.Verify.borderOf Zp.p.X.y,
          hp := Zp.p.X.H, cov := cov, x := x, t := tt,
          iU3 := (Zp.p.X.H.tl.ix.U.getD 2 none).getD 0 } Zp.p.X.layers.wsLay = .ok claim) :
    HeadReturns (LH) b Zp s :=
  headReturns_of_thr (LH).thread b Zp s hHead hN hRest

/-- **`Behind` at the site's own border.** No instance of these hypotheses is exhibited in this
file. -/
theorem behind_headSite (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (R : SiteRest Zp cF H.first s lot J wit)
    (hKp : ∀ t t', Kp s.at_.place t t' ↔ k3KeepsAt Zp s.at_.place t t')
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s)
    (hb₀ : b₀ ≠ borderOf s.link s.digits + 1)
    (hFormOf : ∀ blk, (LH).thread.bs[borderOf s.link s.digits]? = some blk → ∀ (k : Coins Bk)
      (st : FS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (ds : List Fmt.Drawn)
      (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X) (cols : List OpenedColumn) (s' : FS),
      Thr (LH).thread (borderOf s.link s.digits) k st m E → drawsFit blk.rounds ds = true →
      (LH).thread.Stepped blk k st m E ds y cols s' → k3KeepsAt Zp s.at_.place st s' →
      k3OnOut s.p s' = true → (LH).thread.Form (borderOf s.link s.digits + 1) k s' y.2)
    (hst : ∀ c ∈ cs, c.lo ≤ borderOf s.link s.digits → borderOf s.link s.digits + 1 ≤ c.hi →
      StaysBy (LH).thread (borderOf s.link s.digits) c)
    (hl : ∀ c ∈ cs, c.lo = borderOf s.link s.digits + 1 →
      LaysAt (LH).thread (borderOf s.link s.digits) c) :
    Behind (LH).thread (borderOf s.link s.digits) := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, O, hS⟩ :=
    atSite_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot J wit R hH
  cases hb : (LH).thread.bs[borderOf s.link s.digits]? with
  | none =>
    intro blk hblk
    rw [hb] at hblk
    exact nomatch hblk
  | some blk =>
    exact behind_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w o pol lay KL Fd base A B O
      hS hKp
      hb hb₀ hFormOf hst hl

/-- **The same from the pair.** No instance of these hypotheses is exhibited in this file. -/
theorem behindS_headSite (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (R : SiteRest Zp cF H.first s lot J wit)
    (hKp : ∀ t t', Kp s.at_.place t t' ↔ k3KeepsAt Zp s.at_.place t t')
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s)
    (hb₀ : b₀ ≠ borderOf s.link s.digits + 1)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hFormOf : ∀ blk, (LH).thread.bs[borderOf s.link s.digits]? = some blk → ∀ (k : Coins Bk)
      (st : FS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (ds : List Fmt.Drawn)
      (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X) (cols : List OpenedColumn) (s' : FS),
      ThrS (LH).thread Said (borderOf s.link s.digits) k st m E →
      drawsFit blk.rounds ds = true → (LH).thread.Stepped blk k st m E ds y cols s' →
      k3KeepsAt Zp s.at_.place st s' → k3OnOut s.p s' = true →
      (LH).thread.Form (borderOf s.link s.digits + 1) k s' y.2)
    (hst : ∀ c ∈ cs, c.lo ≤ borderOf s.link s.digits → borderOf s.link s.digits + 1 ≤ c.hi →
      StaysBy (LH).thread (borderOf s.link s.digits) c)
    (hl : ∀ c ∈ cs, c.lo = borderOf s.link s.digits + 1 →
      LaysAtS (LH).thread Said (borderOf s.link s.digits) c) :
    BehindS (LH).thread Said (borderOf s.link s.digits) := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, O, hS⟩ :=
    atSite_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot J wit R hH
  cases hb : (LH).thread.bs[borderOf s.link s.digits]? with
  | none =>
    intro blk hblk
    rw [hb] at hblk
    exact nomatch hblk
  | some blk =>
    exact behindS_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w o pol lay KL Fd base A B O
      hS hKp
      hb hb₀ Said hFormOf hst hl

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.atSite_lettersHead
#print axioms ProofFile.Honest.K3.Law.AtThr.headReturns_lettersHead
#print axioms ProofFile.Honest.K3.Law.AtThr.behind_headSite
#print axioms ProofFile.Honest.K3.Law.AtThr.behindS_headSite
