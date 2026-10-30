-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/SiteAllFifty.lean: conditional on the library's
hypothesis `P5J.AtMgA` alone, a site stands at each of the fifty addresses of the lookups' lot, and
its face passes the hearing's own test on its numbers: no public test is left. Theorems, each one or
two calls; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: `hr` is the public test that `site_there_head`
(Honest/K3/Law/Thread/SiteThereHead.lean) leaves at the digits: `rngIn` (Honest/K3/Lot.lean) returns
a number at the link.

What is shown.
  `site_at_all_fifty`: `site_there_head` without `hr`: at every link below 25, at either sort.
    (`site_digits`, Honest/K3/Law/Thread/RngHeadPaid.lean, and `site_digits_paid`,
    Honest/K3/Law/Thread/RngWrittenHolds.lean, have the same statement.)
  `digits_heard_all`: `digits_heard_link` (Honest/K3/Law/Thread/DigitsHeardLink.lean) without `hr`.
  `keepsDigits_all`: `keepsDigits_thread` (Honest/K3/Law/Thread/QuietAtLink.lean) without `hr`, at
    every link below 24.
  `face_ok_all`: at every link below 25, at either sort, a site stands whose face passes `Face.ok`.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hl`: the link's number is below 25 (in `keepsDigits_all`: below 24).
  `hf`, in `keepsDigits_all` alone: the family of clauses has `k3KeepsAt Zp` at the kind K3, as in
    `keepsDigits_thread`.

Imported. The two statements that carry this file stand in other files. `rng_at`
(Johnson/AtFull/Shape/SitesAtHead.lean) states `hr` under `P5J.AtMgA` at every link below 25: under
that hypothesis the table of stretches is the written one, its places are the written 282
(Johnson/AtFull/Desc/SpotsWritten.lean), and at these Lean's kernel decides. `face_ok_site`
(Johnson/AtFull/Shape/FaceAtSites.lean) states that at every site of every public part the face
passes `Face.ok`.
Through
Honest/K3/Law/Thread/QuietAtLink.lean it also imports files under Honest/Thread/ (`keepsDigits_all`
names `lettersHead`, `kpBy`, `Script` and `WtF` of them).

Users. The first three theorems serve wherever a theorem of this folder takes `hr`. Two more
theorems take in its stead the closed test "rngWrittenB = true" (`rng_head_of`, `site_digits_of`:
Honest/K3/Law/Thread/RngHead.lean): where the two files named last may be imported, use this file;
where not, RngHead.lean with its hypothesis. The theorems that take a site (those on the digits over
Honest/K3/Law/Thread/DigitsHeardLink.lean; `keeps_at_link`, `keeps_thread`) gain that such a site
stands at all 25 links on the digits. Honest/K3/Good/MarksLooks.lean imports this file.

Limits. Public data alone, but for what the called theorems say. At the full size alone: `P5J.AtMgA`
speaks of no other. No instance of these hypotheses is exhibited in this file.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietAtLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsHeardLink
import Johnson.AtFull.Shape.SitesAtHead
import Johnson.AtFull.Shape.FaceAtSites

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain Place KindName Strs OpenedColumn)
open VerifiableInference.Desc.K3 (quietAt quietDigits)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open Johnson.Desc.First.Walk.Tied (StepYes)
open Johnson.AtFull.Shape (rng_at face_ok_site)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- At every link below 25, at either sort, the list `lookSites Zp` holds a site with that link and
that sort, at the library's written place, which stands in the written list of places. Conditional
on `P5J.AtMgA`. No instance of this hypothesis is exhibited in this file. -/
theorem site_at_all_fifty (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (d : Bool) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = d ∧ s.at_.place = IM.k3Place l d ∧
      s.at_.place ∈ P5J.At.ps :=
  site_there_head h l hl d fun _ => rng_at h l hl

/-- `digits_heard_link` without `hr`. Conditional on `P5J.AtMgA`. No instance of this hypothesis is
exhibited in this file. -/
theorem digits_heard_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = true ∧
      ∃ blk, cF.blocksInOrder[borderOf l true]? = some blk ∧ blk.place = IM.k3Place l true ∧
        ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
          blk.step ft sj rs c = .ok (sj', n) →
          ∃ tl g, sj'.tl? = some tl ∧ tl.heard = some g ∧
            OpenSame g (lookHeardAt s.shape 0 (rs.map (·.drawn))) ∧
            g.cEnd.ents.isEmpty = true ∧ g.leaves.start.ents.isEmpty = true ∧
            (Good.Ok rs → g.leaves.eps = one rs (firstRound s.at_.face .leaves)) :=
  digits_heard_link h l hl (rng_at h l hl)

/-- At every link below 25, at either sort, a site stands whose face passes the hearing's own test
on its numbers, `Face.ok`. Conditional on `P5J.AtMgA`. No instance of this hypothesis is exhibited
in this file. -/
theorem face_ok_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (d : Bool) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = d ∧ s.at_.face.ok = true := by
  obtain ⟨s, hs, e1, e2, _, _⟩ := site_at_all_fifty h l hl d
  exact ⟨s, hs, e1, e2, face_ok_site Zp s hs⟩

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- `keepsDigits_thread` without `hr`. Conditional on `P5J.AtMgA` and `hf`. No instance of these
hypotheses is exhibited in this file. -/
theorem keepsDigits_all (l : Nat) (hl : l < 24) (hf : f .K3 = k3KeepsAt Zp) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = true ∧
      ∃ used claims, quietAt Zp.p.X l true = some (quietDigits used claims) ∧
        ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.bs[
            borderOf l true]? = some blk →
          ∀ t t', StepYes (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.ft
            blk t t' → K3KeepsDigits s.shape claims t t' :=
  keepsDigits_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w l hl (rng_at h l (by omega)) hf

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.site_at_all_fifty
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_heard_all
#print axioms ProofFile.Honest.K3.Law.AtThr.keepsDigits_all
#print axioms ProofFile.Honest.K3.Law.AtThr.face_ok_all
