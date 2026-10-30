-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/KeepsThread.lean: the lookups' clause of "keeps" at the
thread of `lettersHead` (Honest/Thread/FirstHead.lean), which is stated under the library's
hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean); the theorem ends in the thread's field keeps, at
all fifty borders in front of a lookup. Theorems: each is a composition of earlier ones; no
definition.

Terms. Honest/K3/GLOSSARY.md ("keeps"). In this file: `borderOf l d`
(Johnson/Desc/Sound/MgAt/K3Open.lean) is the number of the border in front of link l's lookup, and
`IM.k3Place l d` (Johnson/IMR/K3Seat.lean) is that lookup's place; the sort d is true for the lookup
on the digits. An accepting step is `StepYes` (Johnson/Top/H0/Walk/Reach.lean).

What is shown.
  `memberAt_thread`: the structure `K3MemberAt` (Honest/K3/Law/Thread/K3KeepsStep.lean) at the
    thread of `lettersHead`, at the border `borderOf l d` of a link below 25 and either sort. It
    comes from `lot_at_link` (Honest/K3/Law/Thread/AtLink.lean); the thread's list is the first
    chain's blocksInOrder list by unfolding.
  `keeps_thread`: behind an accepting step of the thread's member at that border the thread's keeps
    holds: by `k3KeepsAt_stepYes` (K3KeepsStep.lean) at that structure, then `head_keeps_kind`
    (Honest/Thread/KeepsBy.lean).
  `member_thread`: a member stands at that border of the thread's list. So "whatever member stands
    there" in `keeps_thread` speaks of a member at each of the fifty borders. Whether the clause
    says anything of the two states there is another question: see below.

In which form. `keeps_thread` ends in the field keeps of the thread (`Thread.keeps`,
Honest/Thread/Thr.lean), which the thread's rule reads; `head_keeps_kind` ends in the letters' own
keeps; `Letters.thread` (Honest/Thread/First.lean) gives the one as the other: Lean takes them as
one by unfolding.

What `keeps_thread` says, in two steps. Where no site stands at the place the lookups' clause is
empty: not even "no mark behind" is said. Where a site stands: no mark behind, outright; on the
calls the sort's own clause outright; on the digits the sort's own clause only under the public
equation on `quietAt` that `k3ClauseAt` names (Honest/K3/Law/Thread/K3KeepsAt.lean). That a site
stands: on the calls by `site_calls_head`; on the digits by `site_there_head` under its hypothesis
hr: `rngIn` (Honest/K3/Lot.lean) returns a number at the link (both
Honest/K3/Law/Thread/SiteThereHead.lean). `rng_at` (Johnson/AtFull/Shape/SitesAtHead.lean, a file
that is not imported here) states hr under `P5J.AtMgA` at every link below 25; so does
`rng_head_paid`
(Honest/K3/Law/Thread/RngWrittenHolds.lean).

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA`.
  `hl`: the link's number is below 25.
  `hf`: (in `keeps_thread`) the thread's letter for "keeps" is `kpBy f`, and f at the kind K3 is the
    lookups' clause `k3KeepsAt Zp`.

Imported: Honest/Thread/FirstHead.lean, Honest/Thread/KeepsBy.lean, Honest/Thread/Thr.lean and
Honest/Thread/First.lean.

Users. `memberAt_thread` is called in Honest/K3/Law/Thread/HeadDigitsAtLink.lean and
Honest/K3/Law/Thread/LaysNextLight.lean; `keeps_thread` and `member_thread` in
Honest/K3/Law/Thread/QuietAtLink.lean.

Limits. At the full size alone: that limit comes with `P5J.AtMgA`. No statement of this file shows
that the thread holds at any run. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLinkThere
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3KeepsStep
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open Johnson.Desc.First.Walk.Tied (StepYes)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF head_keeps_kind)

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

/-- **The structure `K3MemberAt` at the thread of `lettersHead`**, at the border in front of the
lookup of a link below 25 and either sort. Conditional on `P5J.AtMgA`. No instance of these
hypotheses is exhibited in this file. -/
theorem memberAt_thread (l : Nat) (hl : l < 25) (d : Bool) :
    ∃ (Fd : FileDescription Inst) (Bs : PureBase) (base : List (Block TS ProofFile.Cl)) (A : SharedSeat)
      (B : SecondSeat) (lot : Block TS ProofFile.Cl),
      IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL Fd Zp Bs base cF A B ∧
      lot.place = IM.k3Place l d ∧ K3MemberAt (LK).thread (borderOf l d) Zp Bs cF lot := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hp, hm⟩ := lot_at_link h l hl d
  exact ⟨Fd, Bs, base, A, B, lot, O, hp, ⟨hb, fun blk hk => (hm blk hk).1,
    fun blk hk => (hm blk hk).2.1, fun blk hk => (hm blk hk).2.2⟩⟩

/-- **Behind an accepting step of the thread's member at a lookup's border the thread's keeps
holds**, at all fifty borders. Conditional on `P5J.AtMgA`, and on f at the kind K3 being the
lookups' clause. Where no site stands at the place that clause is empty. No instance of these
hypotheses is exhibited in this file. -/
theorem keeps_thread (l : Nat) (hl : l < 25) (d : Bool) (hf : f .K3 = k3KeepsAt Zp) :
    ∀ blk, (LK).thread.bs[borderOf l d]? = some blk →
      ∀ t t', StepYes (LK).thread.ft blk t t' → (LK).thread.keeps (borderOf l d) t t' := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hp, hM⟩ :=
    memberAt_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w l hl d
  intro blk hblk t t' hy
  have hk : blk.place.kind = KindName.K3 := by rw [hM.place blk hblk, hp]
  have h1 := k3KeepsAt_stepYes (LK).thread _ _ _ _ Fd base A B O hM blk hblk t t' hy
  refine (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hblk hk t t').2 ?_
  rw [hf]
  exact h1

/-- A member stands at that border of the thread's list, at the place `IM.k3Place l d`. Conditional
on `P5J.AtMgA`. -/
theorem member_thread (l : Nat) (hl : l < 25) (d : Bool) :
    ∃ blk, (LK).thread.bs[borderOf l d]? = some blk ∧ blk.place = IM.k3Place l d :=
  member_at_link h l hl d

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.member_thread
#print axioms ProofFile.Honest.K3.Law.AtThr.memberAt_thread
#print axioms ProofFile.Honest.K3.Law.AtThr.keeps_thread
