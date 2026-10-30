-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/QuietAtLink.lean: the kind "lookup" (K3): under the
library's hypothesis `P5J.AtMgA` the equation on `quietAt` (Johnson/Desc/First/Look/K3Whole.lean) is
shown at the digits of all 24 links that are not the head's: what stands behind the lookup there
without a round is `quietDigits` at the plan's own two numbers. Theorems, by composition; no
definition, no new argument.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `quiet_layers_head`, `quiet_attention_head`: the equation at link 2 g and at link 2 g + 1, for g <
    12, with the plan by name.
  `quiet_digits_head`: the equation at a link's number below 24.
  `carries_digits_link24`: `carries_digits_link` (Honest/K3/Law/Thread/AtLink.lean) without its
    hypothesis `hq`.
  `keepsDigits_of_keeps`: for a caller that assumes "keeps": at the letters `lettersHead`
    (Honest/Thread/FirstHead.lean), with "keeps" by the place's kind (`kpBy`,
    Honest/Thread/KeepsBy.lean): from the thread's own keeps at the border to the sort's own clause
    `K3KeepsDigits` (Honest/K3/Law/KeepsDefs.lean).
  `keepsDigits_thread`: the same from the member's accepting step, at a link's number.
The two numbers stand under "there are", with their equation beside them; a caller that wants them
by name takes the first two theorems.

Why. `k3KeepsAt` (Honest/K3/Law/Thread/K3KeepsAt.lean) holds the sort's own clause at the digits
only under that equation: a caller had to supply it. At the 24 links it is shown here.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hs`: the site; or `hr`, under which `site_there_head` (Honest/K3/Law/Thread/SiteThereHead.lean)
    gives one: `rngIn` returns a number at the link. (`rng_at`,
    Johnson/AtFull/Shape/SitesAtHead.lean, a file that is not imported here, states `hr` under
    `P5J.AtMgA` at every
    link below 25; so does `rng_head_paid`, Honest/K3/Law/Thread/RngWrittenHolds.lean.)
  `hg`, `hl`, `hd`: the group's number is below 12; the link's number is below 24; the site is on
    the digits.
  `hf`: the letter f at the kind K3 is the lookups' clause `k3KeepsAt Zp`.

How the proof goes. The library has the equation (`Meaning.K8.quietAt_layers`, `quietAt_attention`,
Johnson/Meaning/PlanClaims.lean) from three public facts. Under `P5J.AtMgA` these hold: attention is
covered, there are twelve groups, and each has its attention plan (`H2K5.Door.scope_all`,
Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean); each has its layers' plan (`IM.Own.built_link`,
Johnson/IMR/NamedOfHeld.lean, with `linksOf_size`, OnBytes/Tie/Pv/Keeps/LinksOrder.lean).

Imported, through Honest/K3/Law/Thread/KeepsThread.lean. Files under Honest/Thread/.

Users. Honest/K3/Law/Thread/SiteAllFifty.lean imports this file.

Limits. At the full size alone, since `P5J.AtMgA` is. The head's own link (24) is not treated: there
`quietAt` is `quietHead`. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.KeepsThread
import Johnson.Meaning.PlanClaims
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.IMR.NamedOfHeld
import OnBytes.Tie.Pv.Keeps.LinksOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs)
open VerifiableInference.Desc.K3 (quietAt quietDigits)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
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

/-! ## 1 The equation -/

include h in
/-- **At a layers' link.** Conditional on `P5J.AtMgA` and g < 12. -/
theorem quiet_layers_head (g : Nat) (hg : g < 12) :
    ∃ hp, Zp.p.X.G[g]? = some hp ∧
      quietAt Zp.p.X (2 * g) true = some (quietDigits hp.used hp.nLin) := by
  obtain ⟨p4, ng, -⟩ := H2K5.Door.scope_all h
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨ls0, hls, -⟩ := IM.Own.built_link O.pub
  have hs : Zp.p.X.G.size = 12 := (OnBytes.L5.LinksOrder.linksOf_size hls).1.trans ng
  have hG : Zp.p.X.G[g]? = some Zp.p.X.G[g] := Array.getElem?_eq_getElem (by omega)
  exact ⟨_, hG, Meaning.K8.quietAt_layers p4 (by rw [ng]; omega) hG⟩

include h in
/-- **At an attention link.** Conditional on `P5J.AtMgA` and g < 12. -/
theorem quiet_attention_head (g : Nat) (hg : g < 12) :
    ∃ a, Zp.p.X.A[g]? = some a ∧
      quietAt Zp.p.X (2 * g + 1) true = some (quietDigits a.nMsg a.nLin) := by
  obtain ⟨p4, -, hAll⟩ := H2K5.Door.scope_all h
  obtain ⟨a, hA⟩ := hAll g hg
  exact ⟨a, hA, Meaning.K8.quietAt_attention p4 hA⟩

include h in
/-- **At a link's number below 24.** Conditional on `P5J.AtMgA`. -/
theorem quiet_digits_head (l : Nat) (hl : l < 24) :
    ∃ used claims, quietAt Zp.p.X l true = some (quietDigits used claims) := by
  by_cases he : l % 2 = 0
  · have ej : 2 * (l / 2) = l := by omega
    obtain ⟨hp, -, e⟩ := quiet_layers_head h (l / 2) (by omega)
    rw [ej] at e
    exact ⟨_, _, e⟩
  · have ej : 2 * (l / 2) + 1 = l := by omega
    obtain ⟨a, -, e⟩ := quiet_attention_head h (l / 2) (by omega)
    rw [ej] at e
    exact ⟨_, _, e⟩

/-! ## 2 `Carries` at the digits without hq -/

include h in
/-- **`carries_digits_link` without `hq`, at the 24 links.** Conditional on `P5J.AtMgA` and the
site. No instance of these hypotheses is exhibited in this file. -/
theorem carries_digits_link24 (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link < 24)
    (hd : s.digits = true) :
    ∃ used claims, quietAt Zp.p.X s.link true = some (quietDigits used claims) ∧
      ∀ (ft : Nat) (g : Nat → ChainSh → Except String ChainSh)
        (vals : Nat → TS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g (borderOf s.link true) = digitsG s.shape s.p.first used claims →
        Carries cF.blocksInOrder ft ⟨ChainSh, chainSh, g, vals⟩ (borderOf s.link true) := by
  obtain ⟨used, claims, hq⟩ := quiet_digits_head h s.link hl
  exact ⟨used, claims, hq, fun ft g vals hg =>
    carries_digits_link h s hs (by omega) hd used claims hq ft g vals hg⟩

/-! ## 3 The sort's own clause of "keeps" -/

/-- **From the thread's own keeps to the sort's own clause.** Conditional on `P5J.AtMgA`, the site
and `hf`. No instance of these hypotheses is exhibited in this file. -/
theorem keepsDigits_of_keeps (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link < 24)
    (hd : s.digits = true) (hf : f .K3 = k3KeepsAt Zp) :
    ∃ used claims, quietAt Zp.p.X s.link true = some (quietDigits used claims) ∧
      ∀ t t', (LK).thread.keeps (borderOf s.link true) t t' → K3KeepsDigits s.shape claims t t'
    := by
  obtain ⟨used, claims, hq⟩ := quiet_digits_head h s.link hl
  refine ⟨used, claims, hq, fun t t' hk => ?_⟩
  obtain ⟨blk, hblk, hp⟩ :=
    member_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w s.link (by omega) true
  have hkind : blk.place.kind = KindName.K3 := by rw [hp]
  have h1 := (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hblk hkind t t').1 hk
  have hpl : s.at_.place = IM.k3Place s.link true := by
    have e := site_place_head h s hs
    rw [hd] at e
    exact e
  rw [hf, hp, ← hpl] at h1
  exact k3KeepsAt_digits h1 hs hd hq

/-- **The same from the member's accepting step, at a link's number.** Conditional on `P5J.AtMgA`,
`hr` and `hf`. No instance of these hypotheses is exhibited in this file. -/
theorem keepsDigits_thread (l : Nat) (hl : l < 24)
    (hr : (rngIn ((spotsOf Zp.cuts).getD []) l).isSome = true) (hf : f .K3 = k3KeepsAt Zp) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = true ∧
      ∃ used claims, quietAt Zp.p.X l true = some (quietDigits used claims) ∧
        ∀ blk, (LK).thread.bs[borderOf l true]? = some blk →
          ∀ t t', StepYes (LK).thread.ft blk t t' → K3KeepsDigits s.shape claims t t' := by
  obtain ⟨s, hs, rfl, e2, -, -⟩ := site_there_head h l (by omega) true (fun _ => hr)
  obtain ⟨used, claims, hq, hK⟩ :=
    keepsDigits_of_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd f w s hs hl e2 hf
  exact ⟨s, hs, rfl, e2, used, claims, hq, fun blk hblk t t' hy =>
    hK t t' (keeps_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w s.link (by omega) true hf blk
      hblk t t' hy)⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.quiet_layers_head
#print axioms ProofFile.Honest.K3.Law.AtThr.quiet_attention_head
#print axioms ProofFile.Honest.K3.Law.AtThr.quiet_digits_head
#print axioms ProofFile.Honest.K3.Law.AtThr.carries_digits_link24
#print axioms ProofFile.Honest.K3.Law.AtThr.keepsDigits_of_keeps
#print axioms ProofFile.Honest.K3.Law.AtThr.keepsDigits_thread
