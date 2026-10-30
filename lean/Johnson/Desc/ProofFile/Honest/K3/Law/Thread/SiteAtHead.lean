-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/SiteAtHead.lean: the kind "lookup" (K3): the structure
`SiteAt` (Honest/K3/Law/Thread/SiteThr.lean) at the letters `lettersHead`
(Honest/Thread/FirstHead.lean) under the library's hypothesis `P5J.AtMgA`, at a site's own border.
It is a file of its own, so that a caller that wants the structure alone imports no theorem on the
riders or on the form behind. One theorem.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `siteAt_lettersHead`: the structure `SiteAt`, with the description's return at the same values: a
    call of `siteAt_lettersAt` (Honest/K3/Law/Thread/SiteAtLetters.lean).

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hsite`: s is a site of the public part (`lookSites Zp`).
  `R`: `SiteRest` (Honest/K3/Law/Thread/SiteAtLetters.lean) at the prover's own halves: a
    sub-protocol of the lookups' lot stands at the site's place (inLot, lotPlace); the prover's list
    of halves holds the lookup's seated row there (half); four tests with code on public data (fits,
    ok, shapeIs, usedIs).
The letter for "keeps" by place, Kp, is a variable: nothing here reads it.

Imported. Files under Honest/Thread/.

Users. `playsAt_headRest` (Honest/K3/Law/Thread/PlaysAtHeadRest.lean [not in this library]),
Honest/K3/Law/Thread/K3KeepsForms.lean [not in this library] and
Honest/K3/Law/Thread/LeftAtCalls.lean call `siteAt_lettersHead`.

Limits. At the full size alone. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.Desc.ProofFile.Honest.Thread.Riders
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtLetters

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

/-- **`SiteAt` at the letters `lettersHead` under `P5J.AtMgA`**, with the description's return at
the same values. -/
theorem siteAt_lettersHead (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (R : SiteRest Zp cF H.first s lot J wit) :
    ∃ o pol lay KL Fd Bs base A B, IM.Open o pol lay KL Fd Zp Bs base cF A B ∧
      SiteAt (LH) (borderOf s.link s.digits) Zp Bs cF s lot J wit h.𝔇.sent h.𝔇.l3 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨_, hS⟩ : ∃ Bs', SiteAt (LH) (borderOf s.link s.digits) Zp Bs' cF s lot J wit h.𝔇.sent
      h.𝔇.l3 := siteAt_lettersAt h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite lot J wit R
  exact ⟨_, _, _, _, _, Bs, base, _, _, O, { hS with inLot := R.inLot }⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.siteAt_lettersHead
