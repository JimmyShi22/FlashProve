-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SessionStopsFit.lean: the premise StopsFit of hidSmall_of_held
(Johnson/FrontRoad/SessionStopsOfHeld.lean), at the prover provG and the data dataZ Z, from public
conditions and conditions on the rows.
Terms of this folder: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
stopsFit_provG. Four public conditions: Z is in scope; the library's reader of the public files
returns its table pp of scales and policy at Z; the IOP's own test on the public files, protocolDataWellFormed,
accepts Z's public head; LaidAt holds at Zp, Np, cF. Two conditions on the rows G: one call of ready
at provG returns (hR); no row of G's first chain is at a place of the kind frame, the kind of the
sealing sub-protocol that ends the first chain (hn). Then the first chain of descZ Zp Np cF is some
list pre followed by one last member e, and pre is not empty. And StopsFit holds at descZ Zp Np cF,
provG, dataZ Z, pre and e.
stopsFit_of_rows: the same with hR replaced. In its place stand three things. The condition Owed at
G.mute, the rows with each row's parameters A and B set to «never», at any relation Rel; the field
rows of PremWDebts (E2E/BridgeDebts.lean) is this condition at the relation relAt … (RyesZ Z)
instanceAsPlainRecord. One input of Rel. And one list of challenges that the rounds can draw and at which the
prover does not abort at that input, by either of its two tests.
  ready_of_rows   under these three, ready at provG succeeds at that input, at every value of the
      coins.
  atPlanOk_of_laid   under the four public conditions the named tests on the plan (P5J.At.PlanOk,
      Johnson/P5J/PlanOk.lean) hold at the given Zp, Np, cF.
  noFrame_provG   the condition hn on G's rows gives the condition of stopsFit_head on the halves of
      provG; by first_provG the two have the same places.

How it fits. One call of stopsFit_head_exists (Johnson/Desc/ProofFile/Honest/Law/StopsHead.lean),
which ends at P5J.F0T o Zp Np cF and a data value D, under the premises P5J.AtMg. descZ Zp Np cF is
P5J.F0T OnBytes.secondHashFunction Zp Np cF by definition. dataZ Z is that D by data_atFiles
(E2E/BridgePaidAtFiles.lean), where protocolDataWellFormed accepts. P5J.AtMg comes from AtMg.of_olderK
(Johnson/P5J/AtMg.lean) and atPlanOk_of_laid, which is two calls: nine_of_laid
(Johnson/Goal/Skeleton/CondsOfLaid.lean), with owed_of_live (Johnson/Goal/Skeleton/OwedOfLive.lean),
and At.PlanOk.of_tests' (Johnson/P5J/GroupsPaid.lean). The list of verifier messages that
stopsFit_head_exists takes as an argument is any one: its type always has a member. ready_of_rows
reads the field runs of Owed (Johnson/Desc/ProofFile/Honest/Owed.lean): the run that it gives begins
with ready (runC, Johnson/Desc/ProofFile/Honest/Walk.lean), and the prover at G.mute is the prover
at G (prover_mute, Johnson/Desc/ProofFile/Honest/Law/Rule/Mute.lean). Owed is the frame's as it now
stands; this proof spends its field runs alone, and of runC the first bind alone. A lemma toward the
condition HidSmall (E2E/BridgePrivacy.lean); not one of the release's goal statements.

Limits.
  StopsFit is a list of tests with code and equalities between lengths. It does not measure how
      often a prover aborts. No probability is named, and nothing is said on hiding.
  The four public conditions are fields of PremWDebts or, for the reader's table, a premise of
      Spec.roadPrivate_of_debts (Johnson/FrontRoad/FromDebtsSpec.lean). Against these and the field
      rows, stopsFit_of_rows asks three things more. The first is hn. The second is that the
      relation holds of some input. The third is that at that input there is at least one list of
      challenges that the rounds can draw at which the prover does not abort. None is proved here of
      any rows or prover.
  The third asks more than ready needs. ready reads no list of challenges; the list is asked only
      because the field runs of Owed gives a whole run outside the set where the prover aborts, not
      ready alone. Where the prover aborts at every list, stopsFit_of_rows says nothing, and
      stopsFit_provG still applies if ready succeeds. By ready_any
      (Johnson/Desc/ProofFile/Honest/Law/ReadyAny.lean) one success of ready, at one input in range
      with a trace, gives success at every such input and every value of the coins.
  hn has the form of the conclusion of wider_no_frame
      (Johnson/Desc/ProofFile/Honest/Thread/FirstFill.lean, by the head of StopsHead.lean). That
      file is not among this file's imports, and the call is not made here.
  The list pre is only said to exist, while hidSmall_of_held states its premise on the first chain
      at pre₁. By the cut, pre is the first chain's list without its last member, (descZ Zp Np
      cF).first.blocksInOrder.dropLast, so a statement that joins the two can name it.
  At the library's full-size parameter set alone (P5J.AtMg, P5J.At.PlanOk).
-/
import Johnson.FrontRoad.SessionHid
import Johnson.Desc.ProofFile.Honest.Law.StopsHead
import E2E.BridgePaidAtFiles
import Johnson.Goal.Skeleton.CondsOfLaid
import Johnson.Goal.Skeleton.OwedOfLive
import Johnson.P5J.GroupsPaid
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run (ckP)
open VerifiableInference.Desc (KindName)
open ProofFile.Honest (Prover ProverCoinCounts Sides StopsFit Ready Coins ready stopsFit_head_exists Owed Draws
  silentAt runC prover_mute)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_fit : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_fit {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- If no row of G's first chain stands at a place of the kind frame, no half of provG's first chain
does. -/
theorem noFrame_provG (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame) :
    ∀ g ∈ (provG Z Zp Np cF B G H).first, g.place.kind ≠ KindName.frame := by
  intro g hg
  rw [first_provG] at hg
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hg
  exact hn L hL

/-- The named tests on the plan hold at the given Zp, Np, cF, where Z is in scope, the library's
reader returns its table at Z, protocolDataWellFormed accepts Z's public head, and LaidAt holds. -/
theorem atPlanOk_of_laid (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    At.PlanOk OnBytes.secondHashFunction Zp Np cF Z.lay :=
  have ⟨t1, t2, t3, t4, t5⟩ := (nine_of_laid scope live hr L (owed_of_live live).rows).1
  At.PlanOk.of_tests' scope hr L t1 t2 t3 t4 t5

/-- **StopsFit at provG and dataZ Z**, from public conditions, one return of ready, and the
condition that no row of G's first chain stands at a place of the kind frame. -/
theorem stopsFit_provG (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x : ProofFile.Inst}
    {k : Coins B} {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame) :
    ∃ pre e, (descZ Zp Np cF).first.blocksInOrder = pre ++ [e] ∧ pre ≠ [] ∧
      StopsFit (descZ Zp Np cF) (provG Z Zp Np cF B G H) (dataZ Z) pre e := by
  obtain rfl := data_atFiles Z Zp Np cF scope live L
  obtain ⟨ρ⟩ : Nonempty (Iop.Rho (chainsOf (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
    (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty).sh) := inferInstance
  exact stopsFit_head_exists (front₀ (dataAtFiles flashProveData Z).G.z₀.2) (join₀ (dataAtFiles flashProveData Z).G.z₀.2)
    ByteArray.empty (AtMg.of_olderK scope hr L (atPlanOk_of_laid Z Zp Np cF scope live hr L)) scope
      hR
    ρ (noFrame_provG Z Zp Np cF B G H hn)

/-- **ready succeeds at provG, from the condition Owed at G.mute** (the rows with each row's
parameters A and B set to «never»), at one input of its relation and one list of challenges that the
rounds can draw and at which the prover does not abort. -/
theorem ready_of_rows {Rel : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → ProofFile.Inst → Prop}
    (rows : Owed (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) G.mute Rel)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x : ProofFile.Inst} (hrel : Rel w₀ rc x) (k : Coins B) (ρ : Draws)
    (hd : ρ.due (descZ Zp Np cF) = true)
    (hs : silentAt (descZ Zp Np cF) (provG Z Zp Np cF B G H) w₀ rc x ρ = none) :
    ∃ R, ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k = .ok R := by
  have e : G.mute.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) = provG Z Zp Np cF B G H :=
    prover_mute G _
  obtain ⟨r, hr'⟩ := rows.runs w₀ rc x hrel k ρ hd (e.symm ▸ hs)
  have hr : runC (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k ρ = .ok r := e ▸ hr'
  cases h : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k with
  | ok R => exact ⟨R, rfl⟩
  | error e =>
    exfalso
    unfold runC at hr
    rw [h] at hr
    cases hr

/-- **StopsFit at provG and dataZ Z, with hR replaced**: by the condition Owed at G.mute, one input
of its relation, and one list of challenges that the rounds can draw and at which the prover does
not abort; with the public conditions and hn of stopsFit_provG. -/
theorem stopsFit_of_rows (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {Rel : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → ProofFile.Inst → Prop}
    (rows : Owed (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) G.mute Rel)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x : ProofFile.Inst} (hrel : Rel w₀ rc x) (k : Coins B) (ρ : Draws)
    (hd : ρ.due (descZ Zp Np cF) = true)
    (hs : silentAt (descZ Zp Np cF) (provG Z Zp Np cF B G H) w₀ rc x ρ = none)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame) :
    ∃ pre e, (descZ Zp Np cF).first.blocksInOrder = pre ++ [e] ∧ pre ≠ [] ∧
      StopsFit (descZ Zp Np cF) (provG Z Zp Np cF B G H) (dataZ Z) pre e := by
  obtain ⟨R, hR⟩ := ready_of_rows Z Zp Np cF B G H rows hrel k ρ hd hs
  exact stopsFit_provG Z Zp Np cF B G H scope hr live L hR hn

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_fit
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_fit
#print axioms OnBytes.FrontRoad.noFrame_provG
#print axioms OnBytes.FrontRoad.atPlanOk_of_laid
#print axioms OnBytes.FrontRoad.stopsFit_provG
#print axioms OnBytes.FrontRoad.ready_of_rows
#print axioms OnBytes.FrontRoad.stopsFit_of_rows
