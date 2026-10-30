-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09LeftD.lean: THE LOOKUPS' PROMISE ON THE STATE (`K3LeftOn`,
Johnson/Top/H/K3LeftStatement.lean), AT BOTH LOOKUP SEATS, AT THE CLOSED CONSTANT's LETTERS, IN
FRONT OF EVERY LINK's BATCHING; AT THE DIGITS' SEAT AT THE PLAN's OWN SHAPE. Two theorems: joins of
other files' lemmas.
  `leftD_at`: **the digits' seat: `K3LeftOn S.fork? heardDig tlD.f9 lm first _ a.1` for some first,
    tlD the structure that `digAt` lays.** By `front_at_mg` (K09Aready.lean), `leftOn_digits_front`,
    `leftOn_digits_head` (KxAtFront.lean), `IM.Open.W`, `shape_of_dig`
    (Johnson/LPFE1R/ShapeOfDig.lean). lm is general here.
  `leftC_at`: the calls' seat: `k3LeftOnItemAt (At.X Zp) m a.1`: `leftOn_at_front` (KxOfTable.lean)
    at the constant's letters.
PREMISES. The head; m < 25; for the first: what `digAt` returns; the condition in front of the
batching.
Limits. `leftD_at` ends in "there is a first", at the condition `fun _ => True`: it pins neither.
`leftC_at` is read back out of the table's promise, which stands in the condition in front: it shows
nothing of that promise. `digAt` is `K3Asks.digAt` here; `First.Look.digAt` is a second constant
with the same text. Nothing on soundness.

-/
import Johnson.P5J.K09Aready
import Johnson.LPFE1R.ShapeOfDig

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Stages (LinkH)
open OnBytes.PscRun (Sized)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes attShapes nScores)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Link Chain)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K9Asks (funs_layers funs_att funs_head)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.LinkJoin (batchAt onTR frontAt kx_of_table ledger_at_front
  part_at_batch_all K9Closed K9OwnL K9OwnA K9OwnH PosPlan OkCoreLess core_layers_front
  core_att_front core_head_front NumbersOk hmS_at digHeard_of_leftOn leftOn_digits_front
  leftOn_digits_head ledgerB_of_sized merge_clause_347 entsMerge_at_347 OkCore OkLayers OkAtt
  OkHead pi8)
open Johnson.Desc.First.Walk.Tied (Reach)
open _root_.Desc.K14.Law (seatZ secondAt)

open VerifiableInference.Desc.LinkJoin (heardDig shape_of_dig leftOn_at_front)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **THE DIGITS' SEAT, AT THE PLAN's OWN SHAPE.** -/
theorem leftD_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.K3Asks.digAt (At.X Zp) m = some (xx, tlD)) (z : ProofFile.InstPub)
    (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps m) a) (lm : ℕ) :
    ∃ first, K3LeftOn S.fork? heardDig tlD.f9 lm first (fun _ => True) a.1 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hp, hr, -, hB, -⟩ := front_at_mg h O hm z a ho
  by_cases h24 : m = 24
  · subst h24
    have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 347 (z, a.1) := hr
    obtain ⟨P', hh, e1, e2, -, L⟩ := leftOn_digits_head h.scope h.reads O hp hr' hB lm
    rw [O.W] at e1
    obtain rfl := shape_of_dig hd P' hh e1 e2
    exact ⟨_, L⟩
  · have e : VerifiableInference.Desc.LinkJoin.frontAt m = 14 * m + 9 := by
      unfold VerifiableInference.Desc.LinkJoin.frontAt
      rw [if_neg h24]
    rw [e] at hr
    obtain ⟨P', hh, e1, e2, -, L⟩ := leftOn_digits_front h.scope h.reads O hp
      (by omega : m < 24) hr hB lm
    rw [O.W] at e1
    obtain rfl := shape_of_dig hd P' hh e1 e2
    exact ⟨_, L⟩

/-- **THE CALLS' SEAT.** -/
theorem leftC_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    (z : ProofFile.InstPub) (a : S × (FrK).E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
      (batchAt fullLinks At.ps m) a) : k3LeftOnItemAt (At.X Zp) m a.1 := by
  have ha := ho.1
  rw [batchIsFront hm] at ha
  exact leftOn_at_front h.𝔇 h.𝔇.N z hm a ha

end P5J

#print axioms P5J.leftD_at
#print axioms P5J.leftC_at
