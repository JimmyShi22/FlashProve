-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/PutFo.lean: the honest side of the kind "lookup" (K3):
behind the lookup on the calls at a layers' link the link's own field fo holds what was heard, and
its shape is the layout's: the sentence that the library asks of the state in front of the layers'
own kind (`K4Fence.heard`, Johnson/Road/K4/More/ElevenAtAll.lean), at the state behind the accepting
step of the lookup's member. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: fo and F are fields of the layers' link's own part of
the state (the arm lay of `Here`, Johnson/Desc/First/State.lean).

What is shown.
  `fo_of_here`: at a layers' link what the lookup's step has set stands in the link's own fields fo
    and F.
  `member_back_fo`: the same at the description's own member at a lookup of a public part.
  `hearVia_shape`: what the seated hearing hands back bears the shape that the parameters make.
  `fs_layers`: the shape that the plan itself holds for the lookup on the calls of a layers' link is
    the layout's.
  `heard_shape_layers`: whatever fo holds behind the member's accepting step has the layout's shape.
The library's own `heard_shape_lay` (Johnson/Desc/First/Look/K3HeardShape.lean) says the like of an
older text of the sub-protocol, not of the one that a description seats.

Hypotheses that remain.
  The member's accepting step (`h`), and the other hypotheses of `calls_here`
    (Honest/K3/Law/Thread/StateHere.lean): `O`, `hs`, `hd`, `hb`, `hbs`, `hm`, `hmp`, `hpk`.
  `h`: (in `fo_of_here`) `CallsHere`. `hp`, `hv`: (in `hearVia_shape`) the parameters make the shape
    h; the seated hearing returns.
  `hc`: (in `heard_shape_layers`) the site is a layers' link's.
  `hf`: (in `heard_shape_layers`) the public test "the shape is the one that the plan itself holds
    for it, field by field" (`shapeIsFs`, Honest/K3/LotPublic.lean) accepts.

How the proof goes. It calls `calls_here` (Honest/K3/Law/Thread/StateHere.lean) and `hearVia_back`
(Honest/K3/Law/Thread/K3Keeps.lean).

Users. `member_back_fo` is called in Honest/K3/Law/Thread/LookRest.lean,
Honest/K3/Law/Thread/LeavesReady.lean [not in this library], Honest/K3/Law/Thread/PadNamesOf.lean
[not in this library] and Honest/K3/Law/Thread/MergedPoint.lean; `fo_of_here` in
Honest/K3/Law/Thread/StandsAt.lean; `heard_shape_layers` in `heard_shape_link`
(Honest/K3/Law/Thread/AtLink.lean).

Limits. Conditional on the hypotheses above. The statements speak of the state right behind the
member's step: that no later member changes the field is not stated. At a link of another sort they
say nothing. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatedWorth
import Johnson.Desc.ProofFile.Honest.K3.LotPublic
import Johnson.Desc.First.Look.K3CallerAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork)
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (seatCalls)
open VerifiableInference.Desc.K3.Law (decideVia hearVia)
open VerifiableInference.Desc.First.Look (P placeAt lookAt lookAt_lay)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **At a layers' link what the lookup's step has set stands in the link's own fields**: fo holds
what was heard, F the ledger behind the hearing. Conditional on the three arms of `CallsHere`
(Honest/K3/Law/KeepsDefs.lean). -/
theorem fo_of_here {sj sj' : FS} {H : OnBytes.Model.Forest.Heard} {G : Fork}
    (h : CallsHere sj sj' H G) : ∀ al, sj'.here = .lay al → al.fo = some H ∧ al.F = G := by
  intro al hal
  rcases h with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ | ⟨a, _, _, rfl⟩
  · obtain rfl : _ = al := VerifiableInference.Desc.First.Here.lay.inj hal
    exact ⟨rfl, rfl⟩
  · exact nomatch hal
  · exact nomatch hal

/-- **At the description's own member at a lookup on the calls of a public part.** Conditional on
the hypotheses of `calls_here` (Honest/K3/Law/Thread/StateHere.lean). No instance of these
hypotheses is exhibited in this file. -/
theorem member_back_fo (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∃ F H G, sj.fork? = some F ∧ hearVia s.p F rs = some (H, G) ∧
      ∀ al, sj'.here = .lay al → al.fo = some H ∧ al.F = G := by
  obtain ⟨F, H, G, a1, _, a3, a4, _⟩ := calls_here o pol lay KL Fd Z Bs base ch A B O s hs hd lot m
    hb hbs hm hmp hpk ft sj sj' n rs c h
  exact ⟨F, H, G, a1, a3, fo_of_here a4⟩

/-- **What the seated hearing hands back bears the shape that the parameters make.** Conditional on
both returns. -/
theorem hearVia_shape {p : P} {h : Shape} {F G : Fork} {rs : List Fmt.RoundView}
    {H : OnBytes.Model.Forest.Heard} (hp : p.shape = some h)
    (hv : hearVia p F rs = some (H, G)) : H.shape = h := by
  obtain ⟨_, _, hH⟩ := hearVia_back hp hv
  exact (toHeard_fields hH).1

/-- **The shape that the plan itself holds for the lookup on the calls of a layers' link is the
layout's.** Conditional on the site, its sort and its caller. -/
theorem fs_layers (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hc : s.caller = .layers) : fsOf Z.p.X s = some Z.p.X.y.fo := by
  unfold lookSites at hs
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, _, f3, f4, _, _, f7, _⟩ := site_facts _ _ x s hsx
  rw [← f3, ← f4, hd] at f1
  rw [← f3] at f7
  unfold placeAt at f1
  obtain ⟨y, hy, _⟩ := Option.map_eq_some_iff.1 f1
  have hcal : (callerOf Z.p.X.p4 Z.p.X.NGr s.link).1 = .layers := f7.symm.trans hc
  unfold callerOf at hcal
  dsimp only at hcal
  by_cases h1 : (s.link == (if Z.p.X.p4 then 2 else 1) * Z.p.X.NGr) = true
  · rw [if_pos h1] at hcal
    exact nomatch hcal
  · rw [if_neg h1] at hcal
    by_cases h2 : (s.link % (if Z.p.X.p4 then 2 else 1) == 0) = true
    · obtain ⟨_, _, _, e, _⟩ := lookAt_lay hy (by simpa using h1) (by simpa using h2)
      unfold fsOf
      rw [hd, hy, Option.map_some, e]
    · rw [if_neg h2] at hcal
      exact nomatch hcal

/-- **Whatever fo holds behind the member's accepting step has the layout's shape.** Conditional on
the hypotheses of `member_back_fo`; the site is a layers' link's; the public test "the shape is the
one that the plan itself holds for it, field by field" accepts. No instance of these hypotheses is
exhibited in this file. -/
theorem heard_shape_layers (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (hc : s.caller = .layers)
    (hf : shapeIsFs Z.p.X s = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∀ al fo', sj'.here = .lay al → al.fo = some fo' → fo'.shape = Z.p.X.y.fo := by
  intro al fo' hal hfo
  obtain ⟨F, H, G, _, hv, hput⟩ := member_back_fo o pol lay KL Fd Z Bs base ch A B O s hs hd lot m
    hb hbs hm hmp hpk ft sj sj' n rs c h
  obtain rfl : H = fo' := Option.some.inj ((hput al hal).1.symm.trans hfo)
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, f2, _⟩ := site_facts _ _ x s hsx
  rw [hearVia_shape f2 hv]
  exact Option.some.inj ((shapeIsFs_holds _ s hf).symm.trans (fs_layers Z s hs hd hc))

#print axioms ProofFile.Honest.K3.Law.AtThr.fo_of_here
#print axioms ProofFile.Honest.K3.Law.AtThr.member_back_fo
#print axioms ProofFile.Honest.K3.Law.AtThr.hearVia_shape
#print axioms ProofFile.Honest.K3.Law.AtThr.fs_layers
#print axioms ProofFile.Honest.K3.Law.AtThr.heard_shape_layers

end ProofFile.Honest.K3.Law.AtThr
