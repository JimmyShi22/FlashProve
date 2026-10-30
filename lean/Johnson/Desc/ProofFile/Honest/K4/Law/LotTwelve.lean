-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/LotTwelve.lean: CONDITIONAL: on h and hG.

What is here. UNDER THE LIBRARY's HYPOTHESIS ON THE PUBLIC FILES K4's LOT LAYS TWELVE HALVES, ONE AT
EACH OF K4's TWELVE PLACES. The lot (`k4HLot`, Honest/K4/Part.lean) is the entry of the feed-forward
layers' own rounds (the sub-protocol K4) in a filling of the honest prover; a half is the prover's
side for one member of the chain. Under h : AtMgA and hG : `ProofFile.blankBy ProofFile.pureRoad.links Zp` =
some G₀: (1) the places of the lot's halves are, up to their order, the library's `IM.k4Place g` at
g below 12: each half's place is one of these (`IM.k4_seated_scope`, Johnson/IMR/K4Seat.lean); at
each of these the lot has a half (`lot_half_head`, Law/HalfHead.lean, at `laid_head`,
Law/SeatedHead.lean, and the library's `atK4_full`, Johnson/Road/K4/K04Tied.lean); and no place
stands twice (`k4HLot_places_once`, Law/LotOnce.lean). (2) so the lot has twelve halves. What it is
for: the statements on all that the lot lays (Law/LotNoStrayOpen.lean, Law/LotOnce.lean) hold also
where it lays nothing: here they are shown not to speak of nothing. General in cells, weights and
look. Statements and proofs.

  `k4Places_once`   the twelve written places have no double.
  `k4HLot_place_iff`   a place is a half's just if it is one of the twelve.
  `k4HLot_places_perm`   **the halves' places are the twelve, up to their order.**
  `k4HLot_twelve`   **twelve halves.**

Not shown here. THAT h CAN HOLD: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). hG ASKS NOTHING BEYOND h: at h's opening the ground that is made
of the public part is there (`IM.Open.blank`). THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction` alone.
THE GROUND IS THE ONE THAT IS MADE OF THE PUBLIC PART (hG). Nothing on what a half sends. Beneath it
stand comparisons by Lean's own kernel: `k4Places_once` here (`decide`); `k4_nums_full`
(Law/SeatedHead.lean, `decide +kernel`), beneath `laid_head`; the library's `k4HereB_full`
(Johnson/Road/K4/K04Tied.lean, `decide +kernel`), beneath `atK4_full`; `k4_front_closed`
(Law/FrontClosed.lean, `decide +kernel`), beneath `k4Pub_head` (Law/FrontCount.lean); and the uses
of kernel_rfl that Law/TableFitsMember.lean's head names. What else of the kind stands beneath the
library's laws that are called is not counted. No independent checker that its writers know of has
replayed them. A LAW, NOT A
PART: no file that defines a part of the proof file's description may import this one. WHAT THIS
FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at every
module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose name
begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…: it
stopped at 36 modules under Johnson/Goal/ and at 5 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 41 is not counted: all the numbers are floors.

Kin. No twin is known to its writers. `k4HLot_side_at_kind` (Law/LotSideAtKind.lean) says (1)'s
second half by the kind of a member's place, not by a group's number; it calls `k4HLot_place_iff`.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfHead
import Johnson.Desc.ProofFile.Honest.K4.Law.LotOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4 (atK4_full)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4 laid_head)

/-- The twelve written places have no double. -/
theorem k4Places_once : ((List.range 12).map IM.k4Place).Nodup := by decide

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place} {W₀ Rc Tr X' : Type}

/-- CONDITIONAL: on h and hG. A place is a half's just if it is one of the twelve. -/
theorem k4HLot_place_iff (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard) (a : Place) :
    a ∈ ((k4HLot (Rc := Rc) (X := X') cells weights look).halves Zp G₀).map (·.place) ↔
      a ∈ (List.range 12).map IM.k4Place := by
  constructor
  · intro ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
    obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hz
    obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hQ, -⟩ := Option.filter_eq_some_iff.1 hQ'
    unfold k4PubOf at hQ
    obtain ⟨r0, -, rfl⟩ := Option.map_eq_some_iff.1 hQ
    obtain ⟨hg, el, ep, -⟩ := IM.k4_seated_scope h.scope h.reads h.laid.pub hG hx
    refine List.mem_map.2 ⟨x.2.g, List.mem_range.2 hg, ?_⟩
    show IM.k4Place x.2.g = (⟨1, some x.2.link, x.2.piece, .K4⟩ : Place)
    rw [el, ep]
  · intro ha
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
    obtain ⟨g', x, blk, Lh⟩ := laid_head h (atK4_full g (List.mem_range.1 hg))
    have eg : g' = g := by
      have e := Lh.num
      omega
    obtain ⟨G₁, hG₁, hx⟩ := Lh.lot
    have eG : G₁ = G₀ := Option.some.inj (hG₁.symm.trans hG)
    rw [eG] at hx
    have e := lot_half_head (Rc := Rc) (X' := X') h Lh cells weights look hx
    rw [eg] at e
    refine List.mem_map.2 ⟨_, List.mem_of_find?_eq_some e, ?_⟩
    have hp := List.find?_some e
    exact beq_iff_eq.1 hp

/-- CONDITIONAL: on h and hG. **THE HALVES' PLACES ARE THE TWELVE, UP TO THEIR ORDER.** -/
theorem k4HLot_places_perm (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard) :
    (((k4HLot (Rc := Rc) (X := X') cells weights look).halves Zp G₀).map (·.place)).Perm
      ((List.range 12).map IM.k4Place) :=
  (List.perm_ext_iff_of_nodup (k4HLot_places_once cells weights look Zp G₀) k4Places_once).2
    (k4HLot_place_iff h hG cells weights look)

/-- CONDITIONAL: on h and hG. **THE LOT LAYS TWELVE HALVES.** -/
theorem k4HLot_twelve (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard) :
    ((k4HLot (Rc := Rc) (X := X') cells weights look).halves Zp G₀).length = 12 := by
  have e := (k4HLot_places_perm (Rc := Rc) (X' := X') h hG cells weights look).length_eq
  rw [List.length_map, List.length_map, List.length_range] at e
  exact e

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Places_once
#print axioms ProofFile.Honest.K4.k4HLot_place_iff
#print axioms ProofFile.Honest.K4.k4HLot_places_perm
#print axioms ProofFile.Honest.K4.k4HLot_twelve
