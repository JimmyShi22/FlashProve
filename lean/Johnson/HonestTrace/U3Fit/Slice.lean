-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/Slice.lean

Under the head (the terms: Johnson/HonestTrace/U3Fit/SeatsAtHead.lean) the declared rounds, cut at a
sub-protocol's border in the first chain's flat list, are that sub-protocol's own rounds; the number
of rounds in front of the border is a written number; and the member of the kind K4 of group g
stands at number 14 (2 g) + 4, with K4's own table of rounds. So the step «the declared rounds are
the entries of the layers' own table of rounds» of "layersVals" (Johnson/HonestTrace/U3Rows.lean)
says yes. Two definitions; theorems. Public data alone.

Definitions: "rowsBeforeW i": the written rows' rounds in front of row i ("cutFirstFull").
"layersPlacesW off": at off = 0 a test at written values: at the twelve layers' segments (2 g, g
below 12) "placeBy" finds the places of K4 and K3, and the table of steps counts in front of them
what the written rows count in front of rows 14 (2 g) + 4 and 14 (2 g) + 3; off = 1 holds them
against the rows one further on, for the control.

Main theorems:
* "roundsTo_at_head": the rounds in front of border i are "rowsBeforeW i".
* "slice_at_head": for "cF.blocksInOrder[i]? = some b": "declared Zp (rowsBeforeW i) b.rounds.length =
  b.rounds.map (·.entry)". General in i.
* "len_at_head": the member's number of rounds is the written row's.
* "k4_block_at_head": K4's member of group g, its plan, its rounds; two facts on the layers' record.
* "layersDeclared_at_head": at each group the two places, the plan, and the step.

Limits. The head is a premise: the full size and the format's second hash function alone. Two closed facts,
"layersPlacesW_yes" and its control "layersPlacesW_can_fail", are shown by "decide +kernel", each
under "set_option maxRecDepth 1000000", which raises the elaborator's depth of recursion.
Not claimed: more than four of the ten steps at which the layers' maker can reject: the plan, its
two places, the declared rounds. No property of a release, of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.SeatsAtHead
import Johnson.HonestTrace.U3Fit.ValsGeneral
import Johnson.Desc.ProofFile.Honest.K5.Law.BaseAt
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatReturns
import Johnson.IMR.K4Seat
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Pub Ground Spot)
open ProofFile.Honest (roundsTo declsTo)
open ProofFile.Honest.K5 (decls_drop roundsTo_cut)
open VerifiableInference.Desc (Block KindName)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (spotsWritten)
open P5J (AtMgA TS)

/-- The written rows' rounds in front of row number i. -/
def rowsBeforeW (i : Nat) : Nat := ((cutFirstFull.take i).map (·.2.2.1)).sum

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The rounds in front of border i are the written rows'. -/
theorem roundsTo_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) (i : Nat) :
    roundsTo cF.blocksInOrder i = rowsBeforeW i := by
  obtain ⟨-, hc⟩ := H2K5.Door.pins_at_head h.toAtMg
  unfold rowsBeforeW
  rw [roundsTo_cut, hc]

/-- **THE SLICE.** -/
theorem slice_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {i : Nat}
    {b : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[i]? = some b) :
    declared Zp (rowsBeforeW i) b.rounds.length = b.rounds.map (·.entry) := by
  have hlt : i < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb).1
  have hbk : cF.blocksInOrder[i] = b := (List.getElem?_eq_some_iff.1 hb).2
  unfold declared
  rw [← roundsTo_at_head h i, ← h.laid.decl₁, decls_drop, List.drop_eq_getElem_cons hlt, hbk,
    List.flatMap_cons, List.take_left' rfl]

/-- The member's number of rounds is the written row's. -/
theorem len_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {i : Nat}
    {b : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[i]? = some b) :
    (cutFirstFull[i]?).map (·.2.2.1) = some b.rounds.length := by
  obtain ⟨-, hc⟩ := H2K5.Door.pins_at_head h.toAtMg
  rw [← hc]
  unfold cutOf
  rw [List.getElem?_map, hb]
  rfl

/-- **K4's member of group g.** -/
theorem k4_block_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12) :
    ∃ (b : Block TS ProofFile.Cl) (hp : Layer.HPlan2), cF.blocksInOrder[14 * (2 * g) + 4]? = some b ∧
      G.W.G[g]? = some hp ∧
      b.rounds = (OnBytes.Desc.First.K4.entries G.W.layers hp g).map (fun e => { entry := e }) ∧
      G.W.layers.tails = Layer.tailsOf G.W.layers.y ∧ Layer.plansG G.W.layers = .ok G.W.G := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨Lk, b, y, e1, e2, -, hla, -, eg, eP, ehp, et, epl⟩ := IM.k4_of h.scope h.reads O g hg
  have e3 := IM.flatIx_scope h.scope h.reads O (l := 2 * g) (by omega) 2
  have hfl := IM.hear_at_flat e1 e2
  rw [e3] at hfl
  refine ⟨b, y.2.hp, hfl, ehp, ?_, ?_, ?_⟩
  · rw [IM.alone_rounds hla, ← eP, ← eg]
    rfl
  · rw [← eP]
    exact et
  · rw [← eP]
    exact epl

/-- **A TEST AT WRITTEN VALUES**, at off = 0; off = 1 is the control's shift by one row. -/
def layersPlacesW (off : Nat) : Bool :=
  (List.range 12).all fun g =>
    match placeBy cutWritten spotsWritten (2 * g) .K4, placeBy cutWritten spotsWritten (2 * g) .K3 with
    | .ok k4, .ok k3 =>
      k4.2 == rowsBeforeW (14 * (2 * g) + 4 + off) && k3.2 == rowsBeforeW (14 * (2 * g) + 3 + off)
    | _, _ => false

set_option maxRecDepth 1000000 in
theorem layersPlacesW_yes : layersPlacesW 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: against the rows one further on the test says no. -/
theorem layersPlacesW_can_fail : layersPlacesW 1 = false := by decide +kernel

/-- **UNDER THE HEAD: AT EACH GROUP: the two places, the plan, and «the declared rounds are the entries of
the layers' own table of rounds».** -/
theorem layersDeclared_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12) :
    ∃ (k4 k3 : Spot × Nat) (hp : Layer.HPlan2),
      placeIn Zp spotsWritten (2 * g) .K4 = .ok k4 ∧ placeIn Zp spotsWritten (2 * g) .K3 = .ok k3 ∧
      k4.2 = rowsBeforeW (14 * (2 * g) + 4) ∧ k3.2 = rowsBeforeW (14 * (2 * g) + 3) ∧
      G.W.G[g]? = some hp ∧
      declared Zp k4.2 (OnBytes.Desc.First.K4.entries G.W.layers hp g).length =
        OnBytes.Desc.First.K4.entries G.W.layers hp g ∧
      (cutFirstFull[14 * (2 * g) + 4]?).map (·.2.2.1) =
        some (OnBytes.Desc.First.K4.entries G.W.layers hp g).length := by
  obtain ⟨b, hp, hb, ehp, er, -, -⟩ := k4_block_at_head h hG hg
  have w := List.all_eq_true.1 layersPlacesW_yes g (List.mem_range.2 hg)
  have q4 := placeIn_by Zp spotsWritten (2 * g) .K4
  have q3 := placeIn_by Zp spotsWritten (2 * g) .K3
  rw [cuts_at_head h] at q4 q3
  have el : b.rounds.length = (OnBytes.Desc.First.K4.entries G.W.layers hp g).length := by
    rw [er, List.length_map]
  cases e4 : placeBy cutWritten spotsWritten (2 * g) .K4 with
  | error e =>
    rw [e4] at w
    cases w
  | ok k4 =>
    cases e3 : placeBy cutWritten spotsWritten (2 * g) .K3 with
    | error e =>
      rw [e4, e3] at w
      cases w
    | ok k3 =>
      rw [e4, e3] at w
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.add_zero] at w
      rw [e4] at q4
      rw [e3] at q3
      refine ⟨k4, k3, hp, q4, q3, w.1, w.2, ehp, ?_, ?_⟩
      · have s := slice_at_head h hb
        rw [el, er, List.map_map] at s
        rw [w.1, s]
        exact List.map_id _
      · rw [← el]
        exact len_at_head h hb

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.roundsTo_at_head
#check @OnBytes.HonestTrace.U3.Fit.slice_at_head
#check @OnBytes.HonestTrace.U3.Fit.len_at_head
#check @OnBytes.HonestTrace.U3.Fit.k4_block_at_head
#check @OnBytes.HonestTrace.U3.Fit.layersPlacesW_yes
#check @OnBytes.HonestTrace.U3.Fit.layersPlacesW_can_fail
#check @OnBytes.HonestTrace.U3.Fit.layersDeclared_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.roundsTo_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.slice_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.len_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.k4_block_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.layersPlacesW_yes
#print axioms OnBytes.HonestTrace.U3.Fit.layersPlacesW_can_fail
#print axioms OnBytes.HonestTrace.U3.Fit.layersDeclared_at_head
