-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/ReturnsAtHead.lean

Theorems; no definition. Under the head (the terms: Johnson/HonestTrace/U3Fit/SeatsAtHead.lean)
"valsAt" (Johnson/HonestTrace/U3Rows.lean) returns at thirteen of the 25 segments: at the twelve
layers' segments (2 g, g below 12), and, under one premise more on cov, at segment 24. Public data
alone. A SegVals is carried whole; its field vec, a function that awaits the trace's cells, is
applied nowhere here.

Main theorems:
* "seat_of_seg": each segment below 25 has a seat of "U3".
* "valsAt_head_returns": under "cov.sized G.W.hS.T = true" and "LookFits Zp spotsWritten 24 .K6
  G.W.HLy.fs", "valsAt" returns at segment 24.
* "layers_return_at_head": "valsAt Zp G cov (2 * g)" returns at each g below 12, at every cov.
* "head_returns_at_head": "valsAt Zp G cov 24" returns at a cov with "cov.sized G.W.hS.T = true".

Limits. The head is a premise: the full size and the format's second hash function alone. No fact by "decide
+kernel" and no raised option of its own; files that it imports have them. One written length (25
links) is evaluated by plain "decide", inside the proof of "seat_of_seg".
Not claimed: that "valsAt" returns at the twelve odd segments, attention's: no file of this folder
shows that "attVals" returns. "valsHalf" at the layers' segments, and "u3AllFit = true", are not
stated. No property of a release, of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.HeadAtHead
import Johnson.HonestTrace.U3Fit.LayersAtHead
import Johnson.HonestTrace.U3Fit.LookFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Ground)
open Johnson.AtFull.Desc (spotsWritten)
open P5J (AtMgA TS)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head each segment below 25 has a seat of "U3". -/
theorem seat_of_seg (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : Nat} (hl : l < 25) :
    ∃ s ∈ u3Seats Zp G, s.seg = l := by
  have k := u3SeatsFit_at_head h hG
  unfold u3SeatsFit seatsFitBy at k
  rw [Bool.and_eq_true, Bool.and_eq_true] at k
  have a := k.1.1
  unfold allSeated at a
  rw [beq_iff_eq, (first_at_head h hG).2.1] at a
  have m : l ∈ (u3Seats Zp G).map (·.seg) := by
    rw [a]
    exact List.mem_range.2 (by
      have e : VerifiableInference.PlanWritten.proofSizedFull.request.link.length = 25 := by decide
      rw [e]
      exact hl)
  obtain ⟨s, hs, e⟩ := List.mem_map.1 m
  exact ⟨s, hs, e⟩

/-- **Under the head, cov.sized and the lookup's two clauses: the maker returns at segment 24.** -/
theorem valsAt_head_returns (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cov : Head.Covered}
    (hc : cov.sized G.W.hS.T = true) (hL : LookFits Zp spotsWritten 24 .K6 G.W.HLy.fs) :
    ∃ V, valsAt Zp G cov 24 = .ok V := by
  obtain ⟨s, hs, e⟩ := seat_of_seg h hG (l := 24) (by decide)
  have k := valsHalf_head_at_head h hG hc hL s hs e
  unfold valsHalf at k
  rw [e] at k
  cases hv : valsAt Zp G cov 24 with
  | ok V => exact ⟨V, rfl⟩
  | error w =>
    rw [hv] at k
    cases k

/-- **UNDER THE HEAD "valsAt" RETURNS AT THE TWELVE LAYERS' SEGMENTS**, at every cov. -/
theorem layers_return_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cov : Head.Covered) :
    ∀ g < 12, ∃ V, valsAt Zp G cov (2 * g) = .ok V :=
  layers_return h hG (fun _ hg => lookFits_layers h hG hg) cov

/-- **AND AT THE OUTPUT HEAD's SEGMENT**, at a cov that is as long as the positions. -/
theorem head_returns_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cov : Head.Covered}
    (hc : cov.sized G.W.hS.T = true) : ∃ V, valsAt Zp G cov 24 = .ok V :=
  valsAt_head_returns h hG hc (lookFits_head h hG)

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.seat_of_seg
#check @OnBytes.HonestTrace.U3.Fit.valsAt_head_returns
#check @OnBytes.HonestTrace.U3.Fit.layers_return_at_head
#check @OnBytes.HonestTrace.U3.Fit.head_returns_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.seat_of_seg
#print axioms OnBytes.HonestTrace.U3.Fit.valsAt_head_returns
#print axioms OnBytes.HonestTrace.U3.Fit.layers_return_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.head_returns_at_head
