-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ReqFrameReads.lean: WHAT `Plan.reqFrame` (OnBytes/Plan/ReqFrame.lean) READS OF
THE ARRAYS THAT THE SUB-PROOFS DECLARE: the moments alone: two arrays of declared links with the
same moments, link by link, give the same frame at every file and number of answers. (A declared
link has two fields: its name and its moments.) Laws; nothing is evaluated.

  `at_moment`: under the premise the two arrays have a link at the same places, with the same
    moments.
  `takeGroup_reads` · `takeBlock_reads`: the two steps.
  **`reqFrame_reads`**: the frame.
Limits. A law on one routine's text. Nothing on soundness. On hiding nothing.

-/
import OnBytes.Plan.ReqFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes.Plan OnBytes.Params
open OnBytes.Model.Stages (FrameArray FrameLink)

variable {A B : Array FrameLink}

theorem at_moment (h : A.map (·.moment) = B.map (·.moment)) (i : Nat) :
    (A[i]?).map (·.moment) = (B[i]?).map (·.moment) := by
  rw [← Array.getElem?_map, ← Array.getElem?_map, h]

theorem takeGroup_reads (h : A.map (·.moment) = B.map (·.moment)) (n : Nat) (s : GroupsSoFar)
    (g : LayoutGroup) : takeGroup A n s g = takeGroup B n s g := by
  have e := at_moment h g.link
  unfold takeGroup
  cases hA : A[g.link]? with
  | none =>
    cases hB : B[g.link]? with
    | none => rfl
    | some b => rw [hA, hB] at e; exact absurd e (by simp)
  | some a =>
    cases hB : B[g.link]? with
    | none => rw [hA, hB] at e; exact absurd e (by simp)
    | some b =>
      rw [hA, hB] at e
      have e' : a.moment = b.moment := Option.some.inj e
      simp only [Option.bind_eq_bind, Option.bind_some, e']

theorem takeBlock_reads (h : A.map (·.moment) = B.map (·.moment)) (G : GroupsSoFar)
    (s : BlocksSoFar) (b : LayoutBlock) : takeBlock A G s b = takeBlock B G s b := by
  have e := at_moment h b.link
  unfold takeBlock
  cases hA : A[b.link]? with
  | none =>
    cases hB : B[b.link]? with
    | none => rfl
    | some y => rw [hA, hB] at e; exact absurd e (by simp)
  | some x =>
    cases hB : B[b.link]? with
    | none => rw [hA, hB] at e; exact absurd e (by simp)
    | some y =>
      rw [hA, hB] at e
      have e' : x.moment = y.moment := Option.some.inj e
      simp only [Option.bind_eq_bind, Option.bind_some, e']

/-- **`reqFrame` reads of the declared links their moments alone.** -/
theorem reqFrame_reads (h : A.map (·.moment) = B.map (·.moment)) (file : LayoutLines) (n : Nat) :
    reqFrame A file n = reqFrame B file n := by
  have f1 : takeGroup A n = takeGroup B n := by
    funext s g; exact takeGroup_reads h n s g
  have f2 : takeBlock A = takeBlock B := by
    funext G s b; exact takeBlock_reads h G s b
  have m0 : (A.map fun _ => (#[] : Array ReqMessage)) = B.map fun _ => #[] := by
    have := congrArg (fun X => X.map fun _ => (#[] : Array ReqMessage)) h
    simpa only [Array.map_map, Function.comp_def] using this
  have m1 : (A.map fun l => l.moment.map fun _ => (#[] : Array Nat)) =
      B.map fun l => l.moment.map fun _ => #[] := by
    have := congrArg (fun X => X.map fun (m : Array (Array FrameArray)) =>
      m.map fun _ => (#[] : Array Nat)) h
    simpa only [Array.map_map, Function.comp_def] using this
  have m2 : (A.map fun _ => (#[] : Array ReqArray)) = B.map fun _ => #[] := by
    have := congrArg (fun X => X.map fun _ => (#[] : Array ReqArray)) h
    simpa only [Array.map_map, Function.comp_def] using this
  have m3 : (A.map fun l => l.moment.map fun m => m.map fun _ => (none : Option Nat)) =
      B.map fun l => l.moment.map fun m => m.map fun _ => none := by
    have := congrArg (fun X => X.map fun (q : Array (Array FrameArray)) =>
      q.map fun m => m.map fun _ => (none : Option Nat)) h
    simpa only [Array.map_map, Function.comp_def] using this
  unfold reqFrame
  rw [f1, f2, m0, m1, m2, m3]

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.at_moment
#print axioms Johnson.AtFull.Made.takeGroup_reads
#print axioms Johnson.AtFull.Made.takeBlock_reads
#print axioms Johnson.AtFull.Made.reqFrame_reads
