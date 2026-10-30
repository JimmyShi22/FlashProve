-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofBack/Decl.lean: the value of `Johnson.G.OfPlan.fileOf`
(Johnson/G/RoundsOfPlan.lean) at the proof file's written values of the full size (so `declPOf`'s
text at them), for every three plans whose rounds are the written rounds' entries and which have no
entry that is no round. In pieces that Lean's kernel bears.

Definitions.
  `shapeW`, `ridersW`, `inputW`: what `declPOf` reads of the sized proof, at the written one
    (`proofSizedFull`).
  `t0`, `t1`, `t2`: the three chains' trees, numbered (Johnson/AtFull/ProofBack/Trees.lean).
  `plan0`, `plan1`, `plan2`: what `frameOpens`, `sharedOpens` and `secondOpens` make of them: for
    each round that draws positions, in order, the list of what it opens. (No `Fmt.Plan`.)
Statements.
  `recs_kind` (BY THE KERNEL), `pos_eq`, `count_pos`: at each of the 136 distinct written rounds the
    kind is that of the entry's name; carried to all rounds by `mem_unrunR`; so the rounds that draw
    positions are counted along the runs by `cntE_eq` (Johnson/G/DryProofSmall.lean).
  `cnt_pos`, `cnt_loc` (BY THE KERNEL), `count_pos0`, `count_pos1`, `count_pos2`, `count_loc0`: 31,
    10 and 5 rounds draw positions; 25 rounds of the first chain are named "LOC".
  `lens`, `none_empty`, `all_opened`: BY THE KERNEL, behind the laws of Johnson/Unfolds/ on Lean's
    library: `plan0`, `plan1`, `plan2` have 31, 10 and 5 lists; none is empty; every tree that a
    chain sends is opened somewhere.
  `c0`, `c1`, `c2`, `fill0`, `fill1`, `fill2`: so `fill` returns `fillL`
    (Johnson/Unfolds/FillLaw.lean) at each chain, at every name.
  **`fileOf_written`**: from (e0, e1, e2) the three plans' rounds are `es0`, `es1`, `es2` and (o0,
    o1, o2) each has as many entries as rounds: `fileOf "proof file" …` returns
    `(fillL es0 plan0, fillL es1 plan1, fillL es2 plan2)`. By `Johnson.Unfolds.fileOf_of`,
    `toldIn_fill`, `treesSent_eq`.
  Negative test, BY THE KERNEL: `all_opened_no`: with `plan0` left out a tree that a chain sends is
    opened by no list.

Limits. The full size alone. THE SIX EQUATIONS ON THE PLANS ARE PREMISES. IT SPEAKS OF WRITTEN
VALUES: that the written sendings, rounds and sizes are what `sendsOf` and the planner make of any
public files is not said here. The value stands as terms; Johnson/AtFull/ProofBack/DeclWritten.lean
ties it to a written list. That the distinct written rounds are 136 is held by no theorem here.
Nothing on soundness. On hiding nothing.

-/
import Johnson.AtFull.ProofBack.Trees
import Johnson.Unfolds.FileLaw
import Johnson.Unfolds.OpensLaw
import Johnson.G.DryProofSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofBack
open OnBytes OnBytes.Params Johnson.G Johnson.G.OfPlan Johnson.Unfolds
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.Written (cntE cntE_eq mem_unrunR)

/-! ## The counts along the runs -/

/-- BY THE KERNEL: at each of the 136 distinct written rounds the kind is that of the entry's name.
-/
theorem recs_kind :
    dryProofRecsFull.all (fun x => Fmt.kindOf x.1.entry.name == some x.1.kind) = true := by
  decide +kernel

/-- So at every round of a list along runs of these 136 rounds: it draws positions by its name just
if by its kind. -/
theorem pos_eq {runs : List (Nat × Nat)} {x : Fmt.Round × List Fmt.Stored}
    (hx : x ∈ unrunR dryProofRecsFull runs) :
    (Fmt.kindOf x.1.entry.name == some .positions) = (x.1.kind == .positions) := by
  rw [eq_of_beq (List.all_eq_true.1 recs_kind x (mem_unrunR hx))]
  rfl

/-- The number of rounds that draw positions, along the runs. -/
theorem count_pos (runs : List (Nat × Nat)) (n : Nat)
    (h : cntE dryProofRecsFull (fun x => x.1.kind == .positions) 0 runs = n) :
    (((unrunR dryProofRecsFull runs).map (·.1.entry)).filter
      fun e => Fmt.kindOf e.name == some .positions).length = n := by
  rw [List.filter_map, List.length_map]
  have e : ((unrunR dryProofRecsFull runs).filter
      ((fun e : Fmt.Entry => Fmt.kindOf e.name == some .positions) ∘ fun x => x.1.entry)) =
      (unrunR dryProofRecsFull runs).filter fun x => x.1.kind == .positions :=
    List.filter_congr fun x hx => pos_eq hx
  rw [e]
  have c := cntE_eq dryProofRecsFull (fun x => x.1.kind == .positions) runs 0
  rw [h] at c
  omega

set_option maxRecDepth 1000000 in
/-- BY THE KERNEL, along the runs: 31, 10 and 5 rounds of the three chains have the kind
"positions". -/
theorem cnt_pos :
    (cntE dryProofRecsFull (fun x => x.1.kind == .positions) 0 dryProofRunsFull0,
      cntE dryProofRecsFull (fun x => x.1.kind == .positions) 0 dryProofRunsFull1,
      cntE dryProofRecsFull (fun x => x.1.kind == .positions) 0 dryProofRunsFull2) =
      (31, 10, 5) := by
  decide +kernel

/-- 31 rounds of the first chain draw positions. -/
theorem count_pos0 :
    (es0.filter fun e => Fmt.kindOf e.name == some .positions).length = 31 := by
  have s := cnt_pos
  rw [Prod.mk.injEq, Prod.mk.injEq] at s
  show (((unrunR dryProofRecsFull dryProofRunsFull0).map (·.1.entry)).filter _).length = 31
  exact count_pos _ _ s.1

/-- 10 rounds of the shared chain draw positions. -/
theorem count_pos1 :
    (es1.filter fun e => Fmt.kindOf e.name == some .positions).length = 10 := by
  have s := cnt_pos
  rw [Prod.mk.injEq, Prod.mk.injEq] at s
  show (((unrunR dryProofRecsFull dryProofRunsFull1).map (·.1.entry)).filter _).length = 10
  exact count_pos _ _ s.2.1

/-- 5 rounds of the second chain draw positions. -/
theorem count_pos2 :
    (es2.filter fun e => Fmt.kindOf e.name == some .positions).length = 5 := by
  have s := cnt_pos
  rw [Prod.mk.injEq, Prod.mk.injEq] at s
  show (((unrunR dryProofRecsFull dryProofRunsFull2).map (·.1.entry)).filter _).length = 5
  exact count_pos _ _ s.2.2

set_option maxRecDepth 1000000 in
/-- BY THE KERNEL, along the runs: 25 rounds of the first chain are named "LOC". -/
theorem cnt_loc :
    cntE dryProofRecsFull (fun x => x.1.entry.name == "LOC") 0 dryProofRunsFull0 = 25 := by
  decide +kernel

/-- 25 rounds of the first chain are named "LOC". -/
theorem count_loc0 : (es0.filter fun e => e.name == "LOC").length = 25 := by
  unfold es0
  rw [List.filter_map, List.length_map]
  have c := cntE_eq dryProofRecsFull (fun x => x.1.entry.name == "LOC") dryProofRunsFull0 0
  rw [cnt_loc] at c
  show ((unrunR dryProofRecsFull dryProofRunsFull0).filter
    fun x => x.1.entry.name == "LOC").length = 25
  omega

/-! ## The three chains' trees and lists -/

/-- The shared chain's shape. -/
def shapeW : LinShape := proofSizedFull.batch.shape

/-- The leaf classes of what rides at the start. -/
def ridersW : List Nat := proofSizedFull.request.atStart.map (·.leafClass)

/-- The first chain's trees, numbered. -/
def t0 : List (Sent × Nat) := (sortedW (sentsOf proofSends0 0) extra0).zipIdx
/-- The shared chain's trees, numbered. -/
def t1 : List (Sent × Nat) := (sortedW (sentsOf proofSends1 0) extra1).zipIdx
/-- The second chain's trees, numbered. -/
def t2 : List (Sent × Nat) := (sortedW (sentsOf proofSends2 0) extra2).zipIdx

/-- Which of the first chain's trees holds the input. -/
def inputW (t : Sent) : Bool := t.tag == .link 0 0 && ridersW.contains t.cls

/-- What the first chain's rounds of positions open, in order. -/
def plan0 : List (List Told × List Fmt.Stored) := noStored (frameOpens ridersW t0 25)
/-- What the shared chain's rounds of positions open and store, in order. -/
def plan1 : List (List Told × List Fmt.Stored) := sharedOpens shapeW t1
/-- What the second chain's rounds of positions open, in order. -/
def plan2 : List (List Told × List Fmt.Stored) := noStored (secondOpens shapeW inputW t0 t1 t2)

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the three plans have 31, 10 and 5 lists. -/
theorem lens : (plan0.length, plan1.length, plan2.length) = (31, 10, 5) := by
  unfold plan0 plan1 plan2 t0 t1 t2 sortedW sentsOf extra0 extra1 extra2 sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: no list of the three plans is empty of trees and of stored tables. -/
theorem none_empty :
    ((plan0.zipIdx.find? fun x => x.1.1.isEmpty && x.1.2.isEmpty).isNone &&
      (plan1.zipIdx.find? fun x => x.1.1.isEmpty && x.1.2.isEmpty).isNone &&
      (plan2.zipIdx.find? fun x => x.1.1.isEmpty && x.1.2.isEmpty).isNone) = true := by
  unfold plan0 plan1 plan2 t0 t1 t2 sortedW sentsOf extra0 extra1 extra2 sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: every tree that a chain sends is opened by some list of the three plans. -/
theorem all_opened :
    (([t0, t1, t2].zipIdx.flatMap fun c => c.1.map fun t => (c.2, t.2)).find? fun x =>
      !(toldW (plan0.flatMap (·.1)) (plan1.flatMap (·.1)) (plan2.flatMap (·.1))).contains x) =
      none := by
  unfold plan0 plan1 plan2 t0 t1 t2 sortedW sentsOf extra0 extra1 extra2 sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- As many rounds of the first chain draw positions as its plan has lists. -/
theorem c0 : (es0.filter fun e => Fmt.kindOf e.name == some .positions).length = plan0.length := by
  have l := lens
  rw [Prod.mk.injEq, Prod.mk.injEq] at l
  rw [count_pos0, l.1]

/-- As many rounds of the shared chain draw positions as its plan has lists. -/
theorem c1 : (es1.filter fun e => Fmt.kindOf e.name == some .positions).length = plan1.length := by
  have l := lens
  rw [Prod.mk.injEq, Prod.mk.injEq] at l
  rw [count_pos1, l.2.1]

/-- As many rounds of the second chain draw positions as its plan has lists. -/
theorem c2 : (es2.filter fun e => Fmt.kindOf e.name == some .positions).length = plan2.length := by
  have l := lens
  rw [Prod.mk.injEq, Prod.mk.injEq] at l
  rw [count_pos2, l.2.2]

/-- `fill` at the first chain, at every name. -/
theorem fill0 (at_ : String) : fill at_ es0 plan0 = .ok (fillL es0 plan0) :=
  fill_of (by rw [c0]; exact beq_self_eq_true _)
    (Option.isNone_iff_eq_none.1 (by
      have h := none_empty
      simp only [Bool.and_eq_true] at h
      exact h.1.1))

/-- `fill` at the shared chain, at every name. -/
theorem fill1 (at_ : String) : fill at_ es1 plan1 = .ok (fillL es1 plan1) :=
  fill_of (by rw [c1]; exact beq_self_eq_true _)
    (Option.isNone_iff_eq_none.1 (by
      have h := none_empty
      simp only [Bool.and_eq_true] at h
      exact h.1.2))

/-- `fill` at the second chain, at every name. -/
theorem fill2 (at_ : String) : fill at_ es2 plan2 = .ok (fillL es2 plan2) :=
  fill_of (by rw [c2]; exact beq_self_eq_true _)
    (Option.isNone_iff_eq_none.1 (by
      have h := none_empty
      simp only [Bool.and_eq_true] at h
      exact h.2))

/-- **For three plans whose rounds are the written entries and which have no other entry: `fileOf`
at the proof file's written values returns `fillL` at the three chains.** -/
theorem fileOf_written {P0 P1 P2 : Fmt.Plan} (e0 : P0.rounds = es0)
    (o0 : P0.entries.length - P0.rounds.length = 0) (e1 : P1.rounds = es1)
    (o1 : P1.entries.length - P1.rounds.length = 0) (e2 : P2.rounds = es2)
    (o2 : P2.entries.length - P2.rounds.length = 0) :
    fileOf "proof file" shapeW P0 P1 P2 proofSends0 proofSends1 proofSends2
      (fun ts es => frameOpens ridersW ts (es.filter fun e => e.name == "LOC").length) inputW =
      .ok (fillL es0 plan0, fillL es1 plan1, fillL es2 plan2) := by
  refine fileOf_of (t0 := t0) (t1 := t1) (t2 := t2) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [treesSent_eq, o0, e0]
    exact trees0 _
  · rw [treesSent_eq, o1, e1]
    exact trees1 _
  · rw [treesSent_eq, o2, e2]
    exact trees2 _
  · rw [e0]
    show fill _ es0
      (noStored (frameOpens ridersW t0 (es0.filter fun e => e.name == "LOC").length)) = _
    rw [count_loc0]
    exact fill0 _
  · rw [e1]
    exact fill1 _
  · rw [e2]
    exact fill2 _
  · rw [toldIn_fill c0 c1 c2]
    exact all_opened

/-! ## A negative test, stated positively -/

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: with `plan0` left out, a tree that a chain sends is opened by no list. -/
theorem all_opened_no :
    ((([t0, t1, t2].zipIdx.flatMap fun c => c.1.map fun t => (c.2, t.2)).find? fun x =>
      !(toldW [] (plan1.flatMap (·.1)) (plan2.flatMap (·.1))).contains x).isSome) = true := by
  unfold plan1 plan2 t0 t1 t2 sortedW sentsOf extra0 extra1 extra2 sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end Johnson.AtFull.ProofBack

#print axioms Johnson.AtFull.ProofBack.recs_kind
#print axioms Johnson.AtFull.ProofBack.pos_eq
#print axioms Johnson.AtFull.ProofBack.count_pos
#print axioms Johnson.AtFull.ProofBack.cnt_pos
#print axioms Johnson.AtFull.ProofBack.count_pos0
#print axioms Johnson.AtFull.ProofBack.count_pos1
#print axioms Johnson.AtFull.ProofBack.count_pos2
#print axioms Johnson.AtFull.ProofBack.cnt_loc
#print axioms Johnson.AtFull.ProofBack.count_loc0
#print axioms Johnson.AtFull.ProofBack.lens
#print axioms Johnson.AtFull.ProofBack.none_empty
#print axioms Johnson.AtFull.ProofBack.all_opened
#print axioms Johnson.AtFull.ProofBack.c0
#print axioms Johnson.AtFull.ProofBack.c1
#print axioms Johnson.AtFull.ProofBack.c2
#print axioms Johnson.AtFull.ProofBack.fill0
#print axioms Johnson.AtFull.ProofBack.fill1
#print axioms Johnson.AtFull.ProofBack.fill2
#print axioms Johnson.AtFull.ProofBack.fileOf_written
#print axioms Johnson.AtFull.ProofBack.all_opened_no
