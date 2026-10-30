-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/ReqKept.lean (kind K10; toward the row K10_condition): WHO JOINS EACH
LINK's GROUP AND WHO IS KEPT THERE, OFF THE WRITTEN REQUEST's SHAPE BY THE PROGRAM's TWO RULES;
HELD, BY THE KERNEL, AGAINST THREE OTHER WRITTEN RECORDS. Definitions, statements and proofs. NO
TEXT OF THE DESCRIPTION STANDS BENEATH THIS FILE.

CornersKept.lean and LayoutDrawn.lean (beside this file) run over EVERY choice of kept members, and
leave open which choice is a plan's: the messages' lives are not in the written lists of messages.
Johnson/Desc/ReqLit/ has the request's shape, with the lives, as a written value.
  `joinersAt s l`: who joins the group of link l, each with the flag "kept", typed after the
    program's two rules (read, not proved: `joinOwn`, OnBytes/Iop/Req.lean:300: the link's own
    messages, kept if the life is above 0; `switchAdmit`, OnBytes/Iop/Cs.lean:539: the carrying
    message, not kept, and the messages that take earlier messages' kept rows, with the flag
    keptAgain of `reqGroups`' target).
  `flagsOf`, `kbAt s l lo`: these flags laid on a written list's messages (a message without a main
    row: not kept). `keptRows lo kb`: the main rows kept.
  `RealAt s links front closings l`: four things at link l, decidable: (1) the joiners' shapes ARE
    the shapes of the written list's messages with a main row, in order; (2) at these flags the
    layout's formula `kLay` gives the k of the program's own `reqGroups`; (3) that k is the number
    of fold rounds of the l-th closing of the written rounds (RoundsWritten.lean); (4) JUST ONE
    group in front has that k and, as its slots, 2 ^ ceilLog2 (1 + the kept rows): the number that
    the planner's load takes group by group (`reqLoadFrom`, OnBytes/Params/DeriveReq.lean: 2 ^ clog2
    (1 + keptHere): read).
  `real_full`, `real_small`: SO IT IS at all 25 and all 5 links. `real_full_numbers`,
    `real_small_numbers`: the kept rows and k: (12, 8) and (3, 7) in turn, then (0, 8); and (4, 9),
    (1, 7), (4, 9), (1, 7), (0, 8).
  `lifeTurned`, `real_controls`: `RealAt` CAN SAY NO: with one life turned to 0 it fails at the
    first two links, at both sizes; at the number behind the last link it fails at the true shapes.
  `RealAt.group`: so a group in front has the layout's k at these flags: the one premise of
    `k10_condition_full_layK` and of `k10_full_block_lay` can be met there; and (4) says which
    group.
What it settles among the written records: which list goes with which closing and with which group
in front, by more than a number that repeats: link by link the shapes agree message by message with
the shape's own links.
Limits. "THE FLAGS" ARE THOSE THAT `joinersAt` MAKES OF THE WRITTEN SHAPE. That the written shape is
the planner's request is held by a run, not by Lean (Johnson/Desc/ReqLit/). `joinersAt` is typed
AFTER the program's two rules: no lemma ties it to `ReqFrame.first`, `later`, `joinOwn`,
`switchAdmit`. That a RUNNING statement's group has these members and flags at a closing is not
shown (`layout_congr`'s premises, LayoutDrawn.lean). The last group (the last test's first stage) is
not treated. Nothing on soundness of the protocol.

-/
import Johnson.Desc.ReqLit.Small
import Johnson.Desc.ReqLit.Full
import Johnson.Desc.First.Close.Law.CornersKept
import Johnson.Desc.First.Close.Law.RoundsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G
open VerifiableInference.Desc.ReqLit

/-- **Who joins the group of link l, with the flag "kept"**, by the program's two rules, in the
order of sending: from the second link on the carrying message (not kept) and the messages that take
earlier messages' kept rows (with the switch's target's flag "kept again"); then the link's own
messages, in the list's order (kept if the life is above 0). -/
def joinersAt (s : ReqShape) (l : Nat) : List (OracleShape × Bool) :=
  let G := (reqGroups s).getD l {}
  (if l == 0 then [] else
    (G.target.shape, false) :: G.target.kept.toList.map fun k => (k.shape, k.keptAgain)) ++
  ((s.link.getD l ⟨0, []⟩).messages.map fun m => (m.shape, decide (0 < m.life)))

/-- The flags of a written list's messages off the joiners' flags: a message with a main row takes
the next joiner's flag; one without takes "not kept". -/
def flagsOf : List (OracleShape × ℕ) → List Bool → List Bool
  | [], _ => []
  | x :: lo, fl =>
    if x.1.mainRows == 0 then false :: flagsOf lo fl
    else match fl with
      | b :: fl' => b :: flagsOf lo fl'
      | [] => false :: flagsOf lo []

/-- The flags at a written list: those of link l of the shape s. -/
def kbAt (s : ReqShape) (l : Nat) (lo : List (OracleShape × ℕ)) (i : Fin lo.length) : Bool :=
  (flagsOf lo ((joinersAt s l).map (·.2))).getD i.val false

/-- The main rows that are kept at a written list under flags. -/
def keptRows (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) : ℕ :=
  ((List.finRange lo.length).map fun i => if kb i then (lo.get i).1.mainRows else 0).sum

/-- What is held at link l: the joiners' shapes are the shapes of the written list's messages with a
main row, in order; at these flags the layout's formula gives the plan's own k; that k is the
number of fold rounds of the l-th closing of the written rounds; and ONE group in front has that k
and, as its slots, the least power of two above the kept rows. -/
def RealAt (s : ReqShape) (links : List (List (OracleShape × ℕ))) (front : List GroupSize)
    (closings : List (ℕ × Option ℕ)) (l : Nat) : Prop :=
  let lo := links.getD l []
  (joinersAt s l).map (·.1) = (lo.filter fun x => x.1.mainRows != 0).map (·.1) ∧
  kLay lo (kbAt s l lo) = ((reqGroups s).getD l {}).k ∧
  (closings.getD l (0, none)).2 = some (kLay lo (kbAt s l lo)) ∧
  (front.filter fun g => g.k == kLay lo (kbAt s l lo) &&
    g.slots == 2 ^ ceilLog2 (keptRows lo (kbAt s l lo) + 1)).length = 1

instance (s : ReqShape) (links : List (List (OracleShape × ℕ))) (front : List GroupSize)
    (closings : List (ℕ × Option ℕ)) (l : Nat) : Decidable (RealAt s links front closings l) := by
  unfold RealAt
  infer_instance

set_option maxRecDepth 1000000 in
/-- **SO IT IS AT ALL 25 LINKS OF THE FULL SIZE.** -/
theorem real_full : ∀ l, l < 25 →
    RealAt shapeFull linksFullLit frontFull (closingsOf dryProofFull.1) l := by
  rw [full_closings]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- And at all 5 of the small size. -/
theorem real_small : ∀ l, l < 5 →
    RealAt shapeSmall linksSmallLit frontSmall (closingsOf dryProofSmall.1) l := by
  rw [small_closings]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The kept main rows and the layout's k at these flags, link by link. -/
theorem real_full_numbers : ((List.range 25).map fun l =>
    (keptRows (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])),
      kLay (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])))) =
    (List.replicate 12 [(12, 8), (3, 7)]).flatten ++ [(0, 8)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem real_small_numbers : ((List.range 5).map fun l =>
    (keptRows (linksSmallLit.getD l []) (kbAt shapeSmall l (linksSmallLit.getD l [])),
      kLay (linksSmallLit.getD l []) (kbAt shapeSmall l (linksSmallLit.getD l [])))) =
    [(4, 9), (1, 7), (4, 9), (1, 7), (0, 8)] := by
  decide +kernel

/-- The shape with the life of the first link's second message turned to 0. -/
def lifeTurned (s : ReqShape) : ReqShape :=
  { s with link := s.link.modifyHead fun L =>
      { L with messages := L.messages.modify 1 fun m => { m with life := 0 } } }

set_option maxRecDepth 1000000 in
/-- **`RealAt` CAN SAY NO**: with one life turned it fails at the first link and at the second, at
both sizes; and at the number behind the last link it fails at the true shapes. -/
theorem real_controls :
    ¬ RealAt (lifeTurned shapeFull) linksFullLit frontFull (closingsOf dryProofFull.1) 0 ∧
    ¬ RealAt (lifeTurned shapeFull) linksFullLit frontFull (closingsOf dryProofFull.1) 1 ∧
    ¬ RealAt (lifeTurned shapeSmall) linksSmallLit frontSmall (closingsOf dryProofSmall.1) 0 ∧
    ¬ RealAt (lifeTurned shapeSmall) linksSmallLit frontSmall (closingsOf dryProofSmall.1) 1 ∧
    ¬ RealAt shapeFull linksFullLit frontFull (closingsOf dryProofFull.1) 25 ∧
    ¬ RealAt shapeSmall linksSmallLit frontSmall (closingsOf dryProofSmall.1) 5 := by
  rw [full_closings, small_closings]
  decide +kernel

/-- **The one premise of `k10_condition_full_layK` and of `k10_full_block_lay` can be met at the
flags that the two rules give at the written shape**: a group in front has the layout's k there. -/
theorem RealAt.group {s : ReqShape} {links : List (List (OracleShape × ℕ))}
    {front : List GroupSize} {closings : List (ℕ × Option ℕ)} {l : Nat}
    (h : RealAt s links front closings l) :
    ∃ gs ∈ front, gs.k = kLay (links.getD l []) (kbAt s l (links.getD l [])) := by
  obtain ⟨-, -, -, h4⟩ := h
  obtain ⟨g, hg⟩ := List.length_eq_one_iff.1 h4
  have hm : g ∈ front.filter fun g => g.k == kLay (links.getD l []) (kbAt s l (links.getD l [])) &&
      g.slots == 2 ^ ceilLog2 (keptRows (links.getD l []) (kbAt s l (links.getD l [])) + 1) := by
    rw [hg]
    exact List.mem_singleton.2 rfl
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hm
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨g, h1, h2.1⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.real_full
#print axioms VerifiableInference.Desc.First.Close.real_small
#print axioms VerifiableInference.Desc.First.Close.real_full_numbers
#print axioms VerifiableInference.Desc.First.Close.real_small_numbers
#print axioms VerifiableInference.Desc.First.Close.real_controls
#print axioms VerifiableInference.Desc.First.Close.RealAt.group

