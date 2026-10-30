-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Honest/FlatSteps.lean: from the shared chain's own flat list, as a proof file's IOP
as written in Lean holds it, to the eight sub-protocols of the linear claim's shared rounds as the
kind's text makes them.

The IOP holds the shared chain carried to the file's type of claims: its list is a front
sub-protocol, then the kind's eight, carried (Johnson/Desc/K14/Honest/FlatForm.lean: Like, FlatOf,
flatOf_carried). Johnson/Desc/K14/Honest/StepsBack.lean and StepsTwins.lean speak of the eight at
the kind's own type. This file goes from the one to the other: a carried sub-protocol has the same
step; a fold that returns over carried ones returns the same over them as they were; the front
sub-protocol takes nothing and leaves the state.

Main names:
  Like.step, fold_like   one step; one return of the fold, member by member
  step_retype, fold_retype, peel_front, peel_frontOf   the same said of Block.retype; the front
                      sub-protocol off the front of a fold
  FlatAt xs c B       FlatOf at the eight of B
  StepTo1.more, …, StepTo7.more   a run of steps, and one step more
  FlatAt.start, FlatAt.stepTo1, …, stepTo8   **from the fold over the list's first so many members
                      to a run of steps**
  FlatAt.member1, …, member8   **at one member**: the fold over the members in front has returned s
                      with nothing left over, and the member's own step has returned s' from s:
                      there is a run of steps up to it whose last two states are s and s'; the
                      rounds and the columns are named

What is assumed, as premises: FlatAt; what goes out with o_u (withU); at "SPLIT": two codes.

What is not claimed. That a fold or a step returns. Nothing on the members behind the eight. Nothing
on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.StepsTwins
import Johnson.Desc.K14.Honest.FlatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block OpenedColumn foldBlocks foldBlocks_ok)
open VerifiableInference.Desc.Sound (foldBlocks_cons_ok)
open Desc.K14.Law (frontOf)

variable {P : P14} {sentU : Array OracleNotice} {Cl : Type}

/-! ## A sub-protocol as far as a step reads it -/

/-- So the two have one step. -/
theorem Like.step {x : Block St Cl} {b : Block St Unit} (h : Like x b) (ft : Nat) (s : St)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) : x.step ft s rs c = b.step ft s rs c := by
  unfold Block.step
  rw [h.rounds, h.decide]

/-- So a fold that returns over a list returns the same over a list that is like it, member by
member. -/
theorem fold_like (ft : Nat) : ∀ (xs : List (Block St Cl)) (bs : List (Block St Unit)),
    List.Forall₂ Like xs bs → ∀ (s : St) (rs : List Fmt.RoundView) (c : List OpenedColumn)
      (r : St × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft xs s rs c = .ok r → foldBlocks ft bs s rs c = .ok r
  | _, _, .nil, _, _, _, _, h => h
  | x :: xs, b :: bs, .cons hl ht, s, rs, c, r, h => by
    obtain ⟨s', k, hle, hs, hf⟩ := foldBlocks_cons_ok ft x xs s rs c r h
    have ih := fold_like ft xs bs ht _ _ _ _ hf
    rw [hl.step, hl.rounds] at hs
    rw [hl.rounds] at hle ih
    have hlen : (rs.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      exact Nat.min_eq_left hle
    have e := foldBlocks_ok ft b bs s (rs.take b.rounds.length) (rs.drop b.rounds.length) c hlen s'
      k hs
    rw [List.take_append_drop] at e
    exact e.trans ih

/-- **A sub-protocol carried to another type of claims has the same step.** -/
theorem step_retype (b : Block St Unit) (ft : Nat) (s : St) (rs : List Fmt.RoundView) (c : List OpenedColumn) :
    (b.retype (Cl' := Cl)).step ft s rs c = b.step ft s rs c :=
  (like_retype b).step ft s rs c

/-- **A fold that returns over carried sub-protocols returns the same over them as they were.** -/
theorem fold_retype (ft : Nat) (l : List (Block St Unit)) (s : St) (rs : List Fmt.RoundView)
    (c : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (l.map (Block.retype (Cl' := Cl))) s rs c = .ok r) :
    foldBlocks ft l s rs c = .ok r := by
  have hl : ∀ l : List (Block St Unit), List.Forall₂ Like (l.map (Block.retype (Cl' := Cl))) l := by
    intro l
    induction l with
    | nil => exact .nil
    | cons b l ih => exact .cons (like_retype b) ih
  exact fold_like ft _ l (hl l) s rs c r h

/-- **The front sub-protocol off the front of a fold**: it has no round, takes no column and leaves
the state. -/
theorem peel_front (c : Model.Verify.Chains) (ft : Nat) (l : List (Block St Unit)) (d : St)
    (rs : List Fmt.RoundView) (cl : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (frontBlock c :: l) d rs cl = .ok r) : foldBlocks ft l d rs cl = .ok r := by
  obtain ⟨s', k, _, hs, hf⟩ := foldBlocks_cons_ok ft (frontBlock c) l d rs cl r h
  obtain ⟨_, rfl, hd⟩ := step_plain_back (frontBlock c) (fun r hr => by cases hr) ft d s' _ cl k hs
  obtain rfl : d = s' := Except.ok.inj hd
  exact hf

/-- **The front sub-protocol, as the carried chain holds it, off the front of a fold.** -/
theorem peel_frontOf (c : Model.Verify.Chains) (ft : Nat) (l : List (Block St Cl)) (d : St)
    (rs : List Fmt.RoundView) (cl : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (frontOf c :: l) d rs cl = .ok r) : foldBlocks ft l d rs cl = .ok r := by
  obtain ⟨s', k, _, hs, hf⟩ := foldBlocks_cons_ok ft (frontOf c) l d rs cl r h
  rw [(like_frontOf c).step] at hs
  obtain ⟨_, rfl, hd⟩ := step_plain_back (frontBlock c) (fun r hr => by cases hr) ft d s' _ cl k hs
  obtain rfl : d = s' := Except.ok.inj hd
  exact hf

/-! ## A flat list that begins with the front sub-protocol and the kind's eight -/

/-- xs begins with the shared chain's front sub-protocol and the eight of B
(Johnson/Desc/K14/Honest/FlatForm.lean: FlatOf). -/
abbrev FlatAt (xs : List (Block St Cl)) (c : Model.Verify.Chains) (B : Eight P) : Prop :=
  FlatOf xs c B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8

variable {xs : List (Block St Cl)} {c : Model.Verify.Chains} {B : Eight P}

/-- In front of "LIN point" the fold has returned the state that it was handed, and has taken
nothing. -/
theorem FlatAt.start (F : FlatAt xs c B) (ft : Nat) (d0 s : St) (rs rs' : List Fmt.RoundView)
    (cl cl' : List OpenedColumn) (h : foldBlocks ft (xs.take 1) d0 rs cl = .ok (s, rs', cl')) :
    d0 = s ∧ rs = rs' ∧ cl = cl' := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, _⟩ := F
  have h' : foldBlocks ft [x0] d0 rs cl = .ok (s, rs', cl') := h
  exact fold_nil
    (peel_front c ft _ _ _ _ _ (fold_like ft _ [frontBlock c] (.cons l0 .nil) _ _ _ _ h'))

/-! ## One step more -/

/-- A run of steps up to the sub-protocol in front, and the step of the sending of o_u: a run of
steps up to it. -/
theorem StepTo1.more {ft : Nat} {d0 : St} {W : Seen8} {D : States8} (u : StepTo1 B ft d0 W D)
    (Ra Rb : Fmt.RoundView) (s' : St) (cl : List OpenedColumn) (n : Nat) (h : B.b2.step ft D.d1 [Ra, Rb] cl = .ok
                    (s', n)) :
    StepTo2 B ft d0 { W with R2a := Ra, R2b := Rb } { D with d2 := s' } :=
  ⟨⟨u.s1⟩, ⟨_, _, h⟩⟩

/-- A run of steps up to the sub-protocol in front, and the step of "(rec_gamma)": a run of steps up
to it. -/
theorem StepTo2.more {ft : Nat} {d0 : St} {W : Seen8} {D : States8} (u : StepTo2 B ft d0 W D)
    (s' : St) (cl : List OpenedColumn) (n : Nat) (h : B.b3.step ft D.d2 [] cl = .ok (s', n)) :
    StepTo3 B ft d0 W { D with d3 := s' } :=
  ⟨⟨⟨u.front.s1⟩, u.s2⟩, ⟨_, _, h⟩⟩

/-- A run of steps up to the sub-protocol in front, and the step of "LOC": so a run
of steps up to it. -/
theorem StepTo3.more {ft : Nat} {d0 : St} {W : Seen8} {D : States8} (u : StepTo3 B ft d0 W D)
    (R : Fmt.RoundView) (cs : List OpenedColumn) (s' : St) (cl : List OpenedColumn) (h : B.b4.step ft D.d3 [R] (cs ++ cl) =
                             .ok (s', cs.length)) :
    StepTo4 B ft d0 { W with R4 := R, cs := cs } { D with d4 := s' } :=
  ⟨⟨⟨⟨u.front.front.s1⟩, u.front.s2⟩, u.s3⟩, ⟨cl, h⟩⟩

/-- A run of steps up to the sub-protocol in front, and the step of the sending of o_omega and o_sp:
a run of steps up to it. -/
theorem StepTo4.more {ft : Nat} {d0 : St} {W : Seen8} {D : States8} (u : StepTo4 B ft d0 W D)
    (Ra Rb : Fmt.RoundView) (s' : St) (cl : List OpenedColumn) (n : Nat) (h : B.b5.step ft D.d4 [Ra, Rb] cl = .ok
                    (s', n)) :
    StepTo5 B ft d0 { W with R5a := Ra, R5b := Rb } { D with d5 := s' } :=
  ⟨⟨⟨⟨⟨u.front.front.front.s1⟩, u.front.front.s2⟩, u.front.s3⟩, u.s4⟩, ⟨_, _, h⟩⟩

/-- A run of steps up to the sub-protocol in front, and the step of the joinings: a run of steps up
to it. -/
theorem StepTo5.more {ft : Nat} {d0 : St} {W : Seen8} {D : States8} (u : StepTo5 B ft d0 W D)
    (s' : St) (cl : List OpenedColumn) (n : Nat) (h : B.b6.step ft D.d5 [] cl = .ok (s', n)) :
    StepTo6 B ft d0 W { D with d6 := s' } :=
  ⟨⟨⟨⟨⟨⟨u.front.front.front.front.s1⟩, u.front.front.front.s2⟩, u.front.front.s3⟩, u.front.s4⟩,
    u.s5⟩, ⟨_, _, h⟩⟩

/-- A run of steps up to the sub-protocol in front, and the step of "LIN zeta": so a run
of steps up to it. -/
theorem StepTo6.more {ft : Nat} {d0 : St} {W : Seen8} {D : States8} (u : StepTo6 B ft d0 W D)
    (R : Fmt.RoundView) (s' : St) (cl : List OpenedColumn) (n : Nat) (h : B.b7.step ft D.d6 [R] cl = .ok (s', n)) :
    StepTo7 B ft d0 { W with R7 := R } { D with d7 := s' } :=
  ⟨⟨⟨⟨⟨⟨⟨u.front.front.front.front.front.s1⟩, u.front.front.front.front.s2⟩,
    u.front.front.front.s3⟩, u.front.front.s4⟩, u.front.s5⟩, u.s6⟩, ⟨_, _, h⟩⟩

/-- A run of steps up to the sub-protocol in front, and the step of "SPLIT": so a run
of steps up to it. -/
theorem StepTo7.more {ft : Nat} {d0 : St} {W : Seen8} {D : States8} (u : StepTo7 B ft d0 W D)
    (R : Fmt.RoundView) (s' : St) (cl : List OpenedColumn) (n : Nat) (h : B.b8.step ft D.d7 [R] cl = .ok (s', n)) :
    StepTo8 B ft d0 { W with R8 := R } { D with d8 := s' } :=
  ⟨⟨⟨⟨⟨⟨⟨⟨u.front.front.front.front.front.front.s1⟩, u.front.front.front.front.front.s2⟩,
    u.front.front.front.front.s3⟩, u.front.front.front.s4⟩, u.front.front.s5⟩, u.front.s6⟩, u.s7⟩,
    ⟨_, _, h⟩⟩

/-! ## From the fold over the flat list to a run of steps -/

/-- **From the fold over the flat list up to "LIN point"** to a run of steps. -/
theorem FlatAt.stepTo1 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 2) d0 rs cl = .ok (s, rs', cl')) :
    ∃ W D, rs = [W.R1] ++ rs' ∧ cl = cl' ∧ D.d1 = s ∧ StepTo1 B ft d0 W D := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have h' : foldBlocks ft [x0, x1] d0 rs cl = .ok (s, rs', cl') := h
  have k := fold_like ft _ (frontBlock c :: [B.b1]) (.cons l0 (.cons l1 .nil)) _ _ _ _ h'
  exact B.stepTo1_of_fold hU ft d0 s rs rs' cl cl' (peel_front c ft _ _ _ _ _ k)

/-- **From the fold over the flat list up to the sending of o_u** to a run of steps. -/
theorem FlatAt.stepTo2 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 3) d0 rs cl = .ok (s, rs', cl')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b] ++ rs' ∧ cl = cl' ∧ D.d2 = s ∧ StepTo2 B ft d0 W D := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have h' : foldBlocks ft [x0, x1, x2] d0 rs cl = .ok (s, rs', cl') := h
  have k := fold_like ft _ (frontBlock c :: [B.b1, B.b2]) (.cons l0 (.cons l1 (.cons l2 .nil))) _ _
    _ _ h'
  exact B.stepTo2_of_fold hU ft d0 s rs rs' cl cl' (peel_front c ft _ _ _ _ _ k)

/-- **From the fold over the flat list up to "(rec_gamma)"** to a run of steps. -/
theorem FlatAt.stepTo3 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 4) d0 rs cl = .ok (s, rs', cl')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b] ++ rs' ∧ cl = cl' ∧ D.d3 = s ∧ StepTo3 B ft d0 W D := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have h' : foldBlocks ft [x0, x1, x2, x3] d0 rs cl = .ok (s, rs', cl') := h
  have k := fold_like ft _ (frontBlock c :: [B.b1, B.b2, B.b3]) (.cons l0 (.cons l1 (.cons l2 (.cons
    l3 .nil)))) _ _ _ _ h'
  exact B.stepTo3_of_fold hU ft d0 s rs rs' cl cl' (peel_front c ft _ _ _ _ _ k)

/-- **From the fold over the flat list up to "LOC"** to a run of steps. -/
theorem FlatAt.stepTo4 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 5) d0 rs cl = .ok (s, rs', cl')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b, W.R4] ++ rs' ∧ cl = W.cs ++ cl' ∧ D.d4 = s ∧ StepTo4 B ft d0 W
      D := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have h' : foldBlocks ft [x0, x1, x2, x3, x4] d0 rs cl = .ok (s, rs', cl') := h
  have k := fold_like ft _ (frontBlock c :: [B.b1, B.b2, B.b3, B.b4]) (.cons l0 (.cons l1 (.cons l2
    (.cons l3 (.cons l4 .nil))))) _ _ _ _ h'
  exact B.stepTo4_of_fold hU ft d0 s rs rs' cl cl' (peel_front c ft _ _ _ _ _ k)

/-- **From the fold over the flat list up to the sending of o_omega and o_sp** to a run of steps. -/
theorem FlatAt.stepTo5 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 6) d0 rs cl = .ok (s, rs', cl')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b] ++ rs' ∧ cl = W.cs ++ cl' ∧ D.d5 = s ∧
      StepTo5 B ft d0 W D := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have h' : foldBlocks ft [x0, x1, x2, x3, x4, x5] d0 rs cl = .ok (s, rs', cl') := h
  have k := fold_like ft _ (frontBlock c :: [B.b1, B.b2, B.b3, B.b4, B.b5]) (.cons l0 (.cons l1
    (.cons l2 (.cons l3 (.cons l4 (.cons l5 .nil)))))) _ _ _ _ h'
  exact B.stepTo5_of_fold hU ft d0 s rs rs' cl cl' (peel_front c ft _ _ _ _ _ k)

/-- **From the fold over the flat list up to the joinings** to a run of steps. -/
theorem FlatAt.stepTo6 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 7) d0 rs cl = .ok (s, rs', cl')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b] ++ rs' ∧ cl = W.cs ++ cl' ∧ D.d6 = s ∧
      StepTo6 B ft d0 W D := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have h' : foldBlocks ft [x0, x1, x2, x3, x4, x5, x6] d0 rs cl = .ok (s, rs', cl') := h
  have k := fold_like ft _ (frontBlock c :: [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6]) (.cons l0 (.cons
    l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 .nil))))))) _ _ _ _ h'
  exact B.stepTo6_of_fold hU ft d0 s rs rs' cl cl' (peel_front c ft _ _ _ _ _ k)

/-- **From the fold over the flat list up to "LIN zeta"** to a run of steps. -/
theorem FlatAt.stepTo7 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 8) d0 rs cl = .ok (s, rs', cl')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7] ++ rs' ∧ cl = W.cs ++ cl' ∧ D.d7 = s
      ∧ StepTo7 B ft d0 W D := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have h' : foldBlocks ft [x0, x1, x2, x3, x4, x5, x6, x7] d0 rs cl = .ok (s, rs', cl') := h
  have k := fold_like ft _ (frontBlock c :: [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7]) (.cons l0
    (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7 .nil)))))))) _ _ _ _ h'
  exact B.stepTo7_of_fold hU ft d0 s rs rs' cl cl' (peel_front c ft _ _ _ _ _ k)

/-- **From the fold over the flat list up to "SPLIT"** to a run of steps. -/
theorem FlatAt.stepTo8 (F : FlatAt xs c B) (hU : withU P.S = some sentU)
    (hS : P.S.sharedSplitNeeded = true) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 9) d0 rs cl = .ok (s, rs', cl')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7, W.R8] ++ rs' ∧ cl = W.cs ++ cl' ∧
      D.d8 = s ∧ StepTo8 B ft d0 W D := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have h' : foldBlocks ft [x0, x1, x2, x3, x4, x5, x6, x7, x8] d0 rs cl = .ok (s, rs', cl') := h
  have k := fold_like ft _ (frontBlock c :: [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8]) (.cons
    l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7 (.cons l8 .nil)))))))))
    _ _ _ _ h'
  exact B.stepTo8_of_fold hU hS ft d0 s rs rs' cl cl' (peel_front c ft _ _ _ _ _ k)

/-! ## At one member: the fold in front of it, and its own step -/

/-- **At "LIN point"**: the fold over the members in front has returned s, with nothing left over,
and the member's own step has returned s' from s: so there is a run of steps up to it, whose last
two states are s and s'. -/
theorem FlatAt.member1 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s s' : St)
    (seen rs : List Fmt.RoundView) (cols0 cols : List OpenedColumn) (n : Nat) (blk : Block St Cl)
    (hm : foldBlocks ft (xs.take 1) d0 seen cols0 = .ok (s, [], [])) (hb : xs[1]? = some blk)
    (hs : blk.step ft s rs cols = .ok (s', n)) :
    ∃ W D, seen = [] ++ [] ∧ rs = [W.R1] ∧ cols0 = [] ∧ d0 = s ∧ D.d1 = s' ∧ StepTo1 B ft d0 W D :=
      by
  have hl := F.at1 hb
  rw [hl.step] at hs
  obtain ⟨rfl, rfl, rfl⟩ := F.start ft d0 s seen [] cols0 [] hm
  obtain ⟨R, rfl, rfl, _⟩ := B.back1 hU ft _ s' rs cols n hs
  exact ⟨⟨R, R, R, R, R, R, R, R, []⟩, { States8.fill d0 with d1 := s' }, rfl, rfl, rfl, rfl, rfl,
    ⟨⟨_, _, hs⟩⟩⟩

/-- **At the sending of o_u**: the fold over the members in front has returned s, with nothing left
over, and the member's own step has returned s' from s: so there is a run of steps up to it, whose
last two states are s and s'. -/
theorem FlatAt.member2 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s s' : St)
    (seen rs : List Fmt.RoundView) (cols0 cols : List OpenedColumn) (n : Nat) (blk : Block St Cl)
    (hm : foldBlocks ft (xs.take 2) d0 seen cols0 = .ok (s, [], [])) (hb : xs[2]? = some blk)
    (hs : blk.step ft s rs cols = .ok (s', n)) :
    ∃ W D, seen = [W.R1] ++ [] ∧ rs = [W.R2a, W.R2b] ∧ cols0 = [] ∧ D.d1 = s ∧ D.d2 = s' ∧ StepTo2 B
      ft d0 W D := by
  have hl := F.at2 hb
  rw [hl.step] at hs
  obtain ⟨W, D, hseen, hcols, rfl, u⟩ := F.stepTo1 hU ft d0 s seen [] cols0 [] hm
  obtain ⟨Ra, Rb, rfl, rfl, _⟩ := B.back2 hU ft _ s' rs cols n hs
  exact ⟨{ W with R2a := Ra, R2b := Rb }, { D with d2 := s' }, hseen, rfl, hcols, rfl, rfl, ⟨⟨u.s1⟩,
    ⟨_, _, hs⟩⟩⟩

/-- **At "(rec_gamma)"**: the fold over the members in front has returned s, with nothing left over,
and the member's own step has returned s' from s: so there is a run of steps up to it, whose last
two states are s and s'. -/
theorem FlatAt.member3 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s s' : St)
    (seen rs : List Fmt.RoundView) (cols0 cols : List OpenedColumn) (n : Nat) (blk : Block St Cl)
    (hm : foldBlocks ft (xs.take 3) d0 seen cols0 = .ok (s, [], [])) (hb : xs[3]? = some blk)
    (hs : blk.step ft s rs cols = .ok (s', n)) :
    ∃ W D, seen = [W.R1, W.R2a, W.R2b] ++ [] ∧ rs = [] ∧ cols0 = [] ∧ D.d2 = s ∧ D.d3 = s' ∧ StepTo3
      B ft d0 W D := by
  have hl := F.at3 hb
  rw [hl.step] at hs
  obtain ⟨W, D, hseen, hcols, rfl, u⟩ := F.stepTo2 hU ft d0 s seen [] cols0 [] hm
  obtain ⟨rfl, rfl, _⟩ := B.back3 hU ft _ s' rs cols n hs
  exact ⟨W, { D with d3 := s' }, hseen, rfl, hcols, rfl, rfl, ⟨⟨⟨u.front.s1⟩, u.s2⟩, ⟨_, _, hs⟩⟩⟩

/-- **At "LOC"**: the fold over the members in front has returned s, with nothing left over, and the
member's own step has returned s' from s: so there is a run of steps up to it, whose last two states
are s and s'. -/
theorem FlatAt.member4 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s s' : St)
    (seen rs : List Fmt.RoundView) (cols0 cols : List OpenedColumn) (n : Nat) (blk : Block St Cl)
    (hm : foldBlocks ft (xs.take 4) d0 seen cols0 = .ok (s, [], [])) (hb : xs[4]? = some blk)
    (hs : blk.step ft s rs cols = .ok (s', n)) :
    ∃ W D, seen = [W.R1, W.R2a, W.R2b] ++ [] ∧ rs = [W.R4] ∧ cols0 = [] ∧ W.cs = cols.take n ∧
      D.d3 = s ∧ D.d4 = s' ∧ StepTo4 B ft d0 W D := by
  have hl := F.at4 hb
  rw [hl.step] at hs
  obtain ⟨W, D, hseen, hcols, rfl, u⟩ := F.stepTo3 hU ft d0 s seen [] cols0 [] hm
  obtain ⟨R, rfl, _, _, hlen, _⟩ := B.back4 hU ft _ s' rs cols n hs
  have h4 : B.b4.step ft D.d3 [R] (cols.take n ++ cols.drop n) =
      .ok (s', (cols.take n).length) := by
    rw [List.take_append_drop, hlen]
    exact hs
  exact ⟨{ W with R4 := R, cs := cols.take n }, { D with d4 := s' }, hseen, rfl, hcols, rfl, rfl,
    rfl, ⟨⟨⟨⟨u.front.front.s1⟩, u.front.s2⟩, u.s3⟩, ⟨cols.drop n, h4⟩⟩⟩

/-- **At the sending of o_omega and o_sp**: the fold over the members in front has returned s, with
nothing left over, and the member's own step has returned s' from s: so there is a run of steps up
to it, whose last two states are s and s'. -/
theorem FlatAt.member5 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s s' : St)
    (seen rs : List Fmt.RoundView) (cols0 cols : List OpenedColumn) (n : Nat) (blk : Block St Cl)
    (hm : foldBlocks ft (xs.take 5) d0 seen cols0 = .ok (s, [], [])) (hb : xs[5]? = some blk)
    (hs : blk.step ft s rs cols = .ok (s', n)) :
    ∃ W D, seen = [W.R1, W.R2a, W.R2b, W.R4] ++ [] ∧ rs = [W.R5a, W.R5b] ∧ cols0 = W.cs ++ [] ∧
      D.d4 = s ∧ D.d5 = s' ∧ StepTo5 B ft d0 W D := by
  have hl := F.at5 hb
  rw [hl.step] at hs
  obtain ⟨W, D, hseen, hcols, rfl, u⟩ := F.stepTo4 hU ft d0 s seen [] cols0 [] hm
  obtain ⟨Ra, Rb, rfl, rfl, _⟩ := B.back5 hU ft _ s' rs cols n hs
  exact ⟨{ W with R5a := Ra, R5b := Rb }, { D with d5 := s' }, hseen, rfl, hcols, rfl, rfl,
    ⟨⟨⟨⟨⟨u.front.front.front.s1⟩, u.front.front.s2⟩, u.front.s3⟩, u.s4⟩, ⟨_, _, hs⟩⟩⟩

/-- **At the joinings**: the fold over the members in front has returned s, with nothing left over,
and the member's own step has returned s' from s: so there is a run of steps up to it, whose last
two states are s and s'. -/
theorem FlatAt.member6 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s s' : St)
    (seen rs : List Fmt.RoundView) (cols0 cols : List OpenedColumn) (n : Nat) (blk : Block St Cl)
    (hm : foldBlocks ft (xs.take 6) d0 seen cols0 = .ok (s, [], [])) (hb : xs[6]? = some blk)
    (hs : blk.step ft s rs cols = .ok (s', n)) :
    ∃ W D, seen = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b] ++ [] ∧ rs = [] ∧ cols0 = W.cs ++ [] ∧
      D.d5 = s ∧ D.d6 = s' ∧ StepTo6 B ft d0 W D := by
  have hl := F.at6 hb
  rw [hl.step] at hs
  obtain ⟨W, D, hseen, hcols, rfl, u⟩ := F.stepTo5 hU ft d0 s seen [] cols0 [] hm
  obtain ⟨rfl, rfl, _⟩ := B.back6 hU ft _ s' rs cols n hs
  exact ⟨W, { D with d6 := s' }, hseen, rfl, hcols, rfl, rfl, ⟨⟨⟨⟨⟨⟨u.front.front.front.front.s1⟩,
    u.front.front.front.s2⟩, u.front.front.s3⟩, u.front.s4⟩, u.s5⟩, ⟨_, _, hs⟩⟩⟩

/-- **At "LIN zeta"**: the fold over the members in front has returned s, with nothing left over,
and the member's own step has returned s' from s: so there is a run of steps up to it, whose last
two states are s and s'. -/
theorem FlatAt.member7 (F : FlatAt xs c B) (hU : withU P.S = some sentU) (ft : Nat) (d0 s s' : St)
    (seen rs : List Fmt.RoundView) (cols0 cols : List OpenedColumn) (n : Nat) (blk : Block St Cl)
    (hm : foldBlocks ft (xs.take 7) d0 seen cols0 = .ok (s, [], [])) (hb : xs[7]? = some blk)
    (hs : blk.step ft s rs cols = .ok (s', n)) :
    ∃ W D, seen = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b] ++ [] ∧ rs = [W.R7] ∧ cols0 = W.cs ++ []
      ∧ D.d6 = s ∧ D.d7 = s' ∧ StepTo7 B ft d0 W D := by
  have hl := F.at7 hb
  rw [hl.step] at hs
  obtain ⟨W, D, hseen, hcols, rfl, u⟩ := F.stepTo6 hU ft d0 s seen [] cols0 [] hm
  obtain ⟨R, rfl, rfl, _⟩ := B.back7 hU ft _ s' rs cols n hs
  exact ⟨{ W with R7 := R }, { D with d7 := s' }, hseen, rfl, hcols, rfl, rfl,
    ⟨⟨⟨⟨⟨⟨⟨u.front.front.front.front.front.s1⟩, u.front.front.front.front.s2⟩,
    u.front.front.front.s3⟩, u.front.front.s4⟩, u.front.s5⟩, u.s6⟩, ⟨_, _, hs⟩⟩⟩

/-- **At "SPLIT"**: the fold over the members in front has returned s, with nothing left over, and
the member's own step has returned s' from s: so there is a run of steps up to it, whose last two
states are s and s'. -/
theorem FlatAt.member8 (F : FlatAt xs c B) (hU : withU P.S = some sentU)
    (hS : P.S.sharedSplitNeeded = true) (ft : Nat) (d0 s s' : St)
    (seen rs : List Fmt.RoundView) (cols0 cols : List OpenedColumn) (n : Nat) (blk : Block St Cl)
    (hm : foldBlocks ft (xs.take 8) d0 seen cols0 = .ok (s, [], [])) (hb : xs[8]? = some blk)
    (hs : blk.step ft s rs cols = .ok (s', n)) :
    ∃ W D, seen = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7] ++ [] ∧ rs = [W.R8] ∧ cols0 = W.cs
      ++ [] ∧ D.d7 = s ∧ D.d8 = s' ∧ StepTo8 B ft d0 W D := by
  have hl := F.at8 hb
  rw [hl.step] at hs
  obtain ⟨W, D, hseen, hcols, rfl, u⟩ := F.stepTo7 hU ft d0 s seen [] cols0 [] hm
  obtain ⟨R, rfl, rfl, _⟩ := B.back8 hU hS ft _ s' rs cols n hs
  exact ⟨{ W with R8 := R }, { D with d8 := s' }, hseen, rfl, hcols, rfl, rfl,
    ⟨⟨⟨⟨⟨⟨⟨⟨u.front.front.front.front.front.front.s1⟩, u.front.front.front.front.front.s2⟩,
    u.front.front.front.front.s3⟩, u.front.front.front.s4⟩, u.front.front.s5⟩, u.front.s6⟩, u.s7⟩,
    ⟨_, _, hs⟩⟩⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.Like.step
#print axioms Desc.K14.Honest.fold_like
#print axioms Desc.K14.Honest.step_retype
#print axioms Desc.K14.Honest.fold_retype
#print axioms Desc.K14.Honest.peel_front
#print axioms Desc.K14.Honest.peel_frontOf
#print axioms Desc.K14.Honest.FlatAt.start
#print axioms Desc.K14.Honest.StepTo1.more
#print axioms Desc.K14.Honest.StepTo2.more
#print axioms Desc.K14.Honest.StepTo3.more
#print axioms Desc.K14.Honest.StepTo4.more
#print axioms Desc.K14.Honest.StepTo5.more
#print axioms Desc.K14.Honest.StepTo6.more
#print axioms Desc.K14.Honest.StepTo7.more
#print axioms Desc.K14.Honest.FlatAt.stepTo1
#print axioms Desc.K14.Honest.FlatAt.stepTo2
#print axioms Desc.K14.Honest.FlatAt.stepTo3
#print axioms Desc.K14.Honest.FlatAt.stepTo4
#print axioms Desc.K14.Honest.FlatAt.stepTo5
#print axioms Desc.K14.Honest.FlatAt.stepTo6
#print axioms Desc.K14.Honest.FlatAt.stepTo7
#print axioms Desc.K14.Honest.FlatAt.stepTo8
#print axioms Desc.K14.Honest.FlatAt.member1
#print axioms Desc.K14.Honest.FlatAt.member2
#print axioms Desc.K14.Honest.FlatAt.member3
#print axioms Desc.K14.Honest.FlatAt.member4
#print axioms Desc.K14.Honest.FlatAt.member5
#print axioms Desc.K14.Honest.FlatAt.member6
#print axioms Desc.K14.Honest.FlatAt.member7
#print axioms Desc.K14.Honest.FlatAt.member8
