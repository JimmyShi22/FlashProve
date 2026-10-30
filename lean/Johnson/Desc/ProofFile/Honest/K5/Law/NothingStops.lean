-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/NothingStops.lean: the honest side of the attention
sub-protocol's own rounds (the kind K5) never stops: no part of its row has a stop, so the frame's
function `chainStopAt` (Johnson/Desc/ProofFile/Honest/Rule.lean) answers `none` at the kind's member,
at every input, at all challenges. No definition; seven theorems. No coin and no input is read: a
part's two stops are functions of the challenges and of what the second stop may see, and here both
are the constant `none`.

  `stopAt_none`        a part whose two stops always answer `none` does not stop. General.
                       The same law stands in Honest/K3/Law/Thread/StandAtMember.lean, by the
                       writers of the lookup's rounds (sub-protocol K3); it is stated again here so
                       that this file need not stand over that kind's own files.
                       Both general laws of this file stand also in E2E/NoStop.lean
                       (AtPublicFiles.Stops.stopAt_none, under its definition Quiet, and
                       AtPublicFiles.Stops.rowStopAt_none); that file stands over far more of the library than
                       this one.
  `rowStopAt_none`     a list of such parts does not stop. General
  `stopAt_bites`       a negative test: a part of one round whose first stop answers is reported as
                       stopping: so the function can say so
  `k5Row_no_stop`      no part of the kind's row has a stop
  `k5Half_no_stop`     no part of the kind's half has a stop
  `k5Half_never_stops` the half's list of parts does not stop
  `k5_nothing_stops`   where the kind's half stands at a thread's member (`K5Seated`,
                       Honest/K5/Law/Seated.lean): `chainStopAt v [blk] T.hs loc ds = none`

What it is for. "The side does not stop" is a premise of the frame's forms `Plays` and `Accepted`
(Honest/Thread/Pays.lean). `k5_nothing_stops` is that premise, at every thread at which the kind's
half is seated. Of `K5Seated` the field half alone is spent.

How. The row is made of three makers of parts: `sumPart` (Honest/Sum.lean), `quietPart` and
`scalarsPart` (Honest/ForKinds.lean): each writes both stops as the constant `none`. `Part.lift`
(Honest/Frame.lean) keeps the first stop and reads the second through a function.

Limits. It says that no stop fires: not that a play returns, and nothing on what is played. This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.ProofFile.Honest.K5.Law.Seated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First.Att (P.Par P.rounds)
open H2K5.Honest (K5In PartShape shapes)

/-! ## 1 General -/

section
variable {V W X : Type}

/-- A part whose two stops always answer `none` does not stop. -/
theorem stopAt_none (q : Part V W X) (hb : ∀ a c, q.bad a c = none)
    (hh : ∀ u a c, q.hid u a c = none) (v : Option V) (loc ds : List Fmt.Drawn) :
    q.stopAt v loc ds = none := by
  unfold Part.stopAt
  refine List.findSome?_eq_none_iff.2 fun j _ => ?_
  have h2 : (v.bind fun u => q.hid u loc (ds.take j)) = none := by
    cases v with
    | none => rfl
    | some u => exact hh u _ _
  rw [hb, h2]
  rfl

/-- A list of such parts does not stop. -/
theorem rowStopAt_none (ps : List (Part V W X))
    (H : ∀ q ∈ ps, (∀ a c, q.bad a c = none) ∧ ∀ u a c, q.hid u a c = none) (v : Option V)
    (loc ds : List Fmt.Drawn) : rowStopAt v ps loc ds = none := by
  induction ps generalizing loc ds with
  | nil => rfl
  | cons q qs ih =>
    show (q.stopAt v loc (ds.take q.moves.length)).or
      (rowStopAt v qs (loc ++ ds.take q.moves.length) (ds.drop q.moves.length)) = none
    rw [stopAt_none q (H q (List.mem_cons_self ..)).1 (H q (List.mem_cons_self ..)).2,
      ih fun r hr => H r (List.mem_cons_of_mem _ hr)]
    rfl

end

/-- A negative test: a part of one round whose first stop answers is reported as stopping. -/
theorem stopAt_bites :
    ({ (quietPart 1 : Part Unit Unit Unit) with bad := fun _ _ => some "stop" }).stopAt none [] [] =
      some .bad := rfl

/-! ## 2 The kind's row and half -/

/-- No part of the kind's row has a stop. -/
theorem k5Row_no_stop (Z : Seat5) :
    ∀ q ∈ k5Row Z, (∀ a c, q.bad a c = none) ∧ ∀ u a c, q.hid u a c = none := by
  intro q hq
  unfold k5Row rowOf at hq
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hq
  obtain ⟨sh, i⟩ := s
  cases sh with
  | sum k => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  | one n =>
    cases n with
    | zero => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
    | succ n => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

section
variable {W₀ Rc Xi Tr X : Type}

/-- No part of the kind's half has a stop. -/
theorem k5Half_no_stop (cells : Tr → Cells) (Z : Seat5) :
    ∀ q ∈ (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts,
      (∀ a c, q.bad a c = none) ∧ ∀ u a c, q.hid u a c = none := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  exact ⟨fun a c => (k5Row_no_stop Z p hp).1 a c, fun _ a c => (k5Row_no_stop Z p hp).2 _ a c⟩

/-- The half's list of parts does not stop. -/
theorem k5Half_never_stops (cells : Tr → Cells) (Z : Seat5) (v : Option (Local W₀ Rc Xi Tr))
    (loc ds : List Fmt.Drawn) :
    rowStopAt v (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts loc ds = none :=
  rowStopAt_none _ (k5Half_no_stop cells Z) v loc ds

end

/-! ## 3 At a thread's member -/

section
variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}

/-- **Nothing stops at the kind's member.** Conditional: Hs: the kind's half stands at the member; of
it the field half alone is spent. -/
theorem k5_nothing_stops
    {T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
    {cells : Tr → Cells} {Z : Seat5} {p : P.Par} {blk : Block S Cl}
    (Hs : K5Seated T b cells Z p blk) (v : Option (Local W₀ Rc Xi Tr))
    (loc ds : List Fmt.Drawn) : chainStopAt v [blk] T.hs loc ds = none := by
  show ((T.hs.find? fun h => h.place == blk.place).bind fun h =>
      rowStopAt v h.parts loc (ds.take blk.rounds.length)).or
    (chainStopAt v [] T.hs (loc ++ ds.take blk.rounds.length) (ds.drop blk.rounds.length)) = none
  rw [Hs.half]
  show (rowStopAt v (k5Half cells Z).parts loc (ds.take blk.rounds.length)).or none = none
  rw [k5Half_never_stops]
  rfl

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.stopAt_none
#print axioms ProofFile.Honest.K5.rowStopAt_none
#print axioms ProofFile.Honest.K5.stopAt_bites
#print axioms ProofFile.Honest.K5.k5Row_no_stop
#print axioms ProofFile.Honest.K5.k5Half_no_stop
#print axioms ProofFile.Honest.K5.k5Half_never_stops
#print axioms ProofFile.Honest.K5.k5_nothing_stops
