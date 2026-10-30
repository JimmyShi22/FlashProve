-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ListsReached.lean: AT EVERY STATE THAT IS REACHED IN FRONT OF THE SUB-PROTOCOLS
BEHIND THE LAST LINK OF THE PROOF FILE's OWN FIRST CHAIN THE STATEMENT IS TIDY (ListsTidy.lean): a
message's list names just the groups that hold it, each once. And the tool for a property that holds
from a border on: along one run, what the plain changes keep goes from the state at border j to the
state at border k. At an opening's own letters (IM.Open, Johnson/IMR/SeatOpen.lean); whoever plays.

How. The library's walk (open_front, open_fold, Johnson/IMR/OpenWalk.lean) at the relation that
StKeeps carries (seatKeeps_by, Johnson/Desc/AtSeats/StatementSeat.lean); at the start there is no
message (startS_facts) and no group (start_groups, Johnson/IMR/GroupAt.lean).

  plain_reached: a property that the plain changes keep and that holds at every first state holds at
    every such reached state. tidy_reached: so Tidy.
  tidy_fold: the same of a fold's return.
  plain_folds: j ≤ k: of two folds from one state over the same rounds and columns, over the first j
    and the first k sub-protocols: the property goes from the first's return to the second's.

Limits. Of a reached state: that anything is reached is not said. Nothing on soundness, completeness
or hiding.
-/
import Johnson.AtFull.Shape.ListsTidy
import Johnson.Desc.AtSeats.StatementSeat
import Johnson.IMR.OpenWalk
import Johnson.IMR.GroupAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription foldBlocks Keeps.foldBlocks_split
  Keeps.foldBlocks_keeps)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.K2 (frontOf open_front open_fold seatKeeps_by startS_facts start_groups flat_eq ByS)
open ProofFile (Cl)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {P : Statement → Prop}

/-- **From the start.** -/
theorem plain_reached (K : PlainKeeps P) (O : IM.Open o pol lay KL F Z Bs base c A B)
    (h0 : ∀ z, P (ProofFile.startS Z z).st) {k : Nat} {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hk : k ≤ (frontOf c).length) : P s.st := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  exact open_fold (seatKeeps_by (stKeeps_of K)) O trivial (fun _ _ _ => trivial) hk f (h0 z)

/-- **The statement is tidy at every state that is reached in front of the sub-protocols behind the
last link** (k ≤ (frontOf c).length). -/
theorem tidy_reached (O : IM.Open o pol lay KL F Z Bs base c A B) {k : Nat} {z : ProofFile.InstPub}
    {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hk : k ≤ (frontOf c).length) :
    Tidy s.st :=
  plain_reached plain_tidy O
    (fun z => tidy_start (startS_facts O.pub z).2.1 (start_groups O.pub z)) h hk

/-- The same of a fold's return. -/
theorem tidy_fold (O : IM.Open o pol lay KL F Z Bs base c A B) {k : Nat}
    (hk : k ≤ (frontOf c).length) {z : ProofFile.InstPub} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z z) rs cols = .ok r) : Tidy r.1.st :=
  open_fold (seatKeeps_by stKeeps_tidy) O trivial (fun _ _ _ => trivial) hk f
    (tidy_start (startS_facts O.pub z).2.1 (start_groups O.pub z))

/-- **From the first j to the first k sub-protocols, along one run.** -/
theorem plain_folds (K : PlainKeeps P) (O : IM.Open o pol lay KL F Z Bs base c A B) {j k : Nat}
    (hjk : j ≤ k) (hk : k ≤ (frontOf c).length) {s₀ : S} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    {a r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (fj : foldBlocks 0 (c.blocksInOrder.take j) s₀ rs cols = .ok a)
    (fk : foldBlocks 0 (c.blocksInOrder.take k) s₀ rs cols = .ok r) : P a.1.st → P r.1.st := by
  have e : c.blocksInOrder.take j ++ (c.blocksInOrder.take k).drop j = c.blocksInOrder.take k := by
    have q := List.take_append_drop j (c.blocksInOrder.take k)
    rwa [List.take_take, Nat.min_eq_left hjk] at q
  rw [← e] at fk
  obtain ⟨t, R, C, g0, g1⟩ := Keeps.foldBlocks_split 0 _ _ _ _ _ _ fk
  rw [fj] at g0
  obtain rfl : a = (t, R, C) := Except.ok.inj g0
  have H := seatKeeps_by (stKeeps_of K)
  obtain ⟨h0, Kb⟩ := open_front H O trivial (fun _ _ _ => trivial)
  refine Keeps.foldBlocks_keeps (ByS (Stays P)) H.refl H.trans 0 _ (fun b hb => Kb b ?_) t R C _ g1
  have hb' := List.mem_of_mem_drop hb
  rw [flat_eq h0, List.take_append_of_le_length hk] at hb'
  exact List.mem_of_mem_take hb'

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.plain_reached
#print axioms Johnson.AtFull.Shape.tidy_reached
#print axioms Johnson.AtFull.Shape.tidy_fold
#print axioms Johnson.AtFull.Shape.plain_folds
