-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/FunsTree.lean: EVERY TABLE IN THE LIST THAT K4's HEARING RETURNS (o.funs) BEARS THE
NUMBER tree = 2 (the reads: the third of the vectors U1 to U3, counted from 0), in every group.
Three statements, each theorems of other files written out: `funs_shapes`
(OnBytes/Tie/Pv/Tail/ShapesLay.lean), whose second half says it of every return of `Layer.funsOf`;
the last clause of `hear_public` (OnBytes/Desc/First/K4/HearPublic.lean): where `hear` returns,
o.funs is a return of `funsOf`; and `heard_reads` (Johnson/Desc/First/K4/ReadsAtS.lean): behind a
yes of K4's block at the carried record the record's reader funs? finds o.funs.

  `funsOf_tree`: where `funsOf` returns funs: every member of funs has tree = 2.
  `funs_tree_of_hear`: where `hear` returns o: every member of o.funs has tree = 2.
  `funs_tree_atS`: behind a yes of `(blockAtS p).decide`: the record's reader `funs?` finds a list,
    and every member of it has tree = 2.

Limits. One field of a table alone: nothing on its matrix, its length, its weights or its first
entry. One direction: from a return or a yes. No premise but that. That the list is still what
`funs?` finds at a later border: K4's three runs leave it (`front_funs`, `back_funs`,
`freeSlot_funs`, ReadsAtS.lean); of other kinds' blocks nothing is said.
-/
import OnBytes.Tie.Pv.Tail.ShapesLay
import OnBytes.Desc.First.K4.HearPublic
import Johnson.Desc.First.K4.ReadsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Layer (Lay Pub HPlan2 Own TableAsk funsOf)
open OnBytes.Desc.First.K4 (Par engFl hear hear_public blockAtS heard_reads)
open VerifiableInference.Desc.First (S)

/-- Every table that `funsOf` returns lies in the reads. -/
theorem funsOf_tree {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {laid : List (TableAsk × List (Nat × Nat))} {funs : Array HFun}
    (h : funsOf y fo pt laid = some funs) : ∀ Fn ∈ funs, Fn.tree = 2 :=
  fun Fn hFn => (OnBytes.Tie.Pv.Tail.Closed.funs_shapes h).2 Fn (Array.mem_def.mp hFn)

/-- **Every table in the list that K4's hearing returns lies in the reads**, in every group. -/
theorem funs_tree_of_hear {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) :
    ∀ Fn ∈ o.funs, Fn.tree = 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hf⟩ := hear_public h
  exact funsOf_tree hf

/-- **Behind a yes of K4's block at the carried record the reader `funs?` finds a list of tables
that lie in the reads.** -/
theorem funs_tree_atS {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs cols = .ok s') :
    ∃ funs, s'.funs? = some funs ∧ ∀ Fn ∈ funs, Fn.tree = 2 := by
  obtain ⟨_, _, o, _, _, _, hh, _, h2, _⟩ := heard_reads h
  exact ⟨o.funs, h2, funs_tree_of_hear hh⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.funsOf_tree
#print axioms OnBytes.Road.K4.funs_tree_of_hear
#print axioms OnBytes.Road.K4.funs_tree_atS
