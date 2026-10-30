-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/ReaderOf.lean: "THE READER IS THE RUN ITSELF": ONE GENERIC MAKE OF THE
READERS OF Johnson/Desc/First/Batch/FormsIn.lean, out of what the segment's blocks state.
Definitions with code. No Mathlib.
  `lateOf F G`: the slots that are free in the ledger F and filled in the ledger G, with what G
    holds under them.
  `readerOf states b name s`: the run that block number b states under that name, looked up as
    `runsBy` looks a run up, CALLED AT THE RECORD s, handed 0 claims in front: its claims' forms,
    and late := `lateOf` (s's ledger) (the ledger behind the run). NOTHING where no such run is
    stated, where it refuses, where no segment is open, WHERE A CLAIM IS MORE THAN A FORM (it has
    runs of entries, or an index of equations: the smallness test's equations: their reader is
    another), or WHERE AN ENTRY NAMES A VIRTUAL ROW THAT IS NOT PLAINLY THE ARRAY's OWN (`ownRow`).
  `ownRow F x`: the entry x names row 0 of an array that has, in the ledger F, one own row.
  `lateOk_lateOf`: at the ledger behind the run the reader's late slots hold just what it says.
  `Readers.ofStates`: the readers of a segment; "piece" is the driver's block number, from 0.
Limits: (1) THAT THE RUN GIVES ONE LIST AT EVERY BORDER AT WHICH ITS ITEM IS OPEN IS NOT SAID: it is
to be shown of each kind's run. (2) The claims' forms name VIRTUAL rows; read as forms over
the arrays' own rows they say the same only where the virtual row is the own row. `ownRow` asks that
the array has one own row and that the entry names row 0; THAT THIS VIRTUAL ROW's ONE WEIGHT IS 1 IS
NOT ASKED: the weights are laid behind the batching. (3) A run that reads the number of claims in
front of it is read at 0. (4) `lateOf`'s list has each slot once (it goes through the slots' numbers
in order); `lateAt` (Johnson/Desc/First/Batch/FormsIn.lean) takes the first entry for a slot,
whatever list it is given. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.FormsIn
import Johnson.Desc.First.Batch.Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- The slots that are free in F and filled in G, with what G holds under them. -/
def lateOf (F G : Fork) : List (Nat × E × E) :=
  (List.range G.ns).filterMap fun j =>
    if !(F.gotF.getD j false) && G.gotF.getD j false then
      some (j, G.vp.getD j zeroE, G.mf.getD j zeroE) else none

/-- At the ledger behind the run the late slots hold just what the list says. -/
theorem lateOk_lateOf (F : Fork) (a : Part) : lateOk (lateOf F a.F) a = true := by
  unfold lateOk
  refine List.all_eq_true.2 fun x hx => ?_
  unfold lateOf at hx
  obtain ⟨j, hj, hx'⟩ := List.mem_filterMap.1 hx
  by_cases hc : (!(F.gotF.getD j false) && a.F.gotF.getD j false) = true
  · rw [if_pos hc] at hx'
    obtain rfl := Option.some.inj hx'
    simp [List.mem_range.1 hj]
  · rw [if_neg hc] at hx'
    exact nomatch hx'

/-- The entry names row 0 of an array that has one own row in the ledger. -/
def ownRow (F : Fork) (x : Ent) : Bool :=
  match F.trees[x.tree]? with
  | some T => T.R == 1 && x.row == 0
  | none => false

/-- **The reader is the run itself.** -/
def readerOf (states : Nat → List (RunOf S)) (b : Nat) (name : String) (s : S) : Option Read :=
  ((states b).find? fun r => r.1 == name).bind fun r =>
    match r.2 0 s, s.fork? with
    | .ok z, some F =>
      (z.2.fork?).bind fun G =>
        if z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F) then
          some { forms := z.1.map (·.form), late := lateOf F G } else none
    | _, _ => none

/-- The readers of a segment, out of what its blocks state. -/
def Readers.ofStates (states : Nat → List (RunOf S)) : Readers := ⟨readerOf states⟩

end VerifiableInference.Desc.K9
