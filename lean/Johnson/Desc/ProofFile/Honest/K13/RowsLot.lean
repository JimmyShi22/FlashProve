-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/RowsLot.lean: kind K13, the members' batching: the kind's lot with
its simulators, as a value of `SLot` (Honest/Thread/Rows.lean): the lot's parts, each with its
simulator, and the conditions `On` and `bud`; and the equation that ties it to the kind's lot of
prover's sides (`k13Lot`, Part.lean of this folder). Three definitions; two statements with their
proofs. General in the reader of the index, the filler of the pile and all types named.

  `k13On`, `k13Bud`   the kind's `On` and `bud`: both ask nothing (True)
  `k13SLot`   one row, at the kind's place: `k13Pairs` (Part.lean: the two parts of `k13Row`, each
     with its simulator of `k13Sims`: `quietSim` beside the part that sends nothing, `sumSim` beside
     the sumcheck's part), `k13On`, `k13Bud`
  `k13_row_sims`   the row has two parts and two simulators (`List.zip` would cut to the shorter
     list in silence)
  `k13SLot_toHLot`   with the simulators, `On` and `bud` forgotten it is `k13Lot`

Why. The frame's rule for a file (`file_owed_rows`) and `laySides` (Honest/Thread/Rows.lean) take
lists of rows. A list of lots reaches them through `rowsOfLots`, and `halves_of_lots` there says
that the prover's sides of these rows are `firstOf` at the lots with the simulators forgotten.
Whoever lays a filling's own list of lots as such a list needs, lot by lot, the equation that for
this kind is `k13SLot_toHLot`.

That `On` and `bud` ask nothing cuts two ways. The rule's hypotheses on them hold trivially. But a
statement at this row has nothing in hand from them: `exact` and `fresh` are asked at every state,
every `front` and every list of read positions. They hold there (Exact.lean and Fields.lean of this
folder; at the proof file's description and book: GoodRows.lean of this folder). At each part that
a run has called, `Lettered.owedAt` (Honest/Rule.lean) still asks that the carried blocks are lent
and that the run has a state before the part.

Limits.
  * At the row `k13Row` alone: the row that keeps its tables (`k13RowKeep`, KeepJob.lean of this
    folder) has no such value here.
  * The place is the proof file's (`whereOf Z`).
  * `k13SLot_toHLot` ends at `k13Lot weights pile`. That a given filling lays that lot, read through
    whatever the filling wraps around it, is not shown here; AtFill.lean of this folder shows it at
    one filling.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc.K13 (whereOf)

variable {V W W₀ Rc Xi Tr X Pb : Type}

/-- The kind's `On`: it asks nothing. -/
def k13On (u : Member V W X Pb) (_ : CsAll u.part.carries) (_ : Mid W X) (_ : Before) : Prop := True

/-- The kind's `bud`: it asks nothing. -/
def k13Bud (_ : Nat) (_ : List Fmt.Drawn) (_ : List (List (List Nat))) : Prop := True

/-- **The kind's rows, each part with its simulator, with the kind's `On` and `bud`**, under the
lot's own name: one row, at the kind's place. -/
def k13SLot (weights : W₀ → Weights) (pile : Pub → Ground → PileOf Xi) :
    SLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb :=
  { name := "K13: the members' batching"
    rows := fun Z G =>
      [⟨k13Place (whereOf Z), k13Pairs weights (pile Z G) (whereOf Z), k13On, k13Bud⟩] }

/-- The row has as many simulators as parts: two. -/
theorem k13_row_sims (weights : W₀ → Weights) (pile : PileOf Xi)
    (p : VerifiableInference.Desc.K13.Where) :
    (k13Row (Rc := Rc) (Tr := Tr) (X := X) weights pile p).length = 2 ∧
      (k13Sims (Pb := Pb) p).length = 2 := ⟨rfl, rfl⟩

/-- **The equation**: with the simulators, `On` and `bud` forgotten it is the kind's lot of prover's
sides. -/
theorem k13SLot_toHLot (weights : W₀ → Weights) (pile : Pub → Ground → PileOf Xi) :
    (k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) weights pile).toHLot =
      k13Lot weights pile := by
  unfold SLot.toHLot k13SLot k13Lot
  congr 1

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13On
#print axioms ProofFile.Honest.K13.k13Bud
#print axioms ProofFile.Honest.K13.k13SLot
#print axioms ProofFile.Honest.K13.k13_row_sims
#print axioms ProofFile.Honest.K13.k13SLot_toHLot
