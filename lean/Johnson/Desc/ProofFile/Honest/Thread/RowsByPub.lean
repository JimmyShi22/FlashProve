-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/RowsByPub.lean: a lot's lists (`SLot`, Honest/Thread/Rows.lean)
whose reader of the index depends on the public part, or whose data of the main rows depends on the
public part and the ground: the twins, for `SLot`, of `HLot.byPub` (Honest/AtPureWiderAt.lean) and
`HLot.byRows` (Honest/AtPureWider.lean). General in every type; no kind is named.

  `SLot.byPub`          the lists of `L (weights Z)` at Z; the name at the reader that is 0
  `SLot.byRows`         the lists of `L (D Z G)` at Z and G; the name at the empty data
  `SLot.byPub_toHLot`   with simulators, On and bud forgotten, the first is `HLot.byPub`
  `SLot.byRows_toHLot`  the same of the second and `HLot.byRows`
  `SLot.byPub_rows`, `SLot.byRows_rows`   the lists at a public part and a ground

Why. The fillings `widerFill…` lay most kinds' lots under `HLot.byPub`, one also under
`HLot.byRows`. Whoever wants a filling's field `lots` in the form `ls.map SLot.toHLot` (the premise
of `halves_of_lots`, Honest/Thread/Rows.lean) has to write each kind's `SLot` in the same way. With
the two equations a kind's own equation `(L wt).toHLot = …`, at every reader wt, is enough.

Limits.
  * Two definitions and four equations by unfolding. No value of `SLot` is defined here, and none is
    shown to be a filling's.
  * The lists are carried as they are: nothing is said of a simulator, of On or of bud.
  * The name is taken at one fixed argument, as in the two definitions for `HLot`: where L's name
    depends on its argument, the name here is the one at that argument.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Rows
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W₀ V W Y Pb Xi : Type}

/-- **A lot's lists whose reader of the index depends on the public part.** `L`: the lists, from a
reader. The name is taken at the reader that is 0 everywhere, as `HLot.byPub` takes it. -/
def SLot.byPub (weights : Pub → W₀ → Weights) (L : (W₀ → Weights) → SLot V W Y Pb) :
    SLot V W Y Pb :=
  { name := (L fun _ => ⟨fun _ _ => OnBytes.Slice.toF 0⟩).name
    rows := fun Z G => (L (weights Z)).rows Z G }

/-- **A lot's lists whose data of the main rows depends on the public part and the ground.** `L`:
the lists, from the data. The name is taken at the empty data, as `HLot.byRows` takes it. -/
def SLot.byRows (D : Pub → Ground → RowDataOf Xi) (L : RowDataOf Xi → SLot V W Y Pb) :
    SLot V W Y Pb :=
  { name := (L fun _ => RowData.empty).name
    rows := fun Z G => (L (D Z G)).rows Z G }

/-- Its lists at a public part and a ground are L's at the reader there. -/
theorem SLot.byPub_rows (weights : Pub → W₀ → Weights) (L : (W₀ → Weights) → SLot V W Y Pb)
    (Z : Pub) (G : Ground) : (SLot.byPub weights L).rows Z G = (L (weights Z)).rows Z G := rfl

/-- Its lists at a public part and a ground are L's at the data there. -/
theorem SLot.byRows_rows (D : Pub → Ground → RowDataOf Xi) (L : RowDataOf Xi → SLot V W Y Pb)
    (Z : Pub) (G : Ground) : (SLot.byRows D L).rows Z G = (L (D Z G)).rows Z G := rfl

/-- **Forgetting commutes with `byPub`.** -/
theorem SLot.byPub_toHLot (weights : Pub → W₀ → Weights) (L : (W₀ → Weights) → SLot V W Y Pb) :
    (SLot.byPub weights L).toHLot = HLot.byPub weights fun wt => (L wt).toHLot := rfl

/-- **Forgetting commutes with `byRows`.** -/
theorem SLot.byRows_toHLot (D : Pub → Ground → RowDataOf Xi) (L : RowDataOf Xi → SLot V W Y Pb) :
    (SLot.byRows D L).toHLot = HLot.byRows D fun d => (L d).toHLot := rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.SLot.byPub_rows
#print axioms ProofFile.Honest.SLot.byRows_rows
#print axioms ProofFile.Honest.SLot.byPub_toHLot
#print axioms ProofFile.Honest.SLot.byRows_toHLot
