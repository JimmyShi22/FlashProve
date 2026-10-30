-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SLot.lean.

What is here. The rows of the layers' own rounds (kind K4) as a lot of rows with their simulators
(`SLot`, Honest/Thread/Rows.lean): a definition; and one equation: by forgetting the simulators it
is the kind's lot of halves (`k4HLot`, Honest/K4/Part.lean). A definition, a statement on lists and
its proof.

Limits. On lists alone: no statement here is on a law of coins, on the playing or on what the
verifier accepts. On and bud are True at every row: whoever states `Good` at such a row states its
fields exact and fresh at every state in front of a part and at all positions. At the G of a return of
the base maker `KindPays … .K4` holds, for every K with K4's slot: `kindPays_K4_at_theGOfReturn`
(Honest/K4/Law/ExactFresh/KindPaysAtTheG.lean): THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW;
A' := B' := False.
The rows are code but for the parameters cells, weights and
look, which a caller lays. A place for which `k4PubOf` yields nothing, or at which `k4TableFits` is
false, has no row: as in `k4HLot`.
No property is claimed.

  `k4Unlettered`   one row: K4's place, K4's parts with their simulators, On := bud := True.
  `k4SLot`         the lot.
  `k4Row_le_sims`  the row has no more parts than there are simulators.
  `k4Unlettered_half`, `k4SLot_toHLot`   **by forgetting it is `k4HLot`.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.Desc.ProofFile.Honest.Thread.RowsMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest

variable {W₀ Rc Tr X : Type}

/-- **One row without letters**: K4's place, K4's parts each with its simulator; On and bud are
True. -/
def k4Unlettered (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub) :
    Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst :=
  ⟨k4Place Q, k4Sided Q cells weights k4Tokens (look Q), fun _ _ _ _ => True, fun _ _ _ => True⟩

/-- **The lot's rows**: a row at each place at which `k4HLot` lays a half. -/
def k4SLot (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    SLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst :=
  { name := "K4"
    rows := fun Z G => (k4From Z G G.built.toList 0 none).filterMap fun x =>
      ((k4PubOf Z x.2).filter k4TableFits).map (k4Unlettered cells weights (look Z G)) }

/-- The row has no more parts than there are simulators: both are made of `k4Sorts`. -/
theorem k4Row_le_sims (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Inst → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    (k4Row (Rc := Rc) (X := X) Q cells weights tokens look).length ≤
      (k4Sims (Xi := Inst) Q).length := by
  unfold k4Row k4RowIn k4Sims k4Sorts
  cases (Q.g == 0) <;> exact Nat.le_refl _

/-- A row's half is the kind's half. -/
theorem k4Unlettered_half (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub) :
    (k4Unlettered (Rc := Rc) (X := X) cells weights look Q).half =
      k4Half cells weights k4Tokens look Q :=
  half_of_zip _ _ _ _ _ (k4Row_le_sims Q cells weights k4Tokens (look Q))

/-- **By forgetting the simulators, On and bud, the lot is `k4HLot`.** -/
theorem k4SLot_toHLot (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    (k4SLot (Rc := Rc) (X := X) cells weights look).toHLot = k4HLot cells weights look := by
  unfold SLot.toHLot k4SLot k4HLot
  congr 1
  funext Z G
  rw [List.map_filterMap]
  congr 1
  funext x
  rw [Option.map_map]
  congr 1
  funext Q
  exact k4Unlettered_half cells weights (look Z G) Q

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Row_le_sims
#print axioms ProofFile.Honest.K4.k4Unlettered_half
#print axioms ProofFile.Honest.K4.k4SLot_toHLot
