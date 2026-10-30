--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/RowThrough.lean: the honest side of the sub-protocol "the
output head's own rounds" (kind K6), read through a pair of maps on the prover's input, is that same
honest side at the composed reader. The online honest prover's filling reads every lot through such a
pair (`OnlineProverParts.through`, Honest/ThruK13.lean). What follows: a law of this folder that is general in the
reader of the small input and in the two types can be read at the composed reader, and the parts there
are the parts read through. The equations are on parts, prover's sides and lots. Simulators, On and bud
are not read through: they read no input, and `headSimulatorLot` sets the same ones at every reader.
That a filling lays this lot is not said here.

What it is not. Equations between definitions. No law on a distribution, nothing on what a part
plays, nothing on soundness, completeness or hiding.

  `headWit_through`        the small input at an input read through: the reader of the index composed;
                           the stored tables' randomness is not read
  `headRow_through`        the eight parts read through are the eight parts at the composed reader
  `headHalf_through`       the same for the prover's side at a place
  `headLot_through`        the same for the lot as a filling holds it, with its reader by public part
  `headSimulatorLot`       the lot's rows with their simulators, at a reader by public part
  `headSimulatorLot_toHLot`, `headSimulatorLot_through`   without its simulators it is the lot that a
                           filling holds; and the lot that a filling read through holds
-/
import Johnson.Desc.ProofFile.Honest.Thru
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt
import Johnson.Desc.ProofFile.Honest.K6.Law.RowsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Kinds (Head.Par)

variable {W₀ W₀' Rc Rc' Tr X : Type}

/-- **The small input at an input read through.** The index is read through `g`; `rd` is not read:
the small input holds nothing of the stored tables' pads and encoding randomness. -/
theorem headWit_through (g : W₀' → W₀) (rd : Rc' → Rc) (cells : Tr → Cells)
    (weights : W₀ → Weights) (Z : Pub) (G : Ground) (w : Local W₀' Rc' Inst Tr) :
    headWit' cells weights Z G (Local.thru g rd w) = headWit' cells (weights ∘ g) Z G w := rfl

/-- **The eight parts read through are the eight parts at the composed reader.** -/
theorem headRow_through (g : W₀' → W₀) (rd : Rc' → Rc) (wit : Local W₀ Rc Inst Tr → HeadAsk)
    (p : Head.Par) (at_ : Place) :
    (headRow (X := X) wit p at_).map (Part.thru (Local.thru g rd) (Local.thru g rd)) =
      headRow (wit ∘ Local.thru g rd) p at_ := by
  unfold headRow
  rw [List.map_map]
  refine List.map_congr_left fun q _ => ?_
  exact Part.lift_thru (Local.thru g rd) (Local.thru g rd) (fun _ => ()) wit (fun _ => ())
    (fun x _ => x) q

/-- The same for the prover's side at a place. -/
theorem headHalf_through (g : W₀' → W₀) (rd : Rc' → Rc) (wit : Local W₀ Rc Inst Tr → HeadAsk)
    (p : Head.Par) (at_ : Place) :
    Placed.thru (Local.thru g rd) (Local.thru g rd) (⟨at_, headRow (X := X) wit p at_⟩) =
      ⟨at_, headRow (wit ∘ Local.thru g rd) p at_⟩ :=
  congrArg (Placed.mk at_) (headRow_through g rd wit p at_)

/-- **The lot as a filling holds it, read through, is that lot at the composed reader.** -/
theorem headLot_through (g : W₀' → W₀) (rd : Rc' → Rc) (weights : Pub → W₀ → Weights) :
    HLot.thru (Local.thru g rd) (Local.thru g rd)
        (HLot.byPub weights fun wt =>
          (headLot headFitsB (headWit' id wt) :
            HLot (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X)) =
      HLot.byPub (fun Z w => weights Z (g w)) fun wt => headLot headFitsB (headWit' id wt) := by
  refine HLot.ext' rfl ?_
  funext Z G
  show ((headLot headFitsB (headWit' id (weights Z))).halves Z G).map _ =
    (headLot headFitsB (headWit' id fun w => weights Z (g w))).halves Z G
  unfold headLot
  by_cases h : headFitsB Z G = true
  · simp only [h, if_true, List.map_map]
    refine List.map_congr_left fun b _ => ?_
    exact headHalf_through g rd (headWit' id (weights Z) Z G) (headParAt G) b.place
  · simp only [h, if_false, Bool.false_eq_true, List.map_nil]

/-- **The lot's rows with their simulators, at a reader of the index that may depend on the public
part**: at each public part the rows of `headSLotAt` (Honest/K6/Law/RowsIn.lean). The name is taken as
`HLot.byPub` takes it. -/
def headSimulatorLot (weights : Pub → W₀ → Weights) :
    SLot (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X Inst :=
  { name := (headSLotAt (W₀ := W₀) (Rc := Rc) (X := X) id
      fun _ => ⟨fun _ _ => OnBytes.Slice.toF 0⟩).name
    rows := fun Z G => (headSLotAt id (weights Z)).rows Z G }

/-- **Without its simulators it is the lot that a filling holds.** -/
theorem headSimulatorLot_toHLot (weights : Pub → W₀ → Weights) :
    (headSimulatorLot (Rc := Rc) (X := X) weights).toHLot =
      HLot.byPub weights fun wt => headLot headFitsB (headWit' id wt) := by
  refine HLot.ext' rfl ?_
  funext Z G
  exact congrFun (congrFun (congrArg HLot.halves
    (headSLotAt_toHLot (Rc := Rc) (X := X) id (weights Z))) Z) G

/-- **And the lot that a filling read through holds.** -/
theorem headSimulatorLot_through (g : W₀' → W₀) (rd : Rc' → Rc) (weights : Pub → W₀ → Weights) :
    (headSimulatorLot (Rc := Rc') (X := X) fun Z w => weights Z (g w)).toHLot =
      HLot.thru (Local.thru g rd) (Local.thru g rd)
        (HLot.byPub weights fun wt =>
          (headLot headFitsB (headWit' id wt) :
            HLot (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X)) :=
  (headSimulatorLot_toHLot _).trans (headLot_through g rd weights).symm

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headWit_through
#print axioms ProofFile.Honest.K6.headRow_through
#print axioms ProofFile.Honest.K6.headHalf_through
#print axioms ProofFile.Honest.K6.headLot_through
#print axioms ProofFile.Honest.K6.headSimulatorLot
#print axioms ProofFile.Honest.K6.headSimulatorLot_toHLot
#print axioms ProofFile.Honest.K6.headSimulatorLot_through
