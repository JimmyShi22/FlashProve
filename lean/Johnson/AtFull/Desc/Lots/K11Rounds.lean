-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K11Rounds.lean: THE SECOND ROW OF THE MERGE's LOT (`K11.lot`,
Johnson/Desc/ProofFile/Lot/K11.lean: the merge of the claims on the committed table) FOR AN EXAMPLE
OF THE PROOF FILE's IOP AS WRITTEN IN LEAN, AT THE FULL SIZE: ITS CORE: the lot's one block sits at
the place ⟨1, some 24, 9, .K11⟩, and its declared rounds are the list that the written table
`listAt` (Johnson/AtFull/Rounds/ListAt.lean) bears at the name "H:9". Under three hypotheses by
field; the closed facts by Lean's kernel. Definitions, statements and proofs. The first row, on the
block's skeleton, is Johnson/AtFull/Desc/Lots/K11Row.lean.

What it says.
  `roundsOn lk n work`: the kind's declared rounds (`mergeEntries`,
    Johnson/Desc/First/Fork/MergeKind.lean) from three numbers.
  `rounds_blkAt`, `place_blkAt`: at every public part Z and all segments' structures G the block's
    rounds read two numbers of G (the committed table's number of column bits; the setting's bits of
    proof of work in front of a field's challenge in a request's own rounds), its place one (how
    many segments are built). Of Z they read nothing.
  `blocks_one`: the lot returns that one block. `no_batch`: it supplies no batching at any place.
  By the kernel: `rounds_written`: at 18 column bits, one claim and no proof of work the rounds are
    `listAt "H:9"`; `rounds_22`: that list has 22 rounds.
  Negative tests, by the kernel, each with one thing altered: `rounds_not_work` (one bit of proof
    of work), `rounds_not_two` (two claims: one word of one round), `rounds_not_17` (one column bit
    less), `rounds_not_next` (the next place's name).
  `k11_rounds_at`: THE CORE OF THE ROW: where 25 segments are built, the table has 18 column bits
    and the setting asks no proof of work there: every block of the lot sits at that place and its
    rounds are `listAt "H:9"`.

Limits. THAT ANY SEGMENTS' STRUCTURES HAVE THE THREE NUMBERS IS SHOWN NOWHERE HERE: hb, hk and hw
are premises (Johnson/AtFull/Desc/Lots/K11RoundsScope.lean pays them in the goals' scope). THAT
"H:9" IS THE NAME OF THE PLACE ⟨1, some 24, 9, .K11⟩, IN ANY LIST OF PLACES, IS NOT SAID HERE: that
is another file's closed fact, and the step from this core to the row in that file's form is a file
of its own. `listAt` is a written value of one set of public files, with synthetic weights, made by
a program off a print of Lean's evaluator: `rounds_written` holds a maker against that text; it does
not show that any files give these values. No law at an opening and none under the proof file's pins
is spent.
May be idle: no example of the head is shown in this
file; two, at storedPublicFiles and at zGap alone, are AtFullSide.Top.headMember_zFull and headMember_zGap,
whose own Limits say what they are worth. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.LotIs
import Johnson.AtFull.Rounds.ListAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K11Rounds

open VerifiableInference.Desc (Place KindName)
open Johnson.Desc.First.ForkMerge (mergeEntries)
open Johnson.AtFull.Rounds (listAt)

/-! ## 1 What the block's rounds and place read -/

/-- The kind's declared rounds, from the number of column bits, the number of claims and the bits of
proof of work. -/
def roundsOn (lk n work : Nat) : List Fmt.DeclaredRound :=
  (mergeEntries lk n work).map fun e => { entry := e }

/-- **The rounds of the lot's block read two numbers of G, and nothing of Z.** -/
theorem rounds_blkAt (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (K11.blkAt Z "H.8.call" G).rounds =
      roundsOn G.W.layers.wsLay.lk 1
        ((OnBytes.Params.settingOf G.W.P.frame).workOf .field .request) :=
  (K11.blkAt_fields Z G).2.1

/-- Its place reads how many segments are built. -/
theorem place_blkAt (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (K11.blkAt Z "H.8.call" G).place = ⟨1, some (G.built.size - 1), 9, .K11⟩ :=
  (K11.blkAt_fields Z G).2.2.2.2.1

/-- The lot returns one block. -/
theorem blocks_one (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (K11.lot Z).blocks G = [K11.blkAt Z "H.8.call" G] := by
  unfold ProofFile.Lot.blocks ProofFile.asCl
  rw [(K11.lot_lays Z G).1, (K11.lot_lays Z G).2.1]
  rfl

/-- The lot supplies no batching: a premise on what a lot's batching makes asks nothing of it. -/
theorem no_batch (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) : (K11.lot Z).batch G a = none := rfl

/-! ## 2 The closed facts -/

/-- The place of the merge where 25 segments are built. -/
def placeW : Place := ⟨1, some 24, 9, .K11⟩

set_option maxRecDepth 1000000 in
/-- **At the written numbers the rounds are the table's list at "H:9".** -/
theorem rounds_written : roundsOn 18 1 0 = listAt "H:9" := by decide +kernel

set_option maxRecDepth 1000000 in
/-- That list has 22 rounds: it is not the empty list. -/
theorem rounds_22 : (listAt "H:9").length = 22 := by decide +kernel

/-! ## 3 Negative tests, by the kernel -/

set_option maxRecDepth 1000000 in
/-- One bit of proof of work: as many rounds, the same names; 21 rounds differ in one word. -/
theorem rounds_not_work : roundsOn 18 1 1 ≠ listAt "H:9" := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Two claims: one word of the first round differs. -/
theorem rounds_not_two : roundsOn 18 2 0 ≠ listAt "H:9" := by decide +kernel

set_option maxRecDepth 1000000 in
/-- One column bit less: 21 rounds. -/
theorem rounds_not_17 : roundsOn 17 1 0 ≠ listAt "H:9" := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At the next place's name the table bears another list. -/
theorem rounds_not_next : roundsOn 18 1 0 ≠ listAt "H:10" := by decide +kernel

/-! ## 4 The core of the row -/

/-- **Every block of the lot sits at that place, and its rounds are the table's list at "H:9".** -/
theorem k11_rounds_at {Z : ProofFile.Pub} {G : ProofFile.Ground} (hb : G.built.size = 25)
    (hk : G.W.layers.wsLay.lk = 18)
    (hw : (OnBytes.Params.settingOf G.W.P.frame).workOf .field .request = 0) :
    ∀ b ∈ (K11.lot Z).blocks G, b.place = placeW ∧ b.rounds = listAt "H:9" := by
  intro b hbm
  rw [blocks_one] at hbm
  obtain rfl := List.mem_singleton.1 hbm
  refine ⟨?_, ?_⟩
  · rw [place_blkAt, hb]
    rfl
  · rw [rounds_blkAt, hk, hw]
    exact rounds_written

end Johnson.AtFull.Lots.K11Rounds

#print axioms Johnson.AtFull.Lots.K11Rounds.rounds_blkAt
#print axioms Johnson.AtFull.Lots.K11Rounds.place_blkAt
#print axioms Johnson.AtFull.Lots.K11Rounds.blocks_one
#print axioms Johnson.AtFull.Lots.K11Rounds.no_batch
#print axioms Johnson.AtFull.Lots.K11Rounds.rounds_written
#print axioms Johnson.AtFull.Lots.K11Rounds.rounds_22
#print axioms Johnson.AtFull.Lots.K11Rounds.rounds_not_work
#print axioms Johnson.AtFull.Lots.K11Rounds.rounds_not_two
#print axioms Johnson.AtFull.Lots.K11Rounds.rounds_not_17
#print axioms Johnson.AtFull.Lots.K11Rounds.rounds_not_next
#print axioms Johnson.AtFull.Lots.K11Rounds.k11_rounds_at
