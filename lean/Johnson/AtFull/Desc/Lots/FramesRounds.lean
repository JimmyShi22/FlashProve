-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/FramesRounds.lean: THE FRAMES' LOT DECLARES NO ROUND: every sub-protocol
(`Block`) of `ProofFile.framesLot Z` (Johnson/Desc/ProofFile/Lots/PureLots.lean) has `rounds = []`. The
first four statements are general laws: at every public part Z and every G, with no premise, and
nothing is evaluated. The fifth and the sixth are closed facts on written data.

Why. The rounds that a proof file's IOP as written in Lean declares are its sub-protocols' own, laid
end to end. To show that they are the written list, it is said of each lot's sub-protocols what
their rounds are. The frames' lot has three for each segment (the field `link` of a place): "lay",
"opened", "clear"; or, where its maker fails, one that rejects. None has a round.

  `frames_rounds`       every sub-protocol of the lot has `rounds = []`
  `frames_rounds_at`    so what holds of every name and no round holds of every name and the rounds
                        of a sub-protocol of the lot: the form of `ProofFile.Sk.base_good`'s premise on
                        the lots (Johnson/Desc/ProofFile/Law/Skel/SkelRoundsParts.lean: not imported
                        here), at each Q
  `frames_rounds_flat`  the lot's sub-protocols, laid end to end, declare nothing
  `frames_no_batching`  the lot supplies no batching, at any place
  `cut_frames`          a closed fact on written data, decided by Lean's kernel: the written cut of
                        the first chain has 77 rows of the kind `frame`; one alone, "seal:5",
                        counts a round, and it stands in no segment
  `cut_frames_but_last` the same count with one thing turned: without the cut's last row, no row of
                        the kind `frame` counts a round
  two `example`s        tests of fit, from the above: `base_good`'s premise on the lots' rounds, to
                        the letter, at this lot; and, from the antecedent of its premise on the
                        batchings at this lot, any conclusion (that premise itself is not written
                        here: it names a function of a file that is not imported)

What is called. `P1K2.blocksOf_quiet` (Johnson/P1K2R/SitsStep.lean): nothing in `P1L20.blocksOf Z`
has a round. `IM.blocks_mem` (Johnson/IMR/LotKinds.lean): what is in `Lot.blocks` is in `own`,
carried to the type of claims, or in `hearC`.

Limits. Of the lot's sub-protocols alone. How many they are is not said here (FramesRow.lean, beside
this file: 75 at the written shape, under six premises). THE ROW "seal:5" IS NOT THIS LOT's: nothing
is said here of its round, nor of the rows "start:0" and "behind the batching", which this lot does
not lay either. No theorem says that the written cut's rows are those of the IOP at the stored
public files (CutLit.lean's own head). No example of the verifier's state after its entry tests is
given here. No soundness statement.

-/
import Johnson.P1K2R.SitsStep
import Johnson.IMR.LotKinds
import Johnson.Desc.ProofFile.Lots.PureLots
import Johnson.Desc.ProofFile.OnlineDescriptionFromBlockTables
import Johnson.Desc.Ok.PlanWritten.CutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1L20.Row

open ProofFile (Pub Ground Cl framesLot)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (cutFirstFull)

/-- **Every sub-protocol of the frames' lot has `rounds = []`.** -/
theorem frames_rounds (Z : Pub) (G : Ground) (b : Block S Cl) (hb : b ∈ (framesLot Z).blocks G) :
    b.rounds = [] := by
  rcases IM.blocks_mem hb with ⟨x, hx, rfl⟩ | hb
  · exact P1K2.blocksOf_quiet Z x hx
  · exact nomatch hb

/-- What holds of every name and no round holds of every name and the rounds of a sub-protocol of
the frames' lot. -/
theorem frames_rounds_at {Q : String → List Fmt.DeclaredRound → Prop}
    (hQ : ∀ n, Q n []) (Z : Pub) (G : Ground) (b : Block S Cl)
    (hb : b ∈ (framesLot Z).blocks G) (n : String) : Q n b.rounds := by
  rw [frames_rounds Z G b hb]
  exact hQ n

/-- The lot's sub-protocols, laid end to end, declare nothing. -/
theorem frames_rounds_flat (Z : Pub) (G : Ground) :
    ((framesLot Z).blocks G).flatMap (·.rounds) = [] := by
  rw [List.flatMap_eq_nil_iff]
  exact fun b hb => frames_rounds Z G b hb

/-- The lot supplies no batching. -/
theorem frames_no_batching (Z : Pub) (G : Ground) (a : Place) : (framesLot Z).batch G a = none :=
  rfl

/-- On written data: the first chain's written cut has 77 rows of the kind `frame`; one alone counts
a round, and it stands in no segment. -/
theorem cut_frames :
    (cutFirstFull.filter fun r => r.2.1.kind == KindName.frame).length = 77 ∧
      ((cutFirstFull.filter fun r => r.2.1.kind == KindName.frame && r.2.2.1 != 0).map
        fun r => (r.1, r.2.1.link, r.2.2.1)) = [("seal:5", none, 1)] := by
  decide +kernel

/-- The same count with one thing turned: without the cut's last row, no row of the kind `frame`
counts a round. -/
theorem cut_frames_but_last :
    ((cutFirstFull.dropLast.filter fun r => r.2.1.kind == KindName.frame && r.2.2.1 != 0).map
      fun r => r.1) = [] := by
  decide +kernel

/-! ### Two tests of fit for `ProofFile.Sk.base_good`'s two premises, at this lot (see the head) -/

example {Q : String → List Fmt.DeclaredRound → Prop} (hQ : ∀ n, Q n []) (Z : Pub) (B : ProofFile.PureBase) :
    ∀ b ∈ (framesLot Z).blocks B.G₀, ∀ p ∈ B.spots, p.place = b.place → Q p.name b.rounds :=
  fun b hb p _ _ => frames_rounds_at hQ Z B.G₀ b hb p.name

example {P : (ProofFile.Gatherer → Block S Cl) → Prop} (Z : Pub) (B : ProofFile.PureBase) :
    ∀ a mk, (framesLot Z).batch B.G₀ a = some mk → P mk :=
  fun a mk h => by
    rw [frames_no_batching] at h
    cases h

end P1L20.Row

#print axioms P1L20.Row.frames_rounds
#print axioms P1L20.Row.frames_rounds_at
#print axioms P1L20.Row.frames_rounds_flat
#print axioms P1L20.Row.frames_no_batching
#print axioms P1L20.Row.cut_frames
#print axioms P1L20.Row.cut_frames_but_last
