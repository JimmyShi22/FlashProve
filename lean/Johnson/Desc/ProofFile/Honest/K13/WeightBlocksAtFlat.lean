-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/WeightBlocksAtFlat.lean: kind K13, the members' batching: OF WHAT
FORM THE WEIGHTS OF THE ROW ON THE TABLE ARE AT THE END OF THE PROOF FILE's OWN FIRST CHAIN, IN THE
GOALS' SCOPE: there is one row, and its weights are vectors that the library's `stretchBlocks`
returns at stretches that end at or below the matrix's rows, each times an element. Two statements
with their proofs; no definition. OF THE VERIFIER's OWN FOLD ALONE: no prover, no instance, no
filler is named.

The two sentences, (plain) and (scaled): WeightBlocks.lean (Johnson/Desc/K13/Honest/); they are
written out here at the shape Z.first.lin. The rows on the table: the library's `S.rows`
(Johnson/Desc/First/State.lean): the pile in front of the batching; behind it the one row, read off
the claim.
Main names:
  `plain_by_number`: a decision of a sub-protocol of a number below 355 keeps "(plain) at each row".
    By `rows_by_number` (PileWalkAtFlat.lean of this folder): the rows stay, or the verifier's own
    row is laid at their end; that row has (plain) by `pendingRowO_blocks`.
  `rows_at_end`: **behind the fold over the whole chain, from a state with no row on the table:
    there is one row on the table, and it has (scaled).** What is carried from border to border: up
    to number 355 "(plain) at each row"; behind it "one row, with (scaled)". The last three
    sub-protocols by the library's `IM.at_355`, `at_356`, `at_357` (Johnson/IMR/LastFour.lean):
    number 355 is K13's batching (`atM3_ok`, then `batt_blocks`); number 356 leaves the rows
    (`atM4_pile`, Johnson/Desc/First/Pile/PileSeated.lean); number 357 returns the state that it is
    handed.

The premises, all four on public data: hS, hR: the public files are in the goals' scope and are
read; O: the maker's opening (`IM.Open`, Johnson/IMR/SeatOpen.lean); hp: each sub-protocol of the
chain passes its test on the plan. And h0: the first state has no row on the table: at the chain's
own start that is the library's `LPFK9.start_rows` (Johnson/LPFK9R/MasksByPlace.lean).

Nearest kin in the library: `LPFK9.PileLawZ` and `fold_rides` (Johnson/LPFK9R/PileByPlace.lean): a
sentence P at every state that a fold over a front stretch of this chain returns. It is not spent
here: its field `push` asks that P ride over the laying of a row made at EVERY shape, and (plain) is
at one; its field `batch` asks that P pass the batching, and the sentence turns there. Its
`fold_ix` is the fold's rule at decisions; `IM.at_355` and its two sisters want the step: so
`foldStepsAt` (FoldCut.lean, Johnson/Desc/K13/Honest/). `last_three`
(Johnson/Desc/AtSeats/LastThree.lean) says the like of a step that reads all its columns
(`StepYes`): the fold's step is not given in that form.

Limits. The goals' scope alone (the full size). The fold is at first tree 0, the first chain's own.
The statement is conditional on the fold's return: where it rejects nothing is said. The shape is
Z.first.lin: that a later sub-protocol asks its test at this shape is not said here. It speaks of
`S.rows`, not of the field `out.pending`.

What is not claimed. That the fold returns anywhere. Anything on the values, the column point, the
mask form or the target. That a weight can be cut below the matrix's rows. It is none of the
library's goals. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.PileWalkAtFlat
import Johnson.Desc.K13.Honest.WeightBlocks
import Johnson.IMR.LastFour
import Johnson.Desc.First.Pile.PileSeated
import Johnson.Desc.Last.IndexAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.K13.Honest (foldStepsAt pendingRowO_blocks batt_blocks)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Law (rowBy_some)

variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **A decision of a number below 355 keeps "(plain) at each row".** -/
theorem plain_by_number (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (k : Nat) (hk : k < 355) (blk : Block S Cl)
    (hb : c.blocksInOrder[k]? = some blk) (s t : S) (R : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : blk.decide s R gs = .ok t)
    (hI : ∀ row ∈ s.rows,
      ∃ (firstRow : ℕ) (values : Array E),
        firstRow + values.size ≤ Z.first.lin.matrixRows ∧
          row.g =
            stretchBlocks Z.first.lin.kRow firstRow values (2 * Z.first.lin.kRow + 2) firstRow) :
    ∀ row ∈ t.rows,
      ∃ (firstRow : ℕ) (values : Array E),
        firstRow + values.size ≤ Z.first.lin.matrixRows ∧
          row.g =
            stretchBlocks Z.first.lin.kRow firstRow values (2 * Z.first.lin.kRow + 2) firstRow := by
  intro row hrow
  rcases rows_by_number hS hR O hp k hk blk hb s t R gs hd with ⟨σ, _, _, r, hr, e⟩ | ⟨_, e⟩
  · rw [e] at hrow
    rcases List.mem_append.1 hrow with h1 | h1
    · exact hI row h1
    · obtain rfl := List.mem_singleton.1 h1
      obtain ⟨w, os, _, hq⟩ := rowBy_some.1 hr
      exact pendingRowO_blocks hq
  · rw [e] at hrow
    exact hI row hrow

/-- **AT THE CHAIN's END: ONE ROW ON THE TABLE, WITH (scaled)**, behind the verifier's own fold over
the whole chain, from a state with no row on the table. -/
theorem rows_at_end (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (s₀ : S) (h0 : s₀.rows = []) :
    ∀ rs cols s r cl, foldBlocks 0 c.blocksInOrder s₀ rs cols = .ok (s, r, cl) →
      ∃ row, s.rows = [row] ∧ ∀ w ∈ row.g,
        ∃ (firstRow : ℕ) (values : Array E) (fuel start : ℕ) (x : E),
          firstRow + values.size ≤ Z.first.lin.matrixRows ∧
            ∃ t ∈ stretchBlocks Z.first.lin.kRow firstRow values fuel start, w = t.scale x := by
  intro rs cols s r cl hf
  have hlen : c.blocksInOrder.length = 358 := VerifiableInference.Desc.Last.flat_358 hS hR O
  have key := foldStepsAt 0 c.blocksInOrder
    (fun k s =>
      (k ≤ 355 → ∀ row ∈ s.rows,
        ∃ (firstRow : ℕ) (values : Array E),
          firstRow + values.size ≤ Z.first.lin.matrixRows ∧
            row.g =
              stretchBlocks Z.first.lin.kRow firstRow values (2 * Z.first.lin.kRow + 2) firstRow) ∧
      (355 < k → ∃ row, s.rows = [row] ∧ ∀ w ∈ row.g,
        ∃ (firstRow : ℕ) (values : Array E) (fuel start : ℕ) (x : E),
          firstRow + values.size ≤ Z.first.lin.matrixRows ∧
            ∃ t ∈ stretchBlocks Z.first.lin.kRow firstRow values fuel start, w = t.scale x))
    s₀ rs cols (s, r, cl)
    (by
      intro j blk hb s c' t n _ _ hstep hI
      have hj : j < 358 := hlen ▸ (List.getElem?_eq_some_iff.1 hb).1
      by_cases h1 : j < 355
      · obtain ⟨gs, hdec⟩ := stepOk hstep
        exact ⟨fun _ => plain_by_number hS hR O hp j h1 blk hb s t _ gs hdec (hI.1 (by omega)),
          fun h => absurd h (by omega)⟩
      · refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
        obtain rfl | rfl | rfl : j = 355 ∨ j = 356 ∨ j = 357 := by omega
        · obtain ⟨⟨rs', gs, y⟩, -, -⟩ := IM.at_355 hS hR O hb hstep
          obtain ⟨out, hbt, e, e'⟩ := VerifiableInference.Desc.K13.Law.atM3_ok y
          have hq := hI.1 (Nat.le_refl _)
          rw [e] at hq
          exact ⟨out.1, e', batt_blocks _ hbt hq⟩
        · obtain ⟨row, e, h⟩ := hI.2 (by omega)
          obtain ⟨w, hw, ⟨rs', gs, y⟩, -, -⟩ := IM.at_356 hS hR O hb hstep
          obtain ⟨P', rfl⟩ : ∃ P', w = VerifiableInference.Desc.K1.sendAtS P' := by
            unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
            obtain ⟨msg, _, e'⟩ := Option.map_eq_some_iff.1 hw
            exact ⟨_, e'.symm⟩
          exact ⟨row, by rw [((Meaning.K2.atM4_pile _ P').1 s rs' gs t y).1, e], h⟩
        · obtain ⟨row, e, h⟩ := hI.2 (by omega)
          exact ⟨row, by rw [IM.at_357 hS hR O hb hstep, e], h⟩)
    hf
    ⟨fun _ row hrow => absurd (h0 ▸ hrow) List.not_mem_nil, fun h => absurd h (Nat.not_lt_zero _)⟩
  rw [hlen] at key
  exact key.2 (by omega)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.plain_by_number
#print axioms ProofFile.Honest.K13.rows_at_end
