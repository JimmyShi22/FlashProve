-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/CondsOfLaid.lean: the one named condition in front of the head of the closed
constant, `P5J.At.Conds Z` (Johnson/P5J/AtNameA.lean: fifteen tests with code, at whatever letters
the laid value opens), from "in scope", "`protocolDataWellFormed` accepts", "the files are read" and ONE condition
on the three public files alone. It compiles over the proof file's entry tests (`LPFD.lawsAsk`), a
list of fourteen rows.
One definition, seven theorems with their proofs. It proves none of the fifteen itself: it calls
each one's theorem.

Why. `sound_of_kinds_at` (Johnson/Goal/Skeleton/SoundOfKindsAtZ.lean) takes `At.Conds Z` as a named
condition. The verifier itself asks two comparisons of the plan
with written values ("pins"): rows 9 and 10, `madeRow` and `cutRow`. `LaidAt.asks` says that every
entry test accepts. So under `LaidAt` in scope the two pins accept (`pins_of_laid`,
Johnson/Goal/Skeleton/PinsOfLaid.lean), and whatever follows from them is no condition.

Main names. Z: three public files. Zp Np cF: the letters that a laid value opens.
  `At.CondsOwed Z`: THE ONE CONDITION BESIDE THE SCOPE, THE LIVE TEST AND THE READING: one field:
    `rows`: `rowsRead Z`
    (Johnson/Goal/Skeleton/RowsRead.lean: the second reading of the three public files returns, with
    one radius a shape).
  `written_of_laid`: in scope, under `LaidAt`: the request's shape and the plan's seats are the
    written ones.
  `nine_of_laid`: in scope, where `protocolDataWellFormed` accepts, the files read, under `LaidAt` at the format's
    second hash function: `rowsRead Z` gives `At.Nine Z Zp Np cF`.
  `conds_of_laid`: in scope, where `protocolDataWellFormed` accepts, the files read: `At.CondsOwed Z → At.Conds Z`.
  `tlB_is`, `armB_is`, `whereB_is`, `laidB_is`: four tests' texts as the files that prove them spell
  them
    are the tests, by definition.

The fifteen, each with its proof.
  `namedThere`    `Meaning.NamedAsk.namedThere_of_pinned`   from the first pin
  `seatsNamedC`   `P5J.seatsNamedC_at_name`                 from the first pin
  `seatsFitP`     `P5T.seatsFit_at_name`                    from both pins
  `endsThere`     `P5J.At.ends_at`                          from `LaidAt` alone, no pin
  `radIsB`        `P5J.At.radii_of_read`                    from `LaidAt` and `rowsRead Z`, no pin
  `headAt`'s      `P5J.At.head_at`                          from `LaidAt` in scope, no pin
  `fullShapeB`    `P5J.fullShape_at_name`                   from the first pin
  `builtB`        `P5J.built_at_name`                       from `LaidAt` in scope, no pin
  `tlB`           `P5J.tlB_at_name`                         from the first pin
  `armB`          `P5J.armB_at_name`                        from the first pin
  `whereB`        `P5J.whereB_at_name`                      from `LaidAt` in scope, no pin
  `spotsB`        `P5J.At.spotsB_of_rowsRead`               from `LaidAt` in scope and `rowsRead Z`
  `wholeB`        `P1M2.wholeB_of_laid`                     from `LaidAt` alone, no pin
  `laidB`         `P5J.laidB_at_name`                       from the first pin
  `k3SeatsB`      `P5J.k3SeatsB_of_two` (four of its six tests at each segment, from the first pin)
                  over `P1Opts.k3SomeB_at_written` (the other two: from `protocolDataWellFormed`, `LaidAt`,
                  `rowsRead Z` and the two equations of `written_of_laid`)

Limits. `rowsRead Z` IS NOT SHOWN HERE TO HOLD AT ANY Z, AND IT IS NO TEST THAT THE VERIFIER RUNS
(the fourteenth entry test asks its like, and `P5J.owed_of_live`, OwedOfLive.lean,
has `At.CondsOwed Z` from the live test's yes). IT IS NOT ONE OF THE FIFTEEN AND DOES NOT FOLLOW
FROM THEM: it stands for what four of them read beside the planner that the verifier runs. Whether a
value is laid at any Z under the entry tests' rows (fourteen) is
not shown here: where none is laid `At.Conds Z` asks nothing. The full size alone.
Nothing on soundness.

-/
import Johnson.P5J.AtNameA
import Johnson.LPFE1R.EndsAt
import Johnson.LPFE1R.RadiiAt
import Johnson.LPFE1R.HeadAt
import Johnson.P5T.SeatsFitWritten
import Johnson.HB.LLHARD.SeatsNamedFull
import Johnson.HB.LLHARD.FullShapeAtName
import Johnson.HB.LLHARD.OptsTlArm
import Johnson.HB.LLHARD.K3SeatsFour
import Johnson.HB.LLHARD.BuiltAtName
import Johnson.HB.LLHARD.OptsWhereLaid
import Johnson.Top.H0.Opts.WholeOfLaid
import Johnson.Top.H0.Opts.SpotsOfRowsRead
import Johnson.Top.H0.Opts.K3SomeB
import Johnson.Goal.Meaning.NamedAtPinned
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.Goal.Skeleton.K3Some

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- The text of `At.tlB` as the file that proves it spells it is the test. -/
theorem tlB_is (Zp : ProofFile.Pub) : At.tlB Zp = tlText Zp := rfl

/-- The text of `At.armB` as the file that proves it spells it is the test. -/
theorem armB_is (Zp : ProofFile.Pub) : At.armB Zp = armText Zp := rfl

/-- The text of `At.whereB` as the file that proves it spells it is the test. -/
theorem whereB_is (Zp : ProofFile.Pub) : At.whereB Zp = whereText Zp := rfl

/-- The text of `At.laidB` as the file that proves it spells it is the test. -/
theorem laidB_is (Zp : ProofFile.Pub) : At.laidB Zp = laidText Zp := rfl

/-- **The one condition beside the scope, the live test and the reading**: on the three public
files. -/
structure At.CondsOwed (Z : VerifierAndGoals.PublicFiles) : Prop where
  rows : rowsRead Z

/-- In scope, under "laid", the request's shape and the plan's seats are the written ones. -/
theorem written_of_laid {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    At.shape Zp = VerifiableInference.PlanWritten.proofSizedFull.request ∧
      At.pseats Zp = P5T.psFull := by
  have hy := (pins_of_laid hZ L).1
  have hv := LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks
  exact ⟨(VerifiableInference.PlanWritten.Joined.first_written_in_scope hZ L.pub hy).2.2.1,
    (P5T.seats_in_scope hZ L.pub hy hv).1⟩

/-- In scope, where `protocolDataWellFormed` accepts, under "laid", the one condition gives the fifteen. -/
theorem nine_of_laid {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (hrr : rowsRead Z) :
    At.Nine Z Zp Np cF := by
  obtain ⟨hy, hc⟩ := pins_of_laid hZ L
  obtain ⟨hS, hp⟩ := written_of_laid hZ L
  exact ⟨⟨Meaning.NamedAsk.namedThere_of_pinned hZ hR L.pub hy, seatsNamedC_at_name hZ hR L hy,
      P5T.seatsFit_at_name hZ hR L hy hc, At.ends_at L, At.radii_of_read L hrr⟩,
    At.head_at hZ hR L, fullShape_at_name hZ hR L hy,
    ⟨built_at_name hZ hR L, (tlB_is Zp).trans (tlB_at_name hZ hR L hy),
      (armB_is Zp).trans (armB_at_name hZ hR L hy), (whereB_is Zp).trans (whereB_at_name hZ hR L),
      At.spotsB_of_rowsRead hZ hR L hrr, P1M2.wholeB_of_laid L,
      (laidB_is Zp).trans (laidB_at_name hZ hR L hy)⟩,
    k3SeatsB_of_two hZ hR L hy (P1Opts.k3SomeB_at_written hl L hrr hS hp)⟩

/-- **`At.Conds Z` FROM THE SCOPE, THE LIVE TEST, THE LAID VALUE AND THE ONE CONDITION.** -/
theorem conds_of_laid {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hZ : VerifierAndGoals.InScope Z = true)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) (hR : VerifierAndGoals.readFiles Z = .ok pp) (T : At.CondsOwed Z) :
    At.Conds Z :=
  fun _ _ _ L => nine_of_laid hZ hl hR L T.rows

end P5J

#print axioms P5J.tlB_is
#print axioms P5J.armB_is
#print axioms P5J.whereB_is
#print axioms P5J.laidB_is
#print axioms P5J.written_of_laid
#print axioms P5J.nine_of_laid
#print axioms P5J.conds_of_laid
