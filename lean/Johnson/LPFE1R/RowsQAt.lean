-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/RowsQAt.lean: e₁'s SHEET, ROW 156, THE ONE SIDE: THE NUMBER OF ROWS THAT THE CLOSING
KIND K10's FIRST DECLARED ROUND BEARS (Q.rows) IS A WRITTEN NUMBER: IN THE GOALS' SCOPE, WHERE THE
VERIFIER's OWN VALUE IS LAID, AT ALL 25 LINKS: WITHOUT THE PARSE OF THE 48,293 WRITTEN ENTRIES (a
try at the closed term over that parse died of stack). Definitions, closed facts by Lean's kernel at
written values, one theorem. A law file; no running text imports it.
  `lensW`, `offW k`   how many rounds each of the 358 sub-protocols declares, off the written cut;
                    how many stand in front of number k.
  `rowsQW`            the 25 numbers of rows. `batsW`: 25 written pairs: (the offset of K10's first
                    round of link l, its number of rows).
  `offs_written`      BY THE KERNEL: the pairs are (offW (ixK10 l), rowsQW l).
  `bats_written`      BY THE KERNEL: the written entry at each of the 25 offsets has the pair's
                    number of rows: 25 readings of the written list by number. `bats_bent`: the
                    control: with one number of rows one more the test says no.
  `rows_q_at`         in scope, laid: K10's sub-protocol b at number ixK10 l of the flat list,
with b.rounds = (kind Q).rounds: Q.rows = rowsQW l. HOW. The sub-protocol's first declared round is
the flat list's round at the offset (flatMap_at; the lengths off the pinned cut); the flat list's
rounds' entries are the written entries (entries_laid); the kind's first
entry is "BAT" with rows := Q.rows.

Limits. At OnBytes.secondHashFunction (the pin's letter). The full size alone. That b.rounds = (kind Q).rounds
is a premise here (LPFK10.k10_rounds_sit pays it). Nothing on the verifier's state. "The value is
laid" is spent here also for the entry test cutRow (Johnson/Desc/Laid/ProofAsks.lean: the
description's cut is the written): by P5J.pins_of_laid's second half: that is "the pinned cut"
above. Nothing on soundness or on hiding.
-/
import Johnson.Top.H0.Tw.K2C.PossWritten
import Johnson.Top.H0.K2Hears.KeptAtIndex
import Johnson.Desc.First.CutAtNumbers
import Johnson.Desc.First.CutWritten
import Johnson.LPFK10R.RoundsAt
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open OnBytes.Maker (WholeD)
open Johnson.G (dryProofFull)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par kind)
open VerifiableInference.Desc.First.K2Caller (entries_laid)
open VerifiableInference.PlanWritten (cutFirstFull)
open LPFK10 (ixK10)
open ProofFile (Cl)

/-- How many rounds each sub-protocol of the first chain declares, off the written cut. -/
def lensW : List ℕ := cutFirstFull.map (·.2.2.1)

/-- How many declared rounds stand in front of sub-protocol number k. -/
def offW (k : ℕ) : ℕ := (lensW.take k).sum

/-- The numbers of rows, link by link. -/
def rowsQW : List ℕ :=
  [6, 3295, 1324, 3295, 1324, 3295, 1324, 3295, 1324, 3295, 1324, 3295, 1324, 3295, 1324, 3295,
    1324, 3295, 1324, 3295, 1324, 3295, 1324, 3295, 1322]

/-- (the offset of K10's first round of link l, its number of rows). -/
def batsW : List (ℕ × ℕ) :=
  [(1970, 6), (3850, 3295), (5827, 1324), (7707, 3295), (9684, 1324), (11564, 3295),
    (13541, 1324), (15421, 3295), (17398, 1324), (19278, 3295), (21255, 1324), (23135, 3295),
    (25112, 1324), (26992, 3295), (28969, 1324), (30849, 3295), (32826, 1324), (34706, 3295),
    (36683, 1324), (38563, 3295), (40540, 1324), (42420, 3295), (44397, 1324), (46277, 3295),
    (48225, 1322)]

set_option maxRecDepth 1000000 in
theorem offs_written :
    batsW = (List.range 25).map fun l => (offW (ixK10 l), rowsQW.getD l 0) := by decide +kernel

/-- The test: the written entry at each offset has the number of rows. -/
def batsB (W : List (ℕ × ℕ)) : Bool :=
  W.all fun y => ((dryProofFull.1.map (·.1.entry))[y.1]?).map (·.rows) == some y.2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem bats_written : batsB batsW = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The control. -/
theorem bats_bent : batsB (batsW.modifyHead fun y => (y.1, y.2 + 1)) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl}

/-- **Q.rows is the written number.** -/
theorem rows_q_at (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l < 25)
    {b : Block S Cl} (hb : cF.blocksInOrder[ixK10 l]? = some b) {Q : Par}
    (hr : b.rounds = (kind (Cl := Unit) Q).rounds) : Q.rows = rowsQW.getD l 0 := by
  have hlen : cF.blocksInOrder.map (·.rounds.length) = lensW := by
    have hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull :=
      (P5J.pins_of_laid hW L).2
    rw [First.roundsLen_cut, hc]
    rfl
  have h0 : 0 < b.rounds.length := by
    rw [hr]
    exact Nat.zero_lt_succ _
  have h1 := Own.flatMap_at (fun x : Block S Cl => x.rounds) cF.blocksInOrder (ixK10 l) b 0 hb h0
  have e1 : ((cF.blocksInOrder.take (ixK10 l)).map fun y => y.rounds.length).sum = offW (ixK10 l) := by
    unfold offW
    rw [← hlen, List.map_take]
  rw [e1, Nat.add_zero] at h1
  have h2 : ((cF.blocksInOrder.flatMap (·.rounds)).map (·.entry))[offW (ixK10 l)]? =
      (b.rounds[0]?).map (·.entry) := by
    rw [List.getElem?_map, h1]
  rw [entries_laid hW L, hr] at h2
  have h3 : (((kind (Cl := Unit) Q).rounds[0]?).map (·.entry)).map (·.rows) = some Q.rows := rfl
  have hin : (offW (ixK10 l), rowsQW.getD l 0) ∈ batsW := by
    rw [offs_written]
    exact List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have c := eq_of_beq (List.all_eq_true.1 bats_written _ hin)
  have c' : ((dryProofFull.1.map (·.1.entry))[offW (ixK10 l)]?).map (·.rows) =
      some (rowsQW.getD l 0) := c
  rw [h2, h3] at c'
  exact Option.some.inj c'

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.offs_written
#print axioms VerifiableInference.Desc.LinkJoin.bats_written
#print axioms VerifiableInference.Desc.LinkJoin.bats_bent
#print axioms VerifiableInference.Desc.LinkJoin.rows_q_at
