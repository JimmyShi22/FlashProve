-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/MemThereFull.lean: "AT EACH NUMBER BELOW n WHOSE PLACE LIES IN THE SEGMENT's GROUP A
MEMBER SITS, AND THE LISTED SHAPE IS THAT MEMBER's" (`membersThereB`,
Johnson/Desc/First/Link/Law/MemberListed.lean), AT THE WRITTEN VALUES, AT EACH OF THE 25 SEGMENTS:
BY LEAN's KERNEL. Three definitions with code and five theorems. No public file is read. In the
make of Johnson/P5T/PlanSixFull.lean.
  `memThereC M places ms grp n`: the test, with what it reads handed in one by one. `memThere_is`:
  **it is `membersThereB`, at any structure of public numbers** (rfl).
  `nMemThere m`: the written count of messages three borders behind segment m's batching.
  `memThereAt M ms m`: the test at the written places `LFull.places`, the written numbers' group
  of m, and `nMemThere m`.
  `memThere_full`: **by the kernel: at the written shapes `MFull` and the written members `msOf
  mlFull`: at all 25 segments.** `memThere_at`: at each.
  `memThere_counts`: what it ranges over: 199 places, 199 shapes, 167 members; the groups have 5
  to 7 places, AND ALL OF THEM LIE BELOW n: the test is idle at no segment.
  `memThere_off`: three negative tests: with the shapes reversed it holds at 0 of 25; WITH THE
  MEMBERS' LIST EMPTIED AT 0 OF 25; with the shapes cut to 100 at 13.
IT IS STRONGER THAN `membersB` (Johnson/Desc/First/Link/Law/PlanFitsB.lean), which another file has
at the head: where no member is found, or the list of shapes is short, that one accepts and this
one rejects.
Every number here was printed by the evaluator before it was typed.
Limits. The written values alone: that they are a verifier's is another file's
(Johnson/P5T/MemThereAtMg.lean). The full size alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.NotIxFull
import Johnson.Desc.First.Link.Law.MemberListed
import Johnson.Desc.First.Close.Law.AlikeFull
import Johnson.HB.LLHARD.LaidWritten
import Johnson.Desc.First.Link.Law.K9KindTiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (FoldData)
open VerifiableInference.Desc.First.Close (mlFull)
open VerifiableInference.Desc.Sound (Mem seatOf msOf)
open VerifiableInference.Desc.LinkJoin (membersThereB batchAt)
open VerifiableInference.Desc.K13.Law (LFull MFull)

/-- The test, with what it reads handed in one by one. -/
def memThereC (M : List OracleShape) (places : List (ℕ × ℕ)) (ms : List Mem) (grp : List (ℕ × ℕ))
    (n : ℕ) : Bool :=
  (List.range n).all fun o =>
    match places[o]? with
    | some x =>
      !grp.contains x ||
        match ms.find? fun y => decide (seatOf y = x) with
        | some y => decide (M[o]? = some (y.1.l.get y.2).1)
        | none => false
    | none => true

/-- **It is the test, at any structure of public numbers.** -/
theorem memThere_is (d : FoldData) (ms : List Mem) (grp : List (ℕ × ℕ)) (n : ℕ) :
    membersThereB d ms grp n = memThereC d.M d.L.places ms grp n := rfl

/-- The written count of messages three borders behind segment m's batching. -/
def nMemThere (m : ℕ) : ℕ := NFull.msgsAt P5J.At.ps[batchAt P5J.fullLinks P5J.At.ps m + 1 + 1 + 1]?

/-- The test at the written places, group and count. -/
def memThereAt (M : List OracleShape) (ms : List Mem) (m : ℕ) : Bool :=
  memThereC M LFull.places ms (N0Full.group m) (nMemThere m)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **By the kernel: at all 25 segments.** -/
theorem memThere_full : ((List.range 25).all fun m => memThereAt MFull (msOf mlFull) m) = true := by
  decide +kernel

theorem memThere_at {m : ℕ} (hm : m < 25) : memThereAt MFull (msOf mlFull) m = true :=
  List.all_eq_true.1 memThere_full m (List.mem_range.2 hm)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By the kernel: what it ranges over. -/
theorem memThere_counts :
    (LFull.places.length, MFull.length, (msOf mlFull).length,
      (List.range 25).map fun m => ((List.range (nMemThere m)).filter fun o =>
        (LFull.places[o]?).any fun x => (N0Full.group m).contains x).length) =
      (199, 199, 167,
        [5, 6, 7, 6, 7, 6, 7, 6, 7, 6, 7, 6, 7, 6, 7, 6, 7, 6, 7, 6, 7, 6, 7, 6, 5]) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By the kernel: three negative tests. -/
theorem memThere_off :
    (((List.range 25).filter fun m => memThereAt MFull.reverse (msOf mlFull) m).length,
      ((List.range 25).filter fun m => memThereAt MFull [] m).length,
      ((List.range 25).filter fun m => memThereAt (MFull.take 100) (msOf mlFull) m).length) =
      (0, 0, 13) := by decide +kernel

end P5T

#print axioms P5T.memThere_is
#print axioms P5T.memThere_full
#print axioms P5T.memThere_at
#print axioms P5T.memThere_counts
#print axioms P5T.memThere_off
