-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/TestsOAtPlan.lean: two of the three named tests Sh.testsO
(Johnson/Desc/K14/Law/SharedConstTests.lean: the premise hO of the kind K14's law's top): hbelow and
hxWB. A law file; no running text imports it. hbelow ("what is open at the first table's last border
is sampled below lo") IS NO TEST TO EVALUATE: it is a theorem, at every lawful list of segments,
from the two comparisons hI and hV that the top has as premises anyway:
sampledBelow_of_open and endOpenOnly. Here: the call, in the test's own letters. hxWB ("the first of
the first chain's sampled members at W's seat is there, with W's shape": wMemberB ms seat sh) READS
THE LIST OF MEMBERS. At the closed constant (P5J.mgAtAll) that list is made off the plan's seats
(P5T.msAtR Z rad). Here it is RESTATED OVER THE PLAN's SEATS: the test reads of a member its shape
and its seat alone; by plain_membersR these pairs are the seats' own, in the sendings'
order; the radii fall out. Then it is evaluated by Lean's kernel at the written seats (
P5T.psFull, P5T.N0Full).
  linksOk_full: the written list of the 25 segments is lawful: Lean's kernel
  hbelow_of: the first test accepts, from linksOk, hI, hV
  pairOf, wPairsB, wMemberB_pairs: the test reads the pairs (shape, seat) alone
  pairsPlan n ps, wMember_byMake, wMember_atR: at the members by the make the test is wPairsB at
      the plan's seats: no radius
  wPairs_written: the accept at the written values: 82 sendings, psFull, W's seat N0Full.w, the
      shape proofSizedFull.batch.shape.w: Lean's kernel
  wPairs_seat_rejects, wPairs_shape_rejects: the negative tests: at the seat one tree further no
      member sits; with one main row more the shape parts
  hxWB_of: so at every Z whose plan's seats, number of sendings and W's shape are the written ones
  testsO_of: Sh.TestsO from the five: linksOk, hI, hV, the second test's accept, the third's

What is not claimed. The three equations of hxWB_of at a seat: planSeats_at and psFull_is bring
the first down to what the door's pin compares. That the top's open letter ms₁ is P5T.msAtR Z rad,
and N₁ P5T.numbersOf of the plan's seats. The third test (five). Nothing on soundness.

-/
import Johnson.Desc.K14.Law.SharedConstTests
import Johnson.Desc.K13.Law.EndTestsAll
import Johnson.P5T.MembersByMake
import Johnson.P5T.PlanSeatsFull
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Desc.ProofFile.Lot.K13
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes
open VerifiableInference.Desc.Sound (Mem seatOf msOf linksFull sampledBelow)
open VerifiableInference.Desc.First (Numbers ModelPart openSets flatPlaces start linksOk)
open VerifiableInference.Desc.K13.Law (sampledBelow_of_open endOpenOnly)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (proofSendsFull)

set_option maxRecDepth 1000000 in
/-- The written list of the segments is lawful. -/
theorem linksOk_full : linksOk linksFull = true := by decide +kernel

/-- **hbelow is a theorem.** -/
theorem hbelow_of (lo : ℕ) (N : Numbers) (links : List ModelPart) (hlk : linksOk links = true)
    (hI : N.index.1 < lo) (hV : N.w.1 < lo) :
    sampledBelow lo N ((openSets links (flatPlaces true links true) (start links))[(flatPlaces true
      links true).length]?.getD []) = true :=
  sampledBelow_of_open lo N _ (endOpenOnly links hlk) hI hV

/-! ## hxWB over the plan's seats -/

/-- What the test reads of a member. -/
def pairOf (x : Mem) : OracleShape × (ℕ × ℕ) := ((x.1.l.get x.2).1, seatOf x)

/-- The test, on the pairs. -/
def wPairsB (ys : List (OracleShape × (ℕ × ℕ))) (seat : ℕ × ℕ) (sh : OracleShape) : Bool :=
  (ys.find? fun y => decide (y.2 = seat)).any fun y => decide (y.1 = sh)

theorem wMemberB_pairs (ms : List Mem) (seat : ℕ × ℕ) (sh : OracleShape) :
    wMemberB ms seat sh = wPairsB (ms.map pairOf) seat sh := by
  unfold wMemberB wPairsB
  rw [List.find?_map]
  show Option.any (fun m : Mem => decide ((m.1.l.get m.2).1 = sh))
    (ms.find? ((fun y : OracleShape × (ℕ × ℕ) => decide (y.2 = seat)) ∘ pairOf)) = _
  cases ms.find? ((fun y : OracleShape × (ℕ × ℕ) => decide (y.2 = seat)) ∘ pairOf) with
  | none => rfl
  | some x => rfl

/-- The pairs of the plan's seats with an OOD sample, in the sendings' order. -/
def pairsPlan (n : ℕ) (ps : List P5T.PSeat) : List (OracleShape × (ℕ × ℕ)) :=
  (List.range n).flatMap fun k => (P5T.mineAt ps k).map fun p => (p.shape, p.seat)

/-- **At the members by the make the test reads the plan's seats alone.** -/
theorem wMember_byMake (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) (seat : ℕ × ℕ)
    (sh : OracleShape) :
    wMemberB (msOf (P5T.memberListsR n rad ps)) seat sh = wPairsB (pairsPlan n ps) seat sh := by
  rw [wMemberB_pairs]
  exact congrArg (fun ys => wPairsB ys seat sh) (P5T.plain_membersR n rad ps)

theorem wMember_atR (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) (seat : ℕ × ℕ) (sh : OracleShape) :
    wMemberB (P5T.msAtR Z rad) seat sh =
      wPairsB (pairsPlan Z.made.proof.1.sends.length (P5T.planSeats Z Z.D.1)) seat sh :=
  wMember_byMake _ rad _ seat sh

set_option maxRecDepth 1000000 in
/-- **The accept at the written values.** -/
theorem wPairs_written : wPairsB (pairsPlan proofSendsFull.1.sends.length P5T.psFull) P5T.N0Full.w
    proofSizedFull.batch.shape.w = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one tree further no member sits. -/
theorem wPairs_seat_rejects : wPairsB (pairsPlan proofSendsFull.1.sends.length P5T.psFull)
    (P5T.N0Full.w.1 + 1, P5T.N0Full.w.2) proofSizedFull.batch.shape.w = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one main row more. -/
theorem wPairs_shape_rejects : wPairsB (pairsPlan proofSendsFull.1.sends.length P5T.psFull)
    P5T.N0Full.w { proofSizedFull.batch.shape.w with
      mainRows := proofSizedFull.batch.shape.w.mainRows + 1 } = false := by decide +kernel

/-- **hxWB, where the plan's seats, the number of sendings and W's shape are the written ones.** -/
theorem hxWB_of (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) (hp : P5T.planSeats Z Z.D.1 = P5T.psFull)
    (hn : Z.made.proof.1.sends.length = proofSendsFull.1.sends.length)
    (hw : (VerifiableInference.Desc.K13.whereOf Z).lin.w = proofSizedFull.batch.shape.w) :
    wMemberB (P5T.msAtR Z rad) (P5T.numbersOf (P5T.planSeats Z Z.D.1)).w
      (VerifiableInference.Desc.K13.whereOf Z).lin.w = true := by
  rw [wMember_atR, hp, hn, hw]
  exact wPairs_written

/-- **Sh.TestsO from the five.** -/
theorem testsO_of {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)
    (lo : ℕ) (hlk : linksOk O.links = true) (hI : O.N₁.index.1 < lo) (hV : O.N₁.w.1 < lo)
    (hW : wMemberB O.ms₁ O.N₁.w O.Pw.lin.w = true) (h5 : (Sh.fiveNums A O).Nodup) :
    Sh.TestsO A O lo :=
  (Sh.TestsO_iff A O lo).2 ⟨hbelow_of lo O.N₁ O.links hlk hI hV, hW, decide_eq_true h5⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.testsO_of
#print axioms Desc.K14.Law.linksOk_full
#print axioms Desc.K14.Law.hbelow_of
#print axioms Desc.K14.Law.wMemberB_pairs
#print axioms Desc.K14.Law.wMember_byMake
#print axioms Desc.K14.Law.wMember_atR
#print axioms Desc.K14.Law.wPairs_written
#print axioms Desc.K14.Law.wPairs_seat_rejects
#print axioms Desc.K14.Law.wPairs_shape_rejects
#print axioms Desc.K14.Law.hxWB_of
