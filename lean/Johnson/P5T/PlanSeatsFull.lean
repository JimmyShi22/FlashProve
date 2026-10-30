-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/PlanSeatsFull.lean: the seats of the proof file's oracle messages, and the core of the
numbers of the table of joints, AT THE WRITTEN VALUES OF THE FULL SIZE, as closed terms; and the
counts that say that these lists are whole. Definitions and statements with their proofs.

THE ARGUMENTS, EACH WITH ITS WRITTEN TERM AND ITS TIE TO THE PUBLIC PART Z:
  Z.made.proof · `proofSendsFull` (Johnson/G/SendsWritten.lean) · `proofSends_of_is`: compiled.
  Z.first.shape · `shapeFull` (Johnson/Desc/ReqLit/Full.lean) · `first_shape_in_scope`: compiled.
  the declared rounds' entries · `esFull`, off `dryProofFull` (Johnson/G/DryProofLit.lean) ·
    `plans_written` and the entry tests' row 1, on the declared rounds: compiled.
  the makers at Z · `planSeats_at`, `planSeatsAll_at` (Johnson/P5T/PlanSeatsAt.lean, …AllAt.lean).
No statement «in scope» is typed here.

  `seedRoots`; `rooted_written`: the rounds of the first chain that declare a root are just the 82
    sendings' first entries: by ONE walk of Lean's kernel over the written runs. So the roots in
    front of a sending are those of the sendings in front of it; no table is written. `roots_all`:
    the first chain declares 83 roots, the shared chain 11.
  `esFull`; `psFull`, `psFull_is`: the first chain's seats; they are the maker's function at the
    written values. `seatsAllFull`, `seatsAllFull_is`: the like for all three chains.
  `roleCounts`; `psFull_whole`: NO SENDING IS SWALLOWED: 199, 18 and 8 seats, as many as the written
    sendings hold messages. `psFull_roles`: NO SEAT OF A LINK's SENDING IS WITHOUT A ROLE, and each
    role's shape fits: 25 carried, 36 kept, 99 own, 26 masks, 1 at the start; the 12 without a role
    are those of the six sendings that are no link's. `seatsAllFull_apart`: no two seats stand at
    one tree and tenant.
  `N0Full`, `N0Full_seats`: the core of the numbers (`numbersOf`, Johnson/P5T/NumbersOf.lean); the
    index masks' message sits at (1, 0), W at (82, 0).
By evaluations in Lean's kernel (`decide +kernel`): `rooted_written`, `roots_all`, `psFull_whole`,
`psFull_roles`, `seatsAllFull_apart`, `N0Full_seats`.

Why the counts stand first. The makers swallow faults: a sending whose trees cannot be laid yields
no seat, a label that is not read yields seats without a role. A test on a list that is short or
without roles could accept for want of members. Whoever states a fact at these terms cites the two
counts.

Limits. `N0Full` is the core alone: what is laid over it (`withRows`, `withTold`) reads the
first chain's sub-protocols: not here. Nothing on soundness.
-/
import Johnson.P5T.PlanSeatsAllAt
import Johnson.P5T.NumbersOf
import Johnson.G.SendsWritten
import Johnson.G.DryProofLit
import Johnson.Desc.ReqLit.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open Johnson.G
open VerifiableInference.Desc.ReqLit (shapeFull)

/-! ## 1 The roots in front of the first chain's 82 sendings -/

/-- For each sending of the first chain: the number of rounds in front of it, and the roots that its
own first entry declares. -/
def seedRoots : List (Nat × Nat) := proofSends0.sends.map fun s => (s.entry - 1, s.seed.roots)

/-- **The rounds of the first chain that declare a root are just the 82 sendings' first entries**,
each with the roots that the written sending says: one walk over the written runs. -/
theorem rooted_written : rooted dryProofRecsFull dryProofRunsFull0 0 = seedRoots := by
  decide +kernel

/-- All roots of the first chain, and of the shared chain. -/
theorem roots_all :
    (rootsRuns dryProofRecsFull dryProofRunsFull0 48293,
      rootsRuns dryProofRecsFull dryProofRunsFull1 68) = (83, 11) := by decide +kernel

/-! ## 2 The seats at the written values -/

/-- The three chains' written entries. -/
def esFull : List Fmt.Entry × List Fmt.Entry × List Fmt.Entry :=
  (dryProofFull.1.map (·.1.entry), dryProofFull.2.1.map (·.1.entry),
    dryProofFull.2.2.map (·.1.entry))

/-- **The first chain's seats at the written values.** -/
def psFull : List PSeat := planSeatsBy (sumBelow seedRoots) proofSends0 shapeFull

/-- It is the maker's function at the written sendings, shape and entries. -/
theorem psFull_is : planSeatsAt proofSendsFull.1 shapeFull esFull.1 = psFull := by
  have e : esFull.1 = (unrunR dryProofRecsFull dryProofRunsFull0).map (·.1.entry) := rfl
  have f : rootsIn esFull.1 = sumBelow seedRoots := by
    funext k
    rw [e, rootsIn_unrun, rootsRuns_rooted _ _ 0 k, rooted_written, Nat.zero_add]
  show planSeatsBy (rootsIn esFull.1) proofSends0 shapeFull = _
  rw [f]
  rfl

/-- **All three chains' seats at the written values.** -/
def seatsAllFull : List PSeat :=
  psFull ++ chainSeatsBy (rootsRuns dryProofRecsFull dryProofRunsFull1) 1 83 proofSends1 ++
    chainSeatsBy (rootsRuns dryProofRecsFull dryProofRunsFull2) 2 94 proofSends2

theorem seatsAllFull_is : planSeatsAllAt proofSendsFull shapeFull esFull = seatsAllFull := by
  have e1 : esFull.1 = (unrunR dryProofRecsFull dryProofRunsFull0).map (·.1.entry) := rfl
  have e2 : esFull.2.1 = (unrunR dryProofRecsFull dryProofRunsFull1).map (·.1.entry) := rfl
  have e3 : esFull.2.2 = (unrunR dryProofRecsFull dryProofRunsFull2).map (·.1.entry) := rfl
  have l1 : esFull.1.length = 48293 := by
    rw [show esFull.1 = dryProofFull.1.map (·.1.entry) from rfl, List.length_map]
    exact congrArg (·.1) dryProofFull_length
  have l2 : esFull.2.1.length = 68 := by
    rw [show esFull.2.1 = dryProofFull.2.1.map (·.1.entry) from rfl, List.length_map]
    exact congrArg (·.2.1) dryProofFull_length
  have r1 : rootsIn esFull.1 esFull.1.length = 83 := by
    rw [l1, e1, rootsIn_unrun]
    exact congrArg (·.1) roots_all
  have r2 : rootsIn esFull.2.1 esFull.2.1.length = 11 := by
    rw [l2, e2, rootsIn_unrun]
    exact congrArg (·.2) roots_all
  have f2 : rootsIn esFull.2.1 = rootsRuns dryProofRecsFull dryProofRunsFull1 := by
    funext k
    rw [e2, rootsIn_unrun]
  have f3 : rootsIn esFull.2.2 = rootsRuns dryProofRecsFull dryProofRunsFull2 := by
    funext k
    rw [e3, rootsIn_unrun]
  unfold planSeatsAllAt seatsAllFull
  rw [psFull_is, r1, r2, f2, f3]
  rfl

/-! ## 3 The counts: that the lists are whole, and that every seat has its role -/

/-- How many seats bear each role: carried, kept, own, mask, at the start, none. -/
def roleCounts (ps : List PSeat) : List Nat :=
  [(ps.filter fun p => p.role == .carried).length,
    (ps.filter fun p => match p.role with | .kept _ _ => true | _ => false).length,
    (ps.filter fun p => match p.role with | .own _ => true | _ => false).length,
    (ps.filter fun p => p.role == .mask).length,
    (ps.filter fun p => match p.role with | .atStart _ => true | _ => false).length,
    (ps.filter fun p => p.role == .other).length]

/-- **No sending is swallowed**: there are as many seats as the written sendings hold messages:
199 in the first chain, 18 and 8 in the two later ones. -/
theorem psFull_whole :
    (psFull.length, (proofSends0.sends.map (·.sent.length)).sum, seatsAllFull.length,
      (proofSends1.sends.map (·.sent.length)).sum, (proofSends2.sends.map (·.sent.length)).sum) =
      (199, 199, 225, 18, 8) := by decide +kernel

/-- **Every seat of a link's sending has a role, and each role's shape fits**; and how many seats
bear each role. The twelve without a role are those of the six sendings that are no link's. -/
theorem psFull_roles :
    (rolesFitAt shapeFull psFull).length :: (psFull.filter fun p => p.seg.isNone).length ::
      roleCounts psFull = [0, 12, 25, 36, 99, 26, 1, 12] := by
  decide +kernel

/-- No two seats of all three chains stand at one tree and tenant. -/
theorem seatsAllFull_apart : (seatsAllFull.map fun p => (p.j, p.t)).Nodup := by decide +kernel

/-! ## 4 The core of the table's numbers -/

/-- **The core of the table's numbers at the written values.** -/
def N0Full : VerifiableInference.Desc.First.Numbers := numbersOf psFull

/-- The index masks' message's seat, and W's. -/
theorem N0Full_seats : (N0Full.index, N0Full.w) = ((1, 0), (82, 0)) := by decide +kernel

end P5T

#print axioms P5T.rooted_written
#print axioms P5T.roots_all
#print axioms P5T.psFull_is
#print axioms P5T.seatsAllFull_is
#print axioms P5T.psFull_whole
#print axioms P5T.psFull_roles
#print axioms P5T.seatsAllFull_apart
#print axioms P5T.N0Full_seats
