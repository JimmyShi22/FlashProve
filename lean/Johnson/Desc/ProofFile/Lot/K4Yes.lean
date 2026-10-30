-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Lot/K4Yes.lean: where a term of the form that the description seats at K4's
places (by reading: see Limits) says yes, K4's own block at the carried record says the same yes.
The term: K4's lot's block `k4Block x` (Johnson/Desc/ProofFile/Lot/K4.lean), behind the test on
marks `guardMark` (Johnson/Desc/ProofFile/Frames1.lean), with a name and a place laid over it,
behind the guard on one seat `Block.guarded` (Johnson/Desc/SeatGuard.lean). Three statements and
their proofs.

  `guardMark_under`: where `guardMark b` says yes, b says the same yes.
  `k4Block_under`: where `k4Block x` says yes, `blockAtS { x.2 with k3Runs := true }` says the same
    yes: the two decisions are one function, by unfolding.
  `k4Seated_under`: where `Block.guarded same but { { guardMark (k4Block x) with name := n } with
    place := a }` says yes, `blockAtS { x.2 with k3Runs := true }` says the same yes.

No new argument: `guarded_under` (Johnson/Desc/Sound/SeatGuardLaws.lean); each of the two tests
returns the record that it is handed, or refuses.

Limits. One direction: from the term's yes. "Yes" is the field decide alone: nothing on the lists of
claims, on what is done after the batching, on the rounds or on the test on the plan; x.1, which
that test reads, is read by no statement here. same, but, x, n and a are letters: nothing says that
x is a member of the lot's list. THAT THE FIRST CHAIN HOLDS THIS TERM AT K4's PLACES IS NOT SAID
HERE: it is read off the fold's and the driver's texts, among them: the lot's blocks in `hearC`
reach the fold as they are (`Lot.blocks`, LotCore.lean); the parts lay `{ guardMark x.2 with name :=
p.name }` (`partsAt`, OnlineDescriptionFromBlockTables.lean); `chainBy` (Frames1.lean) leaves that block as it is ONLY WHERE NO
LOT HANDS A BLOCK OF THE KIND frame AT THE SAME CHAIN, SEGMENT AND NUMBER: else it joins that block
behind it (`Block.andThen`), and the seated term is another, of which nothing is said here; the
driver lays the place over a block that it is handed (`blockAt`), and then the guard over the whole
chain (`firstChain`; both Johnson/Desc/First/Driver/Chain.lean). Nothing on soundness.
-/
import Johnson.Desc.ProofFile.Lot.K4
import Johnson.Desc.ProofFile.Frames1
import Johnson.Desc.Sound.SeatGuardLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open VerifiableInference.Desc (Block Place guarded_under under_of_decide)
open VerifiableInference.Desc.First (S)
open OnBytes.Desc.First.K4 (Par blockAtS)

/-- **Where the test on marks says yes, the block says the same yes.** -/
theorem guardMark_under (b : Block S Cl) : (guardMark b).Under b := by
  intro s rs gs s' H
  have H' : ((b.decide s rs gs).bind fun t =>
      match t.failed with
      | none => .ok t
      | some m => .error ("marked: " ++ m)) = .ok s' := H
  cases hd : b.decide s rs gs with
  | error e =>
    rw [hd] at H'
    exact nomatch H'
  | ok t =>
    rw [hd] at H'
    have H2 : (match t.failed with
      | none => Except.ok t
      | some m => Except.error ("marked: " ++ m)) = Except.ok s' := H'
    split at H2
    · exact H2
    · exact nomatch H2

/-- **Where K4's lot's block says yes, K4's own block at the carried record, with k3Runs := true,
says the same yes.** -/
theorem k4Block_under (x : Bool × Par) :
    (k4Block x).Under (blockAtS { x.2 with k3Runs := true }) :=
  under_of_decide rfl

/-- **Where a term of the seated form says yes, K4's own block says the same yes.** -/
theorem k4Seated_under (same : S → S → Bool) (but : Place → Bool) (x : Bool × Par) (n : String)
    (a : Place) :
    (Block.guarded same but
      { { guardMark (k4Block x) with name := n } with place := a }).Under
      (blockAtS { x.2 with k3Runs := true }) :=
  fun s rs gs s' H =>
    have h1 : (guardMark (k4Block x)).decide s rs gs = .ok s' :=
      guarded_under same but { { guardMark (k4Block x) with name := n } with place := a } s rs gs
        s' H
    k4Block_under x s rs gs s' (guardMark_under (k4Block x) s rs gs s' h1)

end ProofFile

#print axioms ProofFile.guardMark_under
#print axioms ProofFile.k4Block_under
#print axioms ProofFile.k4Seated_under
