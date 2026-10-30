-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/RidesAtM3.lean: kind K13, the members' batching: WHAT A CHAIN's
THREAD ASKS OF THE ITEMS THAT PASS A MEMBER BY (`RidesPast`, Honest/Thread/Pays.lean), AT THE FIRST
CHAIN's THREAD (`Letters.thread`, Honest/Thread/First.lean) AND THE KIND's MEMBER. A definition;
statements with their proofs: general in the thread's parameters, and at the library's own
(`FirstThread.lettersAt`, Honest/Thread/FirstAt.lean), there by one evaluation of Lean's kernel on
the written lists.

`RidesPast T b`: an item that is open at the border number b and that the row behind it neither
shuts nor owes says behind the member, of any witness, what it says in front. AT THE KIND's PLACE
ONE ITEM IS OF THAT SORT: "unmarked": the state bears no mark of failure. The others that are open
in front: "pile" is shut; the committed table's pin and the index masks' pin are owed anew.
Main names:
  `passBy O r`: of the items O, those that the row r neither shuts nor owes: a list, with code.
  `mem_passBy`: what membership in it says.
  `k13_thread_rides`: `RidesPast L.thread b`, from: `passBy` at the border is ["unmarked"]; and
    hkeep. ONCE THE FIRST PREMISE IS SPENT, hkeep IS WHAT `RidesPast` ASKS, in its own words: what
    this statement shows is how many items pass by. Seated.lean of this folder has hkeep from an
    equation on the field `keeps`.
  `m3_passBy`: at the library's own lists and number 355 it is, by the kernel.
  `k13_thread_rides_at`: **`RidesPast` at number 355 of the thread at the library's own
    parameters.**
  `withClaim_failed`: the state that the kind's sub-protocol leaves bears the mark that the state in
    front bears.

The premise hkeep. `keeps` is a field of the thread's parameters without text. `RidesPast` has it in
hand, with the whole thread in front. WHAT IS ASKED OF IT HERE, AS A PREMISE NAMED AS SUCH, AND
UNDER THAT SENTENCE: where the thread holds in front at s and `keeps b s s'` holds, s' bears no mark
of failure. (That s bears none is in the thread's form.)

Words. Thread, border, member, parameters: Honest/Thread/Thr.lean's head tells them. The table of
joints and its items: Johnson/Desc/First/Borders.lean's.

What is not claimed. That `keeps` has a text that gives hkeep and that the member's step meets. That
the hypothesis under which the library's own parameters are laid can be met. That a thread holds at
any run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.K13.Honest.SubProtocols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.First (S Item start)
open VerifiableInference.Desc.K13.Honest (withClaim)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Letters lettersAt Script WtF)

/-- Of the items O, those that the row r neither shuts nor owes. -/
def passBy {ι : Type} [DecidableEq ι] (O : List ι) (r : FwdRow ι) : List ι :=
  O.filter fun i => !r.shuts.contains i && !r.owes.contains i

/-- What membership in it says. -/
theorem mem_passBy {ι : Type} [DecidableEq ι] {O : List ι} {r : FwdRow ι} {i : ι} (hi : i ∈ O)
    (h1 : i ∉ r.shuts) (h2 : i ∉ r.owes) : i ∈ passBy O r := by
  refine List.mem_filter.2 ⟨hi, ?_⟩
  simp [h1, h2]

/-- The state that the kind's sub-protocol leaves bears the mark that the state in front bears. -/
theorem withClaim_failed (s : S) (st : Statement) (msg : Array OracleNotice) (row : TensorRow) :
    (withClaim s st msg row).failed = s.failed := rfl

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M)

/-- **`RidesPast` at a member past which "unmarked" alone goes.** hkeep: what is asked of the field
`keeps`. -/
theorem k13_thread_rides {b : Nat}
    (hO : passBy (L.thread.opened b) (L.thread.row b) = [Item.unmarked])
    (hkeep : ∀ k s m En s', Thr L.thread b k s m En → L.keeps b s s' → s'.failed = none) :
    RidesPast L.thread b := by
  intro k s m En s' ps i v hT hk hi h1 h2 _
  have hi' : i ∈ passBy (L.thread.opened b) (L.thread.row b) := mem_passBy hi h1 h2
  rw [hO] at hi'
  obtain rfl : i = Item.unmarked := List.mem_singleton.1 hi'
  exact hkeep k s m En s' hT hk

end

set_option maxRecDepth 100000 in
/-- At the library's own lists "unmarked" alone goes past the sub-protocol number 355. -/
theorem m3_passBy :
    passBy (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 355)
      (FirstRows.rows P5J.At.links P5J.At.ps 355) = [Item.unmarked] := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`RidesPast` at the kind's member, at the library's own parameters.** -/
theorem k13_thread_rides_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop)
    (hkeep : ∀ k s m En s',
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s m
        En → keeps 355 s s' → s'.failed = none) :
    RidesPast (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 :=
  k13_thread_rides (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) m3_passBy
    hkeep

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.mem_passBy
#print axioms ProofFile.Honest.K13.withClaim_failed
#print axioms ProofFile.Honest.K13.k13_thread_rides
#print axioms ProofFile.Honest.K13.m3_passBy
#print axioms ProofFile.Honest.K13.k13_thread_rides_at
