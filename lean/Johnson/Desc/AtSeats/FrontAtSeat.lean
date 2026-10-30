-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/FrontAtSeat.lean: THE TEST `frontB`
(Johnson/Desc/K13/Law/BridgeG.lean) AT THE PROOF FILE's FIRST STATE, AND SO AT THE REACHED STATES
OF BORDERS 2 AND 3 OF ITS FIRST CHAIN. Statements with their proofs: calls of two lemmas of
other files on that state. `front_start`: from the return of the public part's maker: where
  `ProofFile.startS Z p` bears no mark it passes `frontB`: its frame's groups are its shape's
  (`Meaning.K2.recAll_startS`, RecRun.lean; the blank state, which is laid where the request
  fails the start's own test, bears a mark); nothing is kept (`Meaning.K2.first_keeps_none`,
  Johnson/IMR/KeptNone.lean). `front_23_seat`: `front_23` (FrontAtTwoThree.lean) at that first
  state. TWO PREMISES STAY: h2: at border 2 the reached state is the first state
  (`reach_two`, Johnson/P1L20R/RoomFold.lean, says so in the goals' scope: not imported here: its
  cone is wide); hb, hu: the sub-protocol at number 2 stands under the joined opening.
What is not claimed. h2, hu. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.FrontAtTwoThree
import Johnson.IMR.RecRun
import Johnson.IMR.KeptNone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Params OnBytes.Model
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (frontB frontB_iff)
open VerifiableInference.Desc
open ProofFile (Cl)

/-- The first state's frame stands at link 0: by the make. -/
theorem first_link_zero {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub)
    (hq : (Z.s₀.withReq (Verify.words32 p.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) :
    (ProofFile.startS Z p).check.frame.link = 0 := by
  have e : Z.s₀.check.frame.link = 0 := by
    have k := Meaning.K2.pub_start hZ
    unfold VerifiableInference.Desc.First.S.startP at k
    split at k
    · rw [← Option.some.inj k]
      rfl
    · cases k
  unfold ProofFile.startS
  dsimp only
  rw [if_pos hq]
  exact e

/-- **The first state passes the test.** -/
theorem front_start {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub)
    (hm : (ProofFile.startS Z p).failed = none) : frontB (ProofFile.startS Z p) = true := by
  have hq : (Z.s₀.withReq (Verify.words32 p.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true := by
    by_contra hn
    unfold ProofFile.startS at hm
    dsimp only at hm
    rw [if_neg hn] at hm
    have h1 : (some "state-blank" : Option String) = none := hm
    cases h1
  have R := (Meaning.K2.recAll_startS hZ hq).walk
  refine (frontB_iff _).2 ⟨?_, first_link_zero hZ p hq, Meaning.K2.first_keeps_none hZ p⟩
  rw [R.groups, R.shape]

/-- **The test at the reached states of borders 2 and 3 of the proof file's first chain.** -/
theorem front_23_seat {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) {bs : List (Block S Cl)}
    (h2 : ∀ z s, Reach 0 bs (ProofFile.startS Z) 2 (z, s) → s = ProofFile.startS Z z) {e : Block S Cl}
    (hb : bs[2]? = some e) {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ}
    (hu : e.UnderR (K1.openingZero q gp nm X fvs kCol : Block S Cl)) :
    ∀ j a, Reach 0 bs (ProofFile.startS Z) j a → j = 2 ∨ j = 3 → a.2.failed = none →
      frontB a.2 = true :=
  front_23 h2 (front_start hZ) hb hu

end HashBuild
