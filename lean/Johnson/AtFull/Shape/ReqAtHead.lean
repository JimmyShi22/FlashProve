-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReqAtHead.lean: UNDER THE HEAD P5J.AtMgA: NO MEMBER OF THE PROOF FILE's OWN
FIRST CHAIN TURNS THE REQUEST's WORDS: so every test that reads these words alone says behind a yes
what it said in front. A joining of laws; nothing is evaluated.

What it is for. Some of the members' named tests on values read the request's words and nothing else
of the state: S.reqOk (the output head's own rounds), the tokens' test of the layers' first group,
three of the four tests of S.coveredAt. They are no matter of the prover's values or of the draws:
no member turns what they read. (That S.reqOk holds at every reached state without a mark is walked
in ReqReached.lean; for the tokens' test and S.coveredAt no such walk is stated.)

By what. The library has the relation "the request's words stay, and no mark is taken off" at every
maker of the seat (Meaning.K2.seatKeeps_req, seatBack_req, Johnson/LTPileR/ReqSeat.lean), and the
walk from the makers to every entry of the chain's flat list at an opening's own letters
(Meaning.K2.open_flat, Johnson/IMR/OpenFlat.lean). Under the head every entry passes its test on the
plan (plans_at, PlansAtHead.lean).

  `KeepsReqAt bs b`: every yes of the step of the member number b leaves the request's words.
  `reqStays_at`: under the head, at every n: the library's relation ReqStays from the state in
    front to the state behind every yes of the member's step. The next two are cut from it.
  **`req_kept_at`**: under the head: KeepsReqAt cF.blocksInOrder n AT EVERY n.
  `mark_kept_at`: and takes no mark off: no mark behind, no mark in front.
  `reqOk_same`, `tokv_same`, `coveredAt_same`: three readings of the words alone.
  **`reqOk_kept_at`**: so S.reqOk T V says behind every yes what it said in front, at every member.

Limits. THAT A TEST HOLDS AT THE CHAIN's START IS NOT SHOWN HERE (the library's req_start, in
ReqSeat.lean too, says which words the start bears where it bears no mark). One member at a time: no
run over several members is walked here (the library's open_fold_all does). That the head has a
member is shown at named sets of public files alone, in a side library. At the format's second
hash function. Nothing on soundness, completeness or hiding.

-/
import Johnson.AtFull.Shape.PlansAtHead
import Johnson.IMR.OpenFlat
import Johnson.LTPileR.ReqSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain step_iff)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- Every yes of the member number b leaves the request's words. -/
def KeepsReqAt {Cl : Type} (bs : List (Block S Cl)) (b : Nat) : Prop :=
  ∀ blk, bs[b]? = some blk → ∀ ft s rs cols s' n, blk.step ft s rs cols = .ok (s', n) →
    s'.req = s.req

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The library's relation at every member, under the head. -/
theorem reqStays_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (n : Nat) :
    ∀ blk, cF.blocksInOrder[n]? = some blk → ∀ ft s rs cols s' k, blk.step ft s rs cols = .ok (s', k) →
      Meaning.K2.ReqStays s s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro blk hb ft s rs cols s' k hs
  have hm := List.mem_of_getElem? hb
  obtain ⟨_, hd, _⟩ := (step_iff ft blk s s' rs cols k).1 hs
  exact Meaning.K2.open_flat Meaning.K2.seatKeeps_req Meaning.K2.seatBack_req O trivial
    (fun _ _ _ => trivial) blk hm (plans_at h blk hm) s _ _ s' hd

/-- **No member turns the request's words.** -/
theorem req_kept_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (n : Nat) :
    KeepsReqAt cF.blocksInOrder n :=
  fun blk hb ft s rs cols s' k hs => (reqStays_at h n blk hb ft s rs cols s' k hs).1

/-- No member takes a mark off. -/
theorem mark_kept_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (n : Nat) :
    ∀ blk, cF.blocksInOrder[n]? = some blk → ∀ ft s rs cols s' k, blk.step ft s rs cols = .ok (s', k) →
      s'.failed = none → s.failed = none :=
  fun blk hb ft s rs cols s' k hs => (reqStays_at h n blk hb ft s rs cols s' k hs).2

/-- The request's tokens are read off the words alone. -/
theorem tokv_same {s s' : S} (e : s'.req = s.req) : s'.tokv = s.tokv := by
  unfold S.tokv S.reqT
  rw [e]

/-- The state's own test on the request reads the words alone. -/
theorem reqOk_same {s s' : S} (e : s'.req = s.req) (T V : Nat) : s'.reqOk T V = s.reqOk T V := by
  unfold S.reqOk S.rowR S.rowE S.reqT
  rw [tokv_same e, e]

/-- The covered positions at a given reply are made of the words alone. -/
theorem coveredAt_same {s s' : S} (e : s'.req = s.req) (T V y : Nat) :
    s'.coveredAt T V y = s.coveredAt T V y := by
  unfold S.coveredAt
  rw [e]

/-- **The state's own test on the request says behind every yes what it said in front.** -/
theorem reqOk_kept_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (n T V : Nat) :
    ∀ blk, cF.blocksInOrder[n]? = some blk → ∀ ft s rs cols s' k, blk.step ft s rs cols = .ok (s', k) →
      s'.reqOk T V = s.reqOk T V :=
  fun blk hb ft s rs cols s' k hs => reqOk_same (req_kept_at h n blk hb ft s rs cols s' k hs) T V

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.reqStays_at
#print axioms Johnson.AtFull.Shape.req_kept_at
#print axioms Johnson.AtFull.Shape.mark_kept_at
#print axioms Johnson.AtFull.Shape.tokv_same
#print axioms Johnson.AtFull.Shape.reqOk_same
#print axioms Johnson.AtFull.Shape.coveredAt_same
#print axioms Johnson.AtFull.Shape.reqOk_kept_at
