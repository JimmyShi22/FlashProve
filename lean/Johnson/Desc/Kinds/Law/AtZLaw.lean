-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/AtZLaw.lean: WHAT TIES Johnson/Desc/Kinds/Head/AtZ.lean's FIVE CLOSED TERMS
TO THE BLOCK, THE SEAT AND THE LAWS. STATED AND PROVED.
  iU3At_is · par_sizes · par_policy · sizes_fields · policy_fields · seat_request: by rfl, at every
      Z: iU3At Z is the laws' readsOf X; parOf's sizes and policy at hShapeAt Z and ANY work (they
      do not hang on it) are sizesAt Z and policyAt Z; both field by field (ls is la - lt), for
      whoever holds another text of them; the seat's request at a state is requestOf of it.
  third_O: where publicOfO o returns X, AT EVERY o, the head's plan names the array of reads as
      array 0 (ReadsNamed.public_third says it of publicOf's X; here by the same
      planH2_third, off PublicSteps.attention).
  iU3At_made · block_made: so at pureRoad.pub's value Z, at every o: X's plan names some (iU3At Z),
      iU3At Z = 0, and Head.blockOf X l is blockAt (hShapeAt Z) (iU3At Z) (the setting's work) l.
  rq_of_req · rq_start: requestOf s = rqAt Z p at EVERY state s that holds the words of p.request;
      so at ProofFile.startS Z p where the state's tests on the request pass.
WHAT IT DOES NOT SAY. That pureRoad.pub returns at any files and any o (runs say it of the stored
sets; no theorem). That a state on the chain still holds the request's words: each block's own law.
That rqAt Z p is the library's request of an instance: Law/AtZReqX.lean, under one equation on the
words. The numbers of hShapeAt Z in the goals' scope: numbers_in_scope, stated at
publicOf's X: not carried to publicOfO o here. Nothing on soundness.
LETTERS. o · pol · lay · KL: read by the one premise "pureRoad.pub o pol lay KL = .ok Z". No letter
under "there is".
IMPORTED, NOT PROVED HERE: ProofFile.Law.pub_public; publicSteps_of_O; planH2_third, Third.

-/
import Johnson.Desc.Kinds.Head.AtZ
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Desc.Kinds.Law.RowRides
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.AtZ

open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (publicOfO publicSteps_of_O)
open Law.ReadsNamed (Third planH2_third)

/-- iU3At is the laws' readsOf at X. -/
theorem iU3At_is (Z : ProofFile.Pub) : iU3At Z = Law.readsOf Z.p.X := rfl

/-- parOf's sizes, at any work. -/
theorem par_sizes (Z : ProofFile.Pub) (work : Nat) : (parOf (hShapeAt Z) work).sizes = sizesAt Z := rfl

/-- parOf's policy, at any work. -/
theorem par_policy (Z : ProofFile.Pub) (work : Nat) : (parOf (hShapeAt Z) work).policy = policyAt Z := rfl

/-- The sizes, field by field: whoever holds another text of them lays it beside this one. -/
theorem sizes_fields (Z : ProofFile.Pub) : sizesAt Z =
    { lt := (hShapeAt Z).lt, ls := (hShapeAt Z).la - (hShapeAt Z).lt, d := (hShapeAt Z).d,
      MF := (hShapeAt Z).MF, KF := (hShapeAt Z).KF, epsF := (hShapeAt Z).epsF,
      V := (hShapeAt Z).V, sh := (hShapeAt Z).digSh, F := (hShapeAt Z).famF } := rfl

/-- The policy, field by field. -/
theorem policy_fields (Z : ProofFile.Pub) : policyAt Z =
    { C := (hShapeAt Z).clipC, theta := (hShapeAt Z).theta, cap := (hShapeAt Z).cap } := rfl

/-- The seat's request at a state. -/
theorem seat_request (Z : ProofFile.Pub) (s : S) :
    (seatAt (hShapeAt Z) (iU3At Z)).request s = requestOf s := rfl

/-- **The head's plan names the array of reads as array 0, at every o.** -/
theorem third_O {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : OnBytes.Model.Verify.Public}
    (h : publicOfO o pol KL layout = .ok X) : Third X.H.tl := by
  obtain ⟨_, _, _, _, _, H0, h0, e, _⟩ := (publicSteps_of_O h).attention
  rw [e]
  exact planH2_third _ _ _ _ _ _ _ H0 h0

/-- **At the road's value the plan names iU3At Z, and it is 0.** -/
theorem iU3At_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    Z.p.X.H.tl.ix.U.getD 2 none = some (iU3At Z) ∧ iU3At Z = 0 := by
  have t : Z.p.X.H.tl.ix.U.getD 2 none = some 0 := third_O (ProofFile.Law.pub_public h)
  have z : iU3At Z = 0 := by
    unfold iU3At
    rw [t]
    rfl
  exact ⟨by rw [z]; exact t, z⟩

/-- **So the output head's own block at X is blockAt at the closed terms.** -/
theorem block_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (l : Nat) :
    blockOf Z.p.X l = some (blockAt (hShapeAt Z) (iU3At Z) (Law.workOf Z.p.X) l) := by
  unfold blockOf
  rw [(iU3At_made h).1]
  rfl

/-- requestOf reads the words alone. -/
theorem requestOf_congr (a b : S) (h : a.req = b.req) : requestOf a = requestOf b := by
  unfold requestOf S.tokv S.rowR S.rowE S.reqT
  rw [h]

/-- **At every state that holds the words of p.request.** -/
theorem rq_of_req (Z : ProofFile.Pub) (p : ProofFile.InstPub) (s : S)
    (h : s.req = OnBytes.Model.Verify.words32 p.request) : requestOf s = rqAt Z p :=
  requestOf_congr s (Z.s₀.withReq (OnBytes.Model.Verify.words32 p.request)) h

/-- **At the first chain's first state, where the state's tests on the request pass.** -/
theorem rq_start (Z : ProofFile.Pub) (p : ProofFile.InstPub)
    (h : (Z.s₀.withReq (OnBytes.Model.Verify.words32 p.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) :
    requestOf (ProofFile.startS Z p) = rqAt Z p := by
  unfold ProofFile.startS
  simp only [h, if_true]

end VerifiableInference.Desc.Kinds.Head.AtZ

#print axioms VerifiableInference.Desc.Kinds.Head.AtZ.third_O
#print axioms VerifiableInference.Desc.Kinds.Head.AtZ.iU3At_made
#print axioms VerifiableInference.Desc.Kinds.Head.AtZ.block_made
#print axioms VerifiableInference.Desc.Kinds.Head.AtZ.rq_of_req
#print axioms VerifiableInference.Desc.Kinds.Head.AtZ.rq_start
