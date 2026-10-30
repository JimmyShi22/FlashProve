-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Merge.lean: the merge, the part of a sub-proof that reduces its claims on the
committed weights to one equation on the matrix.

It follows the C++ verifier's header verifier/src/vf_weights_merge.h and the last type and routine
of verifier/src/vf_weights_layout.h (WsForkOut, wsForkEnd). A type or routine has the name of its
C++ counterpart. wsForkStart and wsForkRounds are two loops
inside the C++ routine wsForkMerge.

A sub-proof of some layers or of the head has claims "the weights of a unit, under given factors,
sum to v_a" (OnBytes/Model/Weights.lean). Each v_a is a hidden value in the sense of
OnBytes/Model/Hide.lean: earlier in the sub-proof the prover has sent it masked, under a slot.

The messages. One element is drawn, whose powers are the coefficients rho_a. Then comes a masked
sumcheck (OnBytes/Model/Psc.lean), which the protocol's pages call zero-knowledge: the prover adds a
random polynomial, the protocol's hiding polynomial. This file follows the verifier's steps and
claims nothing about hiding. The sumcheck's sum must be the sum of rho_a v_a. It has lk plain
rounds, one for each column bit of the matrix, and then one closing round in a further variable
(pscEnds), whose challenge is beta. The summand is treated as one function of the column bits. The
value of that function at the point of the lk rounds' challenges is called fv. The prover does not
send fv: it sends fv' and says that fv' = fv + beta c, where c is a mask entry.

Where it runs. In a layer sub-proof the merge's messages come before those of the smallness test
(OnBytes/Model/Tail.lean), in the head's sub-proof after them. In both, the merge's claim is the
last claim that is added.

What is left. One claim on the sub-proof's own mask entries (wsForkLin), which never names fv. The
claim "fv + beta c = fv'" leaves the sub-proof as a row on the committed matrix
(OnBytes/Model/Pending.lean). In that row c is an entry of the request's index-mask message
(explained at memberPendingRow, OnBytes/Iop/Lin.lean), not of the sub-proof's mask row.

Main definitions: WsMerged, wsForkMerge, wsForkLin, wsForkSlots, WsForkOut, wsForkEnd.

What this file does not claim: no theorem is stated here. Nothing is claimed on soundness or zero
knowledge.
-/
import OnBytes.Model.Psc
import OnBytes.Model.Weights

namespace OnBytes.Model

/-- What the merge's messages leave. C++: WsMerged. -/
structure WsMerged where
  /-- fv', as it was shown -/
  fvp : E := zeroE
  /-- the factor of its mask c -/
  beta : E := zeroE
  /-- the merge's point, the highest column bit first -/
  rm : Array E := #[]
  /-- the state of the merge's sumcheck -/
  p : Psc := {}
  /-- the slot of fv'. No claim of the sub-proof may name it. The mask of fv' is c, an entry of the
  request's index-mask message, so entry sFv of the sub-proof's own mask row masks nothing. -/
  sFv : Nat := 0
  deriving Inhabited

/-- The start of the merge's sumcheck: the sum of rho[a] times the hidden value under sv[a]. -/
def wsForkStart (sv : Array Nat) (rho : Array E) : Aff :=
  (sv.zip rho).foldl (fun s y => Aff.addMul s (Aff.slot y.1) y.2) {}

/-- n plain rounds of degree 2. Returns rm with the n new challenges added at its end, and the
sumcheck's state. -/
def wsForkRounds : Nat → Array E → Psc → SubM (Array E × Psc)
  | 0, rm, p => pure (rm, p)
  | n + 1, rm, p => do
    let (r, p) ← roundIn .sum2 p
    wsForkRounds n (rm.push r) p

/-- The merge's messages. sv[a] is the slot of v_a. Returns what they leave, and the coefficients
rho. C++: wsForkMerge. -/
def wsForkMerge (lk : Nat) (sv : Array Nat) : SubM (WsMerged × Array E) := do
  let rho ← SubM.batch sv.size
  let p ← pscBegin (wsForkStart sv rho)
  let (rm, p) ← wsForkRounds lk (Array.emptyWithCapacity lk) p
  let (sFv, p) ← pscEnds p 1 1
  let fvp ← SubM.shown sFv
  -- pscEnds has just added beta to p.r, so the default is never used.
  pure ({ fvp := fvp, beta := p.r.back?.getD zeroE, rm := rm, p := p, sFv := sFv }, rho)

/-- Adds the merge's claim, the sub-proof's last. The state that pscRow returns is dropped: nothing
uses the sumcheck after this claim. C++: wsForkLin. -/
def wsForkLin (o : WsMerged) : SubM Unit := do
  let (row, _) ← pscRow o.p o.fvp
  SubM.lin row

/-- The number of the merge's slots, that of fv' among them. The slots of the v_a are counted where
they are shown. C++: wsForkSlots. -/
def wsForkSlots (lk : Nat) : Nat := sumcheckSlots .sum2 lk 1 1

/-- What wsForkEnd returns: the merge, and recs, what is left of each claim for the row on the
committed matrix. C++: WsForkOut, whose member rec is recs here. -/
structure WsForkOut extends WsMerged where
  /-- what is left of each claim, in the claims' order -/
  recs : List WsRecClaim := []
  deriving Inhabited

/-- For a sub-proof with claims on the weights: tests the number of the claims (1 to 4096, with one
slot for each) and their sizes, runs the merge (wsForkMerge) and forms what is left of each claim.
cl: the claims; sv[a]: the slot of v_a. The scalar of claim a is rho[a] times the value of its
factors on the columns at the merge's point. The merge's claim is not added here: the caller adds it
by wsForkLin. C++: wsForkEnd, which tests claim by claim, so with two faulty claims the name can
differ. -/
def wsForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) : SubM WsForkOut := do
  mustAs "internal-claim-count" (!cl.isEmpty && cl.size ≤ 4096 && sv.size == cl.size)
  mustAs "internal-claim-unit" (cl.all fun c => c.ui < lay.U.size)
  mustAs "internal-claim-factors" (cl.all fun c => (wsClaimShape lay c).isOk)
  let (o, rho) ← wsForkMerge lay.lk sv
  pure {
    toWsMerged := o
    recs := (cl.zip rho).toList.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 o.rm)) }

/-- The names under which the functions of this file refuse: those that the C++ verifier gives to
the same refusals. A failure carries its name out of the run (refuse, OnBytes/Model/Frame.lean). The
C++ puts the sub-proof's name in front of the first. -/
def Merge.names : List String :=
  ["internal-claim-count", "internal-claim-unit", "internal-claim-factors"]

end OnBytes.Model
