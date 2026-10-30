-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/HearsShape.lean: CONDITIONAL. One definition of a hypothesis's
form, and one statement with its proof.

What is here. THE HYPOTHESIS `K4ReadyP` (Law/Hears.lean: what the
accepting decision of K4, the sub-protocol of the feed-forward layers' own rounds, asks of the
verifier's state in front) BROUGHT DOWN FURTHER: where what the lookup has heard has the plan's own
shape, four of its clauses go (shape · the depth in hands · planes · join): the first by that
equation alone, the other three by five tests on the plan alone and one size more of what the lookup
has heard (weights). The test `k4ShapeB` is defined in Law/PublicX.lean.

  `k4ShapeB p` (Law/PublicX.lean)   FIVE TESTS WITH CODE ON THE PLAN ALONE: the host's count of the
      padding keys is the layout's (the host: the sub-protocol that calls the lookup) · each call's
      factor in the join is there, at the array and the places that the plan names · the planes'
      columns at the plan's shape · the depth · the shape's number of calls. An evaluation gives no
      term of `k4ShapeB p = true`. Under h, the hypothesis on the public files (`P5J.AtMgA`), all
      five are proved at each group's plan (`shapeB_head`, Law/DearX.lean).
  `K4ReadyS p s`   THE STATE IN FRONT. CLAUSE BY CLAUSE (mark and owed are fields; the rest are the
      clauses of the field more): mark: the thread's form · owed, room: the promise in front · look:
      the promise's item on the lookup · **shape: what the lookup has heard has the plan's shape**
      (the sixth fact of the library's `K4Fence`): out of the promise in front
      (Law/LookOfPromise.lean) · z, zt, ztSize, zk: SIZES of what the lookup has heard: likewise,
      with comparisons of public numbers (la ≤ dT · lt ≤ dT) · ends, merged, weights (`K4LookRest`,
      Law/LookOfPromise.lean: a reading, one equation and a size): under h wherever the first
      chain's thread stands there, by a statement of the writers of Honest/K3/ (Law/LookJoin.lean,
      Law/ReadyHead.lean) · cEnd: the promise's item on the lookup, with the room · tokens: under h
      and `LaidK4`, wherever the first chain's thread stands in front of the member
      (Law/TokensHead.lean): their number and bound alone.
  `k4ReadyP_of_S`   **K4ReadyP from the test and K4ReadyS.**

Called. Another writer's `join_pay` (Johnson/Desc/First/K4/Returns/JoinSkel.lean): the clause on the
start form of the batched sumcheck (`JoinPub`) is had from it. The rest is rewriting by the equation
of shapes.

Kin. `k4ReadyS_of_tests` (Law/ReadyOfPromise.lean) and `k4ReadyS_of_promise`
(Law/LookOfPromise.lean) end in `K4ReadyS`, out of the promise's tests; `k4_heard_head`
(Law/ReadyHead.lean) has the like equation to the field shape's, at the public parameters' layout,
wherever `lettersHead`'s thread stands in front of the member.

Not shown here. That the test is true at any plan, and that `K4ReadyS` holds at any state:
hypotheses; the list above says of each field where it is shown. This file gives no example of its
hypotheses together. Following import lines, and stopping unopened at every module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins
Cb.Bridge, its imports reach 2 modules under Johnson/Bridge/ and none of the others; what lies
behind the two is not counted; one of the modules that it reaches has RecCompile in its name
(Johnson.TypedOracleCompiler.RecCompile.Bcs), which is not RecCompile's Honest*, Both or PassH*. Nothing on
soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Hears
import Johnson.Desc.First.K4.Returns.JoinSkel
import Johnson.Desc.ProofFile.Honest.K4.Law.PublicX

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E)
open D6.Ret (Room)
open OnBytes.Model (Forest.Heard lastOf)
open OnBytes.Desc.First.K4 (Par seatS shapeFits)
open OnBytes.Desc.First.K4.Rt (k4Takes K3Hands joinB join_pay)
open OnBytes.Desc.First.K4.RtPub (zkFits tokensFit tablesAt)
open VerifiableInference.Desc (First.S)
open VerifiableInference.Desc.First.Look (laidLayers)

/-- **What is asked of the verifier's state in front of the member**, where the lookup's shape is
the plan's. This defines a hypothesis; the definition claims nothing. -/
structure K4ReadyS (p : Par) (s : First.S) : Prop where
  mark : s.failed = none
  owed : (seatS.owed s).isNone = true
  more : ∃ (fo : Forest.Heard) (k : Nat) (Z ztF : Array E) (ends : Array (Array E)),
    seatS.look s = some fo ∧ fo.shape = p.P.y.fo ∧
      Room (seatS.fork s) (k4Takes p.P p.hp p.g + k) ∧
      (lastOf fo.zx p.P.y.h.la).toOption = some Z ∧
      (fo.zk.mapM fun zk => (lastOf zk p.P.y.h.la).toOption) = some ends ∧
      (lastOf fo.zx p.P.y.h.lt).toOption = some ztF ∧ ztF.size = p.P.y.h.lt ∧
      OnBytes.Desc.First.K4.Rt.Shown (seatS.fork s) fo.cEnd ∧ zkFits p.P fo.zk = true ∧
      fo.e.size = p.P.y.calls.size ∧ ends.all (· == Z) = true ∧
      tokensFit { p.P with tokv := seatS.tokv s } p.g = true

/-- **The finer form gives the coarser**, where the test `k4ShapeB` accepts (hB). -/
theorem k4ReadyP_of_S {p : Par} {s : First.S} (hB : k4ShapeB p = true) (R : K4ReadyS p s) :
    K4ReadyP p s := by
  obtain ⟨hm, h0, fo, k, Z, ztF, ends, h3, hsh, hR, hz, he, hzt, hzs, hce, hzk, hw, vM, hk⟩ := R
  unfold k4ShapeB at hB
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
  obtain ⟨⟨⟨⟨hL, hJ⟩, hpc⟩, hd⟩, hcs⟩ := hB
  refine ⟨hm, h0, fo, k, Z, ztF, ends, h3, ?_, hR, ⟨by rw [hsh]; exact hd, hz, he, hzt, hzs, hce⟩,
    hzk, by rw [hsh]; exact hpc, ?_, vM, hk⟩
  · unfold shapeFits
    rw [hsh]
    simp
  · intro iU3 tab laid n hu ht
    rw [hu, ht] at hJ
    exact join_pay (P := { p.P with tokv := seatS.tokv s }) hL hJ (by rw [hsh]; exact hcs) hw
      (by rw [hsh]) (by rw [hsh])

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.K4ReadyS
#print axioms ProofFile.Honest.K4.k4ReadyP_of_S
