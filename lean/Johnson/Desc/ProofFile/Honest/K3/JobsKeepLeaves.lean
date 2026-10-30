-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsKeepLeaves.lean: the leaves' masked sumcheck of a lookup's
table side as a job with a kept state (`KeepJob`, Honest/SumKeep.lean), beside the job of
Honest/K3/JobsFast.lean; the three equations between the two; and `KeepJob.FaithfulOn` of it.
Conditional on `LeavesOk`: where a store is passed on, its bits' table and its factors' table are
the ones that Honest/K3/JobsFast.lean makes. Definitions with code, one definition of a hypothesis,
and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the stage is `Stage.leaves`: mu + d variables, the
summand 1 + bit times factor under equality weights, no end value. A store is a value of `Store`, a
kept state a value of `Kept` (Honest/K3/KeptTypes.lean).

What is defined.
  `leafOff`: the bits' table and the factors' table: off the store where one is passed on, made anew
    where none is. It takes the input as a function of the challenges heard (`Ask`) and applies it
    only where no store is passed on, once: an application may be costly.
  `leavesKeep`: the job with a kept state at the stage `Stage.leaves`. Its earlier job is `jobOfAt`
    at `fastJobs`, at the call that `Stage.call` gives at that stage. The two tables are read once,
    in `start`. As in Honest/K3/JobsFast.lean a round sends three coefficients while fewer than d
    rounds are bound, and two from then on: the number of rounds bound is read off the kept state.
  `LeavesOk`: the hypothesis. Where no store is passed on it holds.

What is shown.
  `leavesOk_none`: at no store `LeavesOk` holds.
  `LeavesOk.bit`: `LeavesOk` gives `BitOk` (Honest/K3/JobsKeepMore.lean).
  `leafOff_ok`: under `LeavesOk` the two tables that `leavesKeep` starts from are the ones that
    Honest/K3/JobsFast.lean makes.
  `leavesKeep_round`: at the kept state made from the start, the job's `round` returns what the
    earlier job's returns: at every list of challenges. Conditional on `LeavesOk`.
  `leavesKeep_inY`, `leavesKeep_ends`: the same of `inY` and `ends`: both sides are the empty list;
    without a hypothesis.
  `leavesKeep_faithful`: `(leavesKeep R row a).FaithfulOn (LeavesOk R row a)`.

Hypotheses that remain.
  `hOk`: `LeavesOk R row a w f.heard f.own`, as the condition of `FaithfulOn`. No store at which it
    holds is exhibited in this file; at `none` it holds.

Imported. Honest/SumKeepLaw.lean for `KeepJob.FaithfulOn`;
Honest/K3/JobsKeepMore.lean. Through them Honest/SumKeep.lean, Honest/SumLaw/Said.lean,
Honest/Sum.lean, Honest/Side.lean, Honest/Frame.lean and Honest/ForKinds.lean.

Users. Honest/K3/RowKeepFill.lean (the filling of `Keeps`, Honest/K3/RowKeep.lean),
Honest/K3/Law/Keep/StoreGives.lean (the hypothesis at the lookup's store),
Honest/K3/Law/Keep/SameRounds.lean. Honest/K3/JobsKeepTopToy.lean [not in this library] tries
numbers.

Limits. One stage. The earlier job is `jobOfAt` at `Option Store`; `lookRow` plays `jobOf`, at
`Unit`: what ties the parts of the two is not shown here: it is `alone_jobOfAt`
(Honest/K3/Law/Keep/Bridge.lean). Nothing is said on who makes a store, nor
that `LeavesOk` stays true as more is heard. How long either job takes is not said and has not been
measured.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeepLaw
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE oneE)

/-- The bits' table and the table of alpha - 1 - row, by the leaf's number: off the store where one
is passed on, made anew where none is. The input is asked for in the second case alone, once. -/
def leafOff (f : LFace) (row : E → Nat → E) (w : Ask) (p : Pts) :
    Option Store → Array E × Array E
  | some st => (st.bitTab, st.facTab)
  | none =>
    let S := Fast.srcOf f row (w p.heard) p.theta p.alpha
    (S.bitTab (), S.facTab ())

/-- The job with a kept state at the stage `Stage.leaves`. -/
def leavesKeep (R : Reads) (row : E → Nat → E) (a : At) : KeepJob Ask (Option Store) Kept :=
  { base := jobOfAt R (fastJobs a.face row).asked a .leaves
      { lead := 0, vs := VerifiableInference.Desc.K3.leafVars a.face #[], ends := none }
    start := fun w h x =>
      let p := R.pts a.face a.base h
      let t := leafOff a.face row w p x
      Fast.keptStart (a.face.mu + a.face.d) [t.1, t.2] (p.tabPt a.face.d)
    bind := Fast.keptBind (OnBytes.Model.orderDefault (a.face.mu + a.face.d))
    round := fun K =>
      (Fast.keptRound oneE (a.face.mu + a.face.d)
        (OnBytes.Model.orderDefault (a.face.mu + a.face.d)) K).take
        (if K.bound < a.face.d then 3 else 2)
    inY := fun _ _ => []
    ends := fun _ => [] }

/-- The hypothesis: where a store is passed on, its bits' table and its factors' table are the ones
that Honest/K3/JobsFast.lean makes of the input, the shift and alpha. A definition, meant as a
hypothesis. -/
def LeavesOk (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) : Prop :=
  ∀ st, x = some st →
    st.bitTab =
      (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
        (R.pts a.face a.base h).alpha).bitTab () ∧
    st.facTab =
      (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
        (R.pts a.face a.base h).alpha).facTab ()

/-- Where no store is passed on `LeavesOk` holds. -/
theorem leavesOk_none (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn) :
    LeavesOk R row a w h none :=
  fun _ e => nomatch e

/-- `LeavesOk` gives `BitOk`. -/
theorem LeavesOk.bit {R : Reads} {row : E → Nat → E} {a : At} {w : Ask} {h : List Fmt.Drawn}
    {x : Option Store} (hOk : LeavesOk R row a w h x) : BitOk R row a w h x :=
  fun st e => (hOk st e).1

/-- Under `LeavesOk` the tables that `leafOff` returns are the ones that Honest/K3/JobsFast.lean
makes. Conditional on `LeavesOk`. -/
theorem leafOff_ok (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) (hOk : LeavesOk R row a w h x) :
    leafOff a.face row w (R.pts a.face a.base h) x =
      ((Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
          (R.pts a.face a.base h).alpha).bitTab (),
        (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
          (R.pts a.face a.base h).alpha).facTab ()) := by
  cases x with
  | none => rfl
  | some st => exact Prod.ext (hOk st rfl).1 (hOk st rfl).2

/-- At the kept state made from the start, `round` returns what the earlier job's returns.
Conditional on `LeavesOk`. -/
theorem leavesKeep_round (R : Reads) (row : E → Nat → E) (a : At) (w : Ask)
    (f : Front (Option Store)) (rs : List E) (hOk : LeavesOk R row a w f.heard f.own) :
    (leavesKeep R row a).round ((leavesKeep R row a).madeAt w f.heard f.own rs) =
      (leavesKeep R row a).base.round w f rs := by
  show (Fast.keptRound oneE (a.face.mu + a.face.d)
      (OnBytes.Model.orderDefault (a.face.mu + a.face.d))
      (rs.foldl (Fast.keptBind (OnBytes.Model.orderDefault (a.face.mu + a.face.d)))
        (Fast.keptStart (a.face.mu + a.face.d) [_, _] _))).take
    (if (rs.foldl (Fast.keptBind (OnBytes.Model.orderDefault (a.face.mu + a.face.d)))
        (Fast.keptStart (a.face.mu + a.face.d) [_, _] _)).bound < a.face.d then 3 else 2) = _
  rw [Fast.prodRound_made, Fast.bound_made, leafOff_ok R row a w f.heard f.own hOk]
  rfl

/-- The same of `ends`: the stage has no end value. -/
theorem leavesKeep_ends (R : Reads) (row : E → Nat → E) (a : At) (w : Ask)
    (f : Front (Option Store)) (rs : List E) :
    (leavesKeep R row a).ends ((leavesKeep R row a).madeAt w f.heard f.own rs) =
      (leavesKeep R row a).base.ends w f rs := rfl

/-- The same of `inY`: the stage has no end value, so nothing is summed in Y. -/
theorem leavesKeep_inY (R : Reads) (row : E → Nat → E) (a : At) (w : Ask)
    (f : Front (Option Store)) (rs m : List E) :
    (leavesKeep R row a).inY ((leavesKeep R row a).madeAt w f.heard f.own rs) m =
      (leavesKeep R row a).base.inY w f rs m := rfl

/-- **The kept state gives what the earlier job computes**, wherever `LeavesOk` holds. Conditional
on `LeavesOk`, as the condition of `KeepJob.FaithfulOn`. -/
theorem leavesKeep_faithful (R : Reads) (row : E → Nat → E) (a : At) :
    (leavesKeep R row a).FaithfulOn (LeavesOk R row a) :=
  ⟨fun w f rs hOk _ => leavesKeep_round R row a w f rs hOk,
    fun w f rs m _ _ => leavesKeep_inY R row a w f rs m,
    fun w f rs _ _ => leavesKeep_ends R row a w f rs⟩

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.leavesOk_none
#print axioms ProofFile.Honest.K3.LeavesOk.bit
#print axioms ProofFile.Honest.K3.leafOff_ok
#print axioms ProofFile.Honest.K3.leavesKeep_round
#print axioms ProofFile.Honest.K3.leavesKeep_ends
#print axioms ProofFile.Honest.K3.leavesKeep_inY
#print axioms ProofFile.Honest.K3.leavesKeep_faithful
