-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsKeepTab.lean: a level of a lookup's table side as a job with a
kept state (`KeepJob`, Honest/SumKeep.lean), beside the job of Honest/K3/JobsFast.lean; the three
equations between the two; and `KeepJob.FaithfulOn` (Honest/SumKeepLaw.lean) of it. Conditional on
`TabOk`: where a store is passed on, its level below is the one that Honest/K3/JobsFast.lean makes.
Definitions with code, one definition of a hypothesis, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the table side's level number l has mu + l variables;
the level below it is the level number l + 1: the stage's two tables are its lower and its upper
half. A store is a value of `Store`, a kept state a value of `Kept` (Honest/K3/KeptTypes.lean).

After. Honest/K3/JobsKeepKey.lean, which does the same for a level of a part's key tree: its text,
with the number of variables mu + l, the order `orderDefault (mu + l)`, the table side's levels and
the point `Pts.tabPt l`.

What is defined.
  `tabBelow`: a level of the table side: off the store where one is passed on, made anew where none
    is. It is handed the input as a function of the challenges (`Ask`) and applies it where no store
    is passed on alone: an application can be costly (Honest/K3/JobsKeepTieToy.lean
    [not in this library] tries that).
  `tabKeep`: the job with a kept state at the stage `Stage.tab l`. Its earlier job is `jobOfAt` at
    `fastJobs`, with the call that `Stage.call` gives at that stage.
  `TabOk`: the hypothesis.

What is shown.
  `tabOk_none`: where no store is passed on, `TabOk` holds.
  `tabKeep_call`: the shape of the earlier job is the call of `Stage.call`: by `rfl`.
  `tabBelow_ok`: under `TabOk` the level that `tabKeep` starts from is the one that
    Honest/K3/JobsFast.lean makes.
  `tabKeep_round`, `tabKeep_inY`, `tabKeep_ends`: at the kept state made from the start, the job's
    `round`, `inY` and `ends` return what the earlier job's return: at every list of challenges.
  `tabKeep_faithful`: `KeepJob.FaithfulOn` of `tabKeep` at `TabOk`. That structure's hypotheses on
    the number of challenges are not used.

Hypotheses that remain.
  `TabOk R row a l w f.heard f.own`: in the three equations as `hOk`, in `tabKeep_faithful` as the
    second argument of `FaithfulOn`. No store at which it holds is exhibited in this file; at `none`
    it holds.

Imported: Honest/SumKeepLaw.lean and Honest/SumKeep.lean, and through them and Honest/K3/Row.lean
the files Honest/Sum.lean, Honest/Side.lean, Honest/Frame.lean and Honest/ForKinds.lean.

Users. Honest/K3/RowKeepFill.lean (`fastKeeps`); Honest/K3/JobsKeepTie.lean (`tabBelow`);
Honest/K3/JobsKeepTieToy.lean [not in this library] (numbers).

Limits. One sort of stage. The earlier job is typed at `Option Store`; the row of `lookRow` plays
`jobOf`, typed at `Unit`: that `sumPart` at the two jobs shows the same rounds is shown in
Honest/K3/Law/Keep/Bridge.lean (`alone_jobOfAt`). Nothing is said on who makes a store, nor that
`TabOk` stays true as more is heard. l is any number: nothing asks that the stage stands in the row
(l below d). `inY` of `tabKeep` does not reject: a mask entry beyond the list's end counts as 0. At
the list that `sumPart` (the masked sumcheck's part) hands over, entries laid behind it change
nothing in what `inY` returns: `no_pad_at_keep` (Honest/K3/Law/Keep/MasksAtKeep.lean
[not in this library]). `inY` and `ends` read the kept state's values by a default too
(`(Fast.keptEnds K).getD`, and `Fast.keptEnds` itself reads each table's first entry so): nothing
here bounds these. How long either job takes is not said and has not been measured.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeepLaw
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)

/-- The table side's level number l: off the store where one is passed on, made anew where none is.
The input w is applied in the second case alone. -/
def tabBelow (f : LFace) (row : E → Nat → E) (l : Nat) (w : Ask) (p : Pts) :
    Option Store → Array E
  | some st => st.tabLvls.getD l #[]
  | none => (Fast.srcOf f row (w p.heard) p.theta p.alpha).tabLvl l

/-- The job with a kept state at the stage `Stage.tab l`. -/
def tabKeep (R : Reads) (row : E → Nat → E) (a : At) (l : Nat) :
    KeepJob Ask (Option Store) Kept :=
  { base := jobOfAt R (fastJobs a.face row).asked a (.tab l) (levelCall (a.face.mu + l))
    start := fun w h x =>
      let p := R.pts a.face a.base h
      let n := tabBelow a.face row (l + 1) w p x
      Fast.keptStart (a.face.mu + l)
        [n.extract 0 (2 ^ (a.face.mu + l)),
          n.extract (2 ^ (a.face.mu + l)) (2 ^ (a.face.mu + l + 1))] (p.tabPt l)
    bind := Fast.keptBind (OnBytes.Model.orderDefault (a.face.mu + l))
    round := Fast.keptRound zeroE (a.face.mu + l) (OnBytes.Model.orderDefault (a.face.mu + l))
    inY := fun K mk =>
      let e := Fast.keptEnds K
      Fast.mulY zeroE (e.getD 0 zeroE) (e.getD 1 zeroE) (mk.getD 0 zeroE) (mk.getD 1 zeroE)
    ends := Fast.keptEnds }

/-- The hypothesis: where a store is passed on, its level below is the one that
Honest/K3/JobsFast.lean makes of the input, the shift and alpha. A definition, meant as a
hypothesis. -/
def TabOk (R : Reads) (row : E → Nat → E) (a : At) (l : Nat) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) : Prop :=
  ∀ st, x = some st → st.tabLvls.getD (l + 1) #[] =
    (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
      (R.pts a.face a.base h).alpha).tabLvl (l + 1)

/-- Where no store is passed on, `TabOk` holds. -/
theorem tabOk_none (R : Reads) (row : E → Nat → E) (a : At) (l : Nat) (w : Ask)
    (h : List Fmt.Drawn) : TabOk R row a l w h none :=
  fun _ e => nomatch e

/-- The shape of the earlier job is the call that `Stage.call` gives at the stage. -/
theorem tabKeep_call (R : Reads) (row : E → Nat → E) (a : At) (l : Nat) :
    (Stage.tab l).call a.face = some (tabKeep R row a l).base.shape := rfl

/-- Under `TabOk` the level that `tabKeep` starts from is the one that Honest/K3/JobsFast.lean
makes. -/
theorem tabBelow_ok (R : Reads) (row : E → Nat → E) (a : At) (l : Nat) (w : Ask)
    (h : List Fmt.Drawn) (x : Option Store) (hOk : TabOk R row a l w h x) :
    tabBelow a.face row (l + 1) w (R.pts a.face a.base h) x =
      (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
        (R.pts a.face a.base h).alpha).tabLvl (l + 1) := by
  cases x with
  | none => rfl
  | some st => exact hOk st rfl

/-- At the kept state made from the start, `round` returns what the earlier job's returns.
Conditional on `TabOk`. -/
theorem tabKeep_round (R : Reads) (row : E → Nat → E) (a : At) (l : Nat) (w : Ask)
    (f : Front (Option Store)) (rs : List E) (hOk : TabOk R row a l w f.heard f.own) :
    (tabKeep R row a l).round ((tabKeep R row a l).madeAt w f.heard f.own rs) =
      (tabKeep R row a l).base.round w f rs := by
  show Fast.keptRound zeroE (a.face.mu + l) (OnBytes.Model.orderDefault (a.face.mu + l))
    (rs.foldl (Fast.keptBind (OnBytes.Model.orderDefault (a.face.mu + l)))
      (Fast.keptStart (a.face.mu + l) [_, _] _)) = _
  rw [Fast.prodRound_made, tabBelow_ok R row a l w f.heard f.own hOk]
  rfl

/-- The same of `ends`. Conditional on `TabOk`. -/
theorem tabKeep_ends (R : Reads) (row : E → Nat → E) (a : At) (l : Nat) (w : Ask)
    (f : Front (Option Store)) (rs : List E) (hOk : TabOk R row a l w f.heard f.own) :
    (tabKeep R row a l).ends ((tabKeep R row a l).madeAt w f.heard f.own rs) =
      (tabKeep R row a l).base.ends w f rs := by
  show Fast.keptEnds (rs.foldl (Fast.keptBind (OnBytes.Model.orderDefault (a.face.mu + l)))
    (Fast.keptStart (a.face.mu + l) [_, _] _)) = _
  rw [Fast.prodEnds_made, tabBelow_ok R row a l w f.heard f.own hOk]
  rfl

/-- The same of `inY`. Conditional on `TabOk`. -/
theorem tabKeep_inY (R : Reads) (row : E → Nat → E) (a : At) (l : Nat) (w : Ask)
    (f : Front (Option Store)) (rs m : List E) (hOk : TabOk R row a l w f.heard f.own) :
    (tabKeep R row a l).inY ((tabKeep R row a l).madeAt w f.heard f.own rs) m =
      (tabKeep R row a l).base.inY w f rs m := by
  have e := tabKeep_ends R row a l w f rs hOk
  show Fast.mulY zeroE
    (((tabKeep R row a l).ends ((tabKeep R row a l).madeAt w f.heard f.own rs)).getD 0 zeroE)
    (((tabKeep R row a l).ends ((tabKeep R row a l).madeAt w f.heard f.own rs)).getD 1 zeroE)
    (m.getD 0 zeroE) (m.getD 1 zeroE) = _
  rw [e]
  rfl

/-- **The kept state of `tabKeep` gives what the earlier job computes.** Conditional on `TabOk`, as
the second argument of `FaithfulOn`. -/
theorem tabKeep_faithful (R : Reads) (row : E → Nat → E) (a : At) (l : Nat) :
    (tabKeep R row a l).FaithfulOn (TabOk R row a l) :=
  ⟨fun w f rs hOk _ => tabKeep_round R row a l w f rs hOk,
    fun w f rs m hOk _ => tabKeep_inY R row a l w f rs m hOk,
    fun w f rs hOk _ => tabKeep_ends R row a l w f rs hOk⟩

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.tabOk_none
#print axioms ProofFile.Honest.K3.tabKeep_call
#print axioms ProofFile.Honest.K3.tabBelow_ok
#print axioms ProofFile.Honest.K3.tabKeep_round
#print axioms ProofFile.Honest.K3.tabKeep_ends
#print axioms ProofFile.Honest.K3.tabKeep_inY
#print axioms ProofFile.Honest.K3.tabKeep_faithful
