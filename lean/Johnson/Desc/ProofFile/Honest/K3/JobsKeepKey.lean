-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsKeepKey.lean: a level of a lookup's key tree as a job with a
kept state (`KeepJob`, Honest/SumKeep.lean), beside the job of Honest/K3/JobsFast.lean; and the
three equations between the two. Conditional on `KeyOk`: where a store is passed on, its level below
is the one that Honest/K3/JobsFast.lean makes. Definitions with code, one definition of a
hypothesis, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the level below the level with k variables is the level
with k + 1 variables: the stage's two tables are its lower and its upper half. A store is a value of
`Store`, a kept state a value of `Kept` (Honest/K3/KeptTypes.lean).

What is defined.
  `jobOfAt`: the text of `jobOf` (Honest/K3/Row.lean) at any type of what is passed on; none of its
    functions reads what is passed on.
  `keyBelow`: a level of a part's key tree: off the store where one is passed on, made anew where
    none is.
  `keyKeep`: the job with a kept state at the stage `Stage.key i k`. Its earlier job is `jobOfAt` at
    `fastJobs`.
  `KeyOk`: the hypothesis. Where no store is passed on it holds.

What is shown.
  `jobOfAt_unit`: at `Unit` it is `jobOf`: by `rfl`.
  `keyBelow_ok`: under `KeyOk` the level that `keyKeep` starts from is the one that
    Honest/K3/JobsFast.lean makes.
  `keyKeep_round`, `keyKeep_inY`, `keyKeep_ends`: at the kept state made from the start, the job's
    `round`, `inY` and `ends` return what the earlier job's return: at every list of challenges.

Hypotheses that remain.
  `hOk`: `KeyOk R row a i k w f.heard f.own`. No store at which it holds is exhibited in this file;
    at `none` it holds. Shown in: Honest/K3/JobsKeepKeyLaw.lean (`keyOk_none`).

Imported: Honest/SumKeep.lean, and through it and Honest/K3/Row.lean the files Honest/Sum.lean,
Honest/Side.lean, Honest/Frame.lean and Honest/ForKinds.lean.

Users. Honest/K3/JobsKeepKeyLaw.lean; Honest/K3/RowKeepFill.lean; for `jobOfAt` the files on the
other sorts of stage. The three equations have the form of the three fields of `KeepJob.FaithfulOn`
(Honest/SumKeepLaw.lean; not imported here), without that structure's
hypotheses on the number of challenges. That the forms fit is shown in:
Honest/K3/JobsKeepKeyLaw.lean (`keyKeep_faithful`).

Limits. One sort of stage. Nothing is said on who makes a store, nor that `KeyOk` stays true as more
is heard. `inY` of `keyKeep` does not reject: a mask entry beyond the list's end counts as 0. At the
list that `sumPart` (the masked sumcheck's part) hands over, entries laid behind it change nothing
in what `inY` returns: `no_pad_at_keep` (Honest/K3/Law/Keep/MasksAtKeep.lean [not in this library]).
`inY` and `ends` read the kept state's values by a default too (`(Fast.keptEnds K).getD`, and
`Fast.keptEnds` itself reads each table's first entry so): nothing here bounds these. How long
either job takes is not said and has not been measured.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeep
import Johnson.Desc.ProofFile.Honest.K3.Row
import Johnson.Desc.ProofFile.Honest.K3.JobsKeep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)
open VerifiableInference.Desc.Part.MaskedSum (Call)

/-- The text of `jobOf` at any type X of what is passed on. -/
def jobOfAt {W X : Type} (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (k : Call) :
    SumJob W X :=
  { shape := k
    points := fun _ fr => R.pointsAt a.face s (R.pts a.face a.base fr.heard)
    lead := fun _ _ => []
    round := fun w fr rs => (J.job s).round w (R.pts a.face a.base fr.heard) rs
    inY := fun w fr rs m => (J.job s).inY w (R.pts a.face a.base fr.heard) rs m
    ends := fun w fr rs => (J.job s).ends w (R.pts a.face a.base fr.heard) rs }

/-- At `Unit` it is `jobOf`. -/
theorem jobOfAt_unit {W : Type} (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (k : Call) :
    jobOfAt (X := Unit) R J a s k = jobOf R J a s k := rfl

/-- The level with m variables of part i's key tree: off the store where one is passed on, made anew
where none is. The input w is applied to the challenges in the second case alone: an application can
be costly (on the digits it goes through all keys), and Lean's code evaluates an argument before the
call. -/
def keyBelow (f : LFace) (row : E → Nat → E) (i m : Nat) (w : Ask) (p : Pts) :
    Option Store → Array E
  | some st => (st.keyLvls.getD i #[]).getD m #[]
  | none => (Fast.srcOf f row (w p.heard) p.theta p.alpha).keyLvl i m

/-- The job with a kept state at the stage `Stage.key i k`. -/
def keyKeep (R : Reads) (row : E → Nat → E) (a : At) (i k : Nat) :
    KeepJob Ask (Option Store) Kept :=
  { base := jobOfAt R (fastJobs a.face row).asked a (.key i k) (levelCall k)
    start := fun w h x =>
      let p := R.pts a.face a.base h
      let n := keyBelow a.face row i (k + 1) w p x
      Fast.keptStart k [n.extract 0 (2 ^ k), n.extract (2 ^ k) (2 ^ (k + 1))] (p.keyPt i k)
    bind := Fast.keptBind (a.face.orders i k)
    round := Fast.keptRound zeroE k (a.face.orders i k)
    inY := fun K mk =>
      let e := Fast.keptEnds K
      Fast.mulY zeroE (e.getD 0 zeroE) (e.getD 1 zeroE) (mk.getD 0 zeroE) (mk.getD 1 zeroE)
    ends := Fast.keptEnds }

/-- The hypothesis: where a store is passed on, its level below is the one that
Honest/K3/JobsFast.lean makes of the input, the shift and alpha. A definition, meant as a
hypothesis. -/
def KeyOk (R : Reads) (row : E → Nat → E) (a : At) (i k : Nat) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) : Prop :=
  ∀ st, x = some st → (st.keyLvls.getD i #[]).getD (k + 1) #[] =
    (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
      (R.pts a.face a.base h).alpha).keyLvl i (k + 1)

/-- Under `KeyOk` the level that `keyKeep` starts from is the one that Honest/K3/JobsFast.lean
makes. -/
theorem keyBelow_ok (R : Reads) (row : E → Nat → E) (a : At) (i k : Nat) (w : Ask)
    (h : List Fmt.Drawn) (x : Option Store) (hOk : KeyOk R row a i k w h x) :
    keyBelow a.face row i (k + 1) w (R.pts a.face a.base h) x =
      (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
        (R.pts a.face a.base h).alpha).keyLvl i (k + 1) := by
  cases x with
  | none => rfl
  | some st => exact hOk st rfl

/-- At the kept state made from the start, `round` returns what the earlier job's returns.
Conditional on `KeyOk`. -/
theorem keyKeep_round (R : Reads) (row : E → Nat → E) (a : At) (i k : Nat) (w : Ask)
    (f : Front (Option Store)) (rs : List E) (hOk : KeyOk R row a i k w f.heard f.own) :
    (keyKeep R row a i k).round ((keyKeep R row a i k).madeAt w f.heard f.own rs) =
      (keyKeep R row a i k).base.round w f rs := by
  show Fast.keptRound zeroE k (a.face.orders i k) (rs.foldl (Fast.keptBind (a.face.orders i k))
    (Fast.keptStart k [_, _] _)) = _
  rw [Fast.prodRound_made, keyBelow_ok R row a i k w f.heard f.own hOk]
  rfl

/-- The same of `ends`. Conditional on `KeyOk`. -/
theorem keyKeep_ends (R : Reads) (row : E → Nat → E) (a : At) (i k : Nat) (w : Ask)
    (f : Front (Option Store)) (rs : List E) (hOk : KeyOk R row a i k w f.heard f.own) :
    (keyKeep R row a i k).ends ((keyKeep R row a i k).madeAt w f.heard f.own rs) =
      (keyKeep R row a i k).base.ends w f rs := by
  show Fast.keptEnds (rs.foldl (Fast.keptBind (a.face.orders i k))
    (Fast.keptStart k [_, _] _)) = _
  rw [Fast.prodEnds_made, keyBelow_ok R row a i k w f.heard f.own hOk]
  rfl

/-- The same of `inY`. Conditional on `KeyOk`. -/
theorem keyKeep_inY (R : Reads) (row : E → Nat → E) (a : At) (i k : Nat) (w : Ask)
    (f : Front (Option Store)) (rs m : List E) (hOk : KeyOk R row a i k w f.heard f.own) :
    (keyKeep R row a i k).inY ((keyKeep R row a i k).madeAt w f.heard f.own rs) m =
      (keyKeep R row a i k).base.inY w f rs m := by
  have e := keyKeep_ends R row a i k w f rs hOk
  show Fast.mulY zeroE
    (((keyKeep R row a i k).ends ((keyKeep R row a i k).madeAt w f.heard f.own rs)).getD 0 zeroE)
    (((keyKeep R row a i k).ends ((keyKeep R row a i k).madeAt w f.heard f.own rs)).getD 1 zeroE)
    (m.getD 0 zeroE) (m.getD 1 zeroE) = _
  rw [e]
  rfl

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.jobOfAt_unit
#print axioms ProofFile.Honest.K3.keyBelow_ok
#print axioms ProofFile.Honest.K3.keyKeep_round
#print axioms ProofFile.Honest.K3.keyKeep_ends
#print axioms ProofFile.Honest.K3.keyKeep_inY
