-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsKeepBits.lean: the bits' masked sumcheck of a lookup's table
side as a job with a kept state (`KeepJob`, Honest/SumKeep.lean), beside the job of
Honest/K3/JobsFast.lean; the three equations between the two; and `KeepJob.FaithfulOn` of it.
Conditional on `BitsOk`: where a store is passed on, its bits' table is the one that
Honest/K3/JobsFast.lean makes. Definitions with code, one definition of a hypothesis, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the stage is `Stage.bits`: mu + d variables, the summand
bit times (bit less 1) under equality weights, one end value: the bits' table at the point of all
challenges. A store is a value of `Store`, a kept state a value of `Kept`
(Honest/K3/KeptTypes.lean).

What is defined.
  `bitsKeep`: the job with a kept state at the stage `Stage.bits`. Its earlier job is `jobOfAt` at
    `fastJobs`, at the call that `Stage.call` gives at that stage. The bits' table is read once and
    the table of the bits less 1 is made once, in `start`. The kept state holds both tables; the end
    value is the first one's.
  `BitsOk`: the hypothesis: `BitOk` (Honest/K3/JobsKeepMore.lean) under the stage's name. Where no
    store is passed on it holds.

What is shown.
  `bitsOk_none`: at no store `BitsOk` holds.
  `bitsKeep_round`, `bitsKeep_ends`, `bitsKeep_inY`: at the kept state made from the start, the
    job's `round`, `ends` and `inY` return what the earlier job's return: at every list of
    challenges. The earlier job binds the bits' table alone for its end value: that this is the
    first of the two tables bound together is `Fast.prodEnds_take`.
  `bitsKeep_faithful`: `(bitsKeep R row a).FaithfulOn (BitsOk R row a)`.

Hypotheses that remain.
  `hOk`: `BitsOk R row a w f.heard f.own`, as the condition of `FaithfulOn`. No store at which it
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
that `BitsOk` stays true as more is heard. As in Honest/K3/JobsFast.lean both factors of the summand
in Y take the first mask entry. `inY` of `bitsKeep` does not reject: a mask entry beyond the list's
end counts as 0. At the list that `sumPart` (the masked sumcheck's part) hands over, entries laid
behind it change nothing in what `inY` returns: `no_pad_at_keep`
(Honest/K3/Law/Keep/MasksAtKeep.lean [not in this library]). That it does read its one entry:
`pad_parts` (Honest/K3/Law/Keep/MasksAtKeepTooth.lean [not in this library]). `inY` and `ends` read
the kept state's values by a default too (`((Fast.keptEnds K).take 1).getD`): nothing here bounds
these. How long either job takes is not said and has not been measured.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeepLaw
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE oneE subE)

/-- The job with a kept state at the stage `Stage.bits`. -/
def bitsKeep (R : Reads) (row : E → Nat → E) (a : At) : KeepJob Ask (Option Store) Kept :=
  { base := jobOfAt R (fastJobs a.face row).asked a .bits
      (VerifiableInference.Desc.K3.bitsCall (List.replicate (a.face.mu + a.face.d) zeroE))
    start := fun w h x =>
      let p := R.pts a.face a.base h
      let b := bitOff a.face row w p x
      Fast.keptStart (a.face.mu + a.face.d) [b, b.map fun x => subE x oneE] p.zeroPt
    bind := Fast.keptBind (OnBytes.Model.orderDefault (a.face.mu + a.face.d))
    round := Fast.keptRound zeroE (a.face.mu + a.face.d)
      (OnBytes.Model.orderDefault (a.face.mu + a.face.d))
    inY := fun K mk =>
      let b := ((Fast.keptEnds K).take 1).getD 0 zeroE
      Fast.mulY zeroE b (subE b oneE) (mk.getD 0 zeroE) (mk.getD 0 zeroE)
    ends := fun K => (Fast.keptEnds K).take 1 }

/-- The hypothesis: where a store is passed on, its bits' table is the one that
Honest/K3/JobsFast.lean makes of the input, the shift and alpha. A definition, meant as a
hypothesis. -/
def BitsOk (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) : Prop :=
  BitOk R row a w h x

/-- Where no store is passed on `BitsOk` holds. -/
theorem bitsOk_none (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn) :
    BitsOk R row a w h none :=
  fun _ e => nomatch e

/-- At the kept state made from the start, `round` returns what the earlier job's returns.
Conditional on `BitsOk`. -/
theorem bitsKeep_round (R : Reads) (row : E → Nat → E) (a : At) (w : Ask)
    (f : Front (Option Store)) (rs : List E) (hOk : BitsOk R row a w f.heard f.own) :
    (bitsKeep R row a).round ((bitsKeep R row a).madeAt w f.heard f.own rs) =
      (bitsKeep R row a).base.round w f rs := by
  show Fast.keptRound zeroE (a.face.mu + a.face.d)
    (OnBytes.Model.orderDefault (a.face.mu + a.face.d))
    (rs.foldl (Fast.keptBind (OnBytes.Model.orderDefault (a.face.mu + a.face.d)))
      (Fast.keptStart (a.face.mu + a.face.d) [_, _] _)) = _
  rw [Fast.prodRound_made, bitOff_ok R row a w f.heard f.own hOk]
  rfl

/-- The same of `ends`. Conditional on `BitsOk`. -/
theorem bitsKeep_ends (R : Reads) (row : E → Nat → E) (a : At) (w : Ask)
    (f : Front (Option Store)) (rs : List E) (hOk : BitsOk R row a w f.heard f.own) :
    (bitsKeep R row a).ends ((bitsKeep R row a).madeAt w f.heard f.own rs) =
      (bitsKeep R row a).base.ends w f rs := by
  show (Fast.keptEnds
    (rs.foldl (Fast.keptBind (OnBytes.Model.orderDefault (a.face.mu + a.face.d)))
      (Fast.keptStart (a.face.mu + a.face.d) [_, _] _))).take 1 = _
  rw [Fast.prodEnds_made, ← Fast.prodEnds_take, bitOff_ok R row a w f.heard f.own hOk]
  rfl

/-- The same of `inY`. Conditional on `BitsOk`. -/
theorem bitsKeep_inY (R : Reads) (row : E → Nat → E) (a : At) (w : Ask)
    (f : Front (Option Store)) (rs m : List E) (hOk : BitsOk R row a w f.heard f.own) :
    (bitsKeep R row a).inY ((bitsKeep R row a).madeAt w f.heard f.own rs) m =
      (bitsKeep R row a).base.inY w f rs m := by
  have e := bitsKeep_ends R row a w f rs hOk
  show Fast.mulY zeroE
    (((bitsKeep R row a).ends ((bitsKeep R row a).madeAt w f.heard f.own rs)).getD 0 zeroE)
    (subE (((bitsKeep R row a).ends ((bitsKeep R row a).madeAt w f.heard f.own rs)).getD 0 zeroE)
      oneE)
    (m.getD 0 zeroE) (m.getD 0 zeroE) = _
  rw [e]
  rfl

/-- **The kept state gives what the earlier job computes**, wherever `BitsOk` holds. Conditional on
`BitsOk`, as the condition of `KeepJob.FaithfulOn`. -/
theorem bitsKeep_faithful (R : Reads) (row : E → Nat → E) (a : At) :
    (bitsKeep R row a).FaithfulOn (BitsOk R row a) :=
  ⟨fun w f rs hOk _ => bitsKeep_round R row a w f rs hOk,
    fun w f rs m hOk _ => bitsKeep_inY R row a w f rs m hOk,
    fun w f rs hOk _ => bitsKeep_ends R row a w f rs hOk⟩

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.bitsOk_none
#print axioms ProofFile.Honest.K3.bitsKeep_round
#print axioms ProofFile.Honest.K3.bitsKeep_ends
#print axioms ProofFile.Honest.K3.bitsKeep_inY
#print axioms ProofFile.Honest.K3.bitsKeep_faithful
