-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/SoundAt.lean: the named hypothesis "HoleAt.sound a" of Johnson/Top/OnFilesAt.lean, for
every description whose indices, instances, builder and model are the integer model's and whose
relaxed relation, at built requests, gives the library's relaxed relation with the cost ledger at
exact match.

WHAT THIS WEIGHS. By the first theorem "HoleAt.sound a" holds at the library's relation; that
accepted proofs have witnesses of that relation is the open hypothesis ("HoleAt.proofSound a"): the
weight lies there and in the premise on the relation together. The second theorem splits
"HoleAt.sound a" into 26 names and a premise; for some mx these say exactly that every witness of
Rno is true under the policy: nothing is made smaller. For the programs the meaning is not proved.
The statements over Johnson/Top/InnerCompiledVerifier.lean name another hypothesis, "CompilerSoundnessConditionStatements.sound b": this
file says nothing of it.

The two theorems are those of Johnson/Road/Lane5SoundFour.lean at the letters a.I, a.X, a.build,
a.nextToken, a.Wn, a.Rno; that file names no description, so it serves other statements of the same
form as well. "ReadsModel a.build a.nextToken scales" holds a map "idx" from a's indices to the
well-formed tables of weights, a map from a's instances to the model's requests, and two laws on
builder and model. "idx" is total and the model's law is asked at every index: a description whose
indices are arbitrary matrices meets this only if its model is defined through "idx" and its
relation fails wherever the matrix holds no well-formed table; where the decoder gives well-formed
tables alone, that they are well formed lies in "HoleAt.keySound a".

Main theorems (namespace "VerifiableInference.OnPublicFiles"):
* "HoleAt.sound_of_ledger": from witnesses of "Policy.LedgerRel.Rno" at the protocol's prime and
  "AcceptancePolicy.exact", at a lawful table of scales.
* "HoleAt.sound_of_meanHoles": from the 26 named hypotheses "MeanHoles".

Limits: those of Johnson/Road/Lane5SoundFour.lean. No description is given here, and none is shown
to have "ReadsModel" or a premise on its relation. No theorem of the top is fed with these two.
"wit" reads the witness alone. At the inputs of Johnson/Flat/TwoSizes.lean the witnesses are one
point ("relationsAndEncodingOfClaims", OnBytes/Flat/FilesAt.lean), so there the premise asks one trace that serves every
index and every built request: it cannot be looked for there. "HoleAt.proofSound a" reads the same
relation: a relation filled tighter than what the protocol enforces makes that hypothesis false,
one filled looser makes the premise here false.

-/
import Johnson.Top.OnFilesAt
import Johnson.Road.Lane5SoundFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open VerifiableInference.OnPublicFiles

variable (a : DescriptionAt)

/-- **"HoleAt.sound a", from the relaxed relation with the cost ledger at exact match.** -/
theorem _root_.VerifiableInference.OnPublicFiles.HoleAt.sound_of_ledger {scales : Cm.Scales}
    (lawful : scales.Lawful) (R : ReadsModel a.build a.nextToken scales)
    (wit : a.Wn → Inst.Model.All.Trace)
    (hR : ∀ i x' b x w, a.build x' b = some x → a.Rno i x w →
      Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf scales AcceptancePolicy.exact) (R.idx i) (R.req x) (wit w)) :
    HoleAt.sound a := by
  intro i x' b x hb hw
  exact sound_four_of_ledger lawful R wit hR i x' b x hb hw

/-- **"HoleAt.sound a", from the named hypotheses by group.** -/
theorem _root_.VerifiableInference.OnPublicFiles.HoleAt.sound_of_meanHoles {scales : Cm.Scales}
    (lawful : scales.Lawful) (R : ReadsModel a.build a.nextToken scales)
    {Rno : Cm.Idx → Instance ppref → a.Wn → Prop}
    {mx : Cm.Idx → Instance ppref → a.Wn → ℕ → Mx}
    (hR : ∀ i x' b x w, a.build x' b = some x → a.Rno i x w → Rno (R.idx i) (R.req x) w)
    (H : MeanHoles scales AcceptancePolicy.exact Rno mx) : HoleAt.sound a := by
  intro i x' b x hb hw
  exact sound_four_of_meanHoles lawful R hR H i x' b x hb hw

end OnBytes.Road.L5

#print axioms VerifiableInference.OnPublicFiles.HoleAt.sound_of_ledger
#print axioms VerifiableInference.OnPublicFiles.HoleAt.sound_of_meanHoles
