-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5SoundFour.lean

"A built instance with a witness has the integer model's output tokens", for any types of indices,
instances and witnesses, any builder, any model and any relation that are tied to the integer model
by two maps, two laws and a premise on the relation.

WHAT THIS WEIGHS. The first theorem is paid at the library's relaxed relation with the cost ledger;
that a protocol's accepted proofs have witnesses of that relation is the open question: the weight
lies there and in the premise on the relation together. The proof is the library's own step from
that relation to "true under the policy" with two lemmas of its front (Lane5SoundLedger.lean). The
second theorem splits the statement into 26 names and a premise hR; for some mx they say exactly
that every witness of Rno is true under the policy ("holes_iff_language", Lane5Holes.lean): nothing
is made smaller. For the programs the meaning is not proved.

The file names no description of a protocol: it is written over the letters I, X, build and
nextToken, with Wn and Rn for witnesses and relation, so that it serves every statement of the form
"build x' b = some x → (∃ w, Rn i x w) → the output tokens are nextToken's".

Main definitions and theorems:
* "ReadsModel build nextToken scales": a map "idx" from I to the well-formed tables of weights
  ("Cm.Idx"), a map "req" from X to the model's requests, and two laws: what build builds is what
  "requestOfTokens" builds; nextToken is "IntegerModel.nextToken" at the table of scales and the
  index's tensors. "idx" is total and the model's law is asked at every index: a description whose
  indices are arbitrary matrices meets this only if its model is defined through "idx" and its
  relation fails wherever the matrix holds no well-formed table; where a decoder gives well-formed
  tables alone, that they are well formed is a matter of the hypothesis on the key file.
* "sound_four_of_ledger": at a lawful table of scales: if, at every built instance, every witness
  of Rn gives a witness of "Policy.LedgerRel.Rno" at the protocol's prime and "AcceptancePolicy.exact", at the
  mapped index and request, then every built instance with a witness has nextToken's output tokens.
* "sound_four_of_meanHoles": the same from the 26 named hypotheses "MeanHoles" (Lane5Holes.lean).

Not claimed: that any builder, model or relation has "ReadsModel" or a premise here. A lawful table
of scales is a premise. The library proves its reference table lawful ("lawful_sRef",
Cm/Rel2Guards.lean). That the words of a scale file give a lawful table is no theorem in this tree.
"wit" reads the witness alone. At the inputs of Johnson/Flat/TwoSizes.lean the witnesses are one
point ("relationsAndEncodingOfClaims", OnBytes/Flat/FilesAt.lean), so there the premise asks one trace that serves every
index and every built request: it cannot be looked for there. All is at the reference sizes and at
exact match.

-/
import Johnson.Road.Lane5SoundLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open VerifiableInference

/-- Indices, instances, a builder and a model are the integer model's. -/
structure ReadsModel {I X : Type} (build : List Token × List Token → List Token → Option X)
    (nextToken : I → List Token → Option Token) (scales : Cm.Scales) where
  /-- an index is a well-formed table of weights -/
  idx : I → Cm.Idx
  /-- an instance is a request of the model -/
  req : X → Instance ppref
  /-- what the builder builds is what "requestOfTokens" builds -/
  built : ∀ x' b x, build x' b = some x → requestOfTokens x' b = some (req x)
  /-- the model is the integer model at the table and the index's tensors -/
  next : ∀ i l, nextToken i l = IntegerModel.nextToken scales (idx i).index l

section Four
variable {I X Wn : Type} {build : List Token × List Token → List Token → Option X}
  {nextToken : I → List Token → Option Token} {Rn : I → X → Wn → Prop}

/-- **From the relaxed relation with the cost ledger at exact match.** -/
theorem sound_four_of_ledger {scales : Cm.Scales} (lawful : scales.Lawful)
    (R : ReadsModel build nextToken scales) (wit : Wn → Inst.Model.All.Trace)
    (hR : ∀ i x' b x w, build x' b = some x → Rn i x w →
      Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf scales AcceptancePolicy.exact) (R.idx i) (R.req x) (wit w)) :
    ∀ i (x' : List Token × List Token) b x, build x' b = some x → (∃ w, Rn i x w) →
      ∀ position (h : position < x'.2.length),
        nextToken i (x'.1 ++ x'.2.take position) = some x'.2[position] := by
  intro i x' b x hb hw position h
  obtain ⟨w, hw⟩ := hw
  rw [R.next]
  exact sound_ledger_exact lawful (R.idx i) x' b (R.req x) (R.built x' b x hb)
    ⟨wit w, hR i x' b x w hb hw⟩ position h

/-- **From the named hypotheses by group.** -/
theorem sound_four_of_meanHoles {scales : Cm.Scales} (lawful : scales.Lawful)
    (R : ReadsModel build nextToken scales) {Rno : Cm.Idx → Instance ppref → Wn → Prop}
    {mx : Cm.Idx → Instance ppref → Wn → ℕ → Mx}
    (hR : ∀ i x' b x w, build x' b = some x → Rn i x w → Rno (R.idx i) (R.req x) w)
    (H : MeanHoles scales AcceptancePolicy.exact Rno mx) :
    ∀ i (x' : List Token × List Token) b x, build x' b = some x → (∃ w, Rn i x w) →
      ∀ position (h : position < x'.2.length),
        nextToken i (x'.1 ++ x'.2.take position) = some x'.2[position] := by
  intro i x' b x hb hw position h
  obtain ⟨w, hw⟩ := hw
  rw [R.next]
  exact sound_of_holes_exact lawful H (R.idx i) x' b (R.req x) (R.built x' b x hb)
    ⟨w, hR i x' b x w hb hw⟩ position h

end Four

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.sound_four_of_ledger
#print axioms OnBytes.Road.L5.sound_four_of_meanHoles
