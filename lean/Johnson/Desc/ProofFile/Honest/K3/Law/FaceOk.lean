-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/FaceOk.lean: the verifier's own tests on a lookup's numbers
(`Face.ok`, Johnson/Desc/First/Look/K3LookupGeneral.lean) hold of the face of a proof file's lookup.
Conditional on the library's test on the shape and on one key that is no padding. One definition,
one theorem, two tests by evaluation.

Terms. Honest/K3/GLOSSARY.md. In this file: the face of a proof file's lookup of shape h is
`faceOf h` (K3LookupGeneral.lean). The library's test on the shape is `FoNums.ok`
(OnBytes/Tie/Pv/Lookup/Port/FoNums.lean).

What is shown.
  `someKey`: a Boolean test on a shape h: at least one key of the face of h is no padding.
  `faceOf_ok`: if `FoNums.ok h` and `someKey h` accept, then `(faceOf h).ok = true`.

Hypotheses that remain.
  `hok`: the library's test accepts the shape h.
  `hk`: `someKey` accepts h. The library's test alone is not enough. `Face.ok` asks that the
    padding's places are fewer than the keys; `FoNums.ok` asks that they are at most as many. A
    shape all of whose keys are padding passes the second and fails the first (the two #guard lines
    at the end of the file show one, by evaluation). So the strict bound is a hypothesis here: it
    reads public numbers alone, and `someKey` is its test with code.

Users. `site_face_ok` (Honest/K3/Law/SomeKeyAt.lean [not in this library]).

Limits. That the strict bound holds at a site of a public part is not shown in this file. Since:
`someKey_of_pubOk` and `face_ok_site` (Johnson/AtFull/Shape/FaceAtSites.lean)
state the strict bound for every shape that passes two public tests, and `Face.ok` at every site of
every public part; by report alone they are compiled.
At a course that passes `Fit` (Honest/K3/Law/Statements.lean) the face's tests are a clause of
`Fit`.
An instance: Honest/K3/FastLaw/RealMember.lean [not in this library] evaluates `FoNums.ok` and
`Face.ok` true at one shape (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecValues
import OnBytes.Tie.Pv.Lookup.Forest.FoDescent
import OnBytes.Tie.Pv.Lookup.Forest.FoHole
import OnBytes.Tie.Pv.Lookup.Test.FoNumsTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open VerifiableInference.Desc.K3 (faceOf)

/-- A Boolean test: at least one key of the face of shape h is no padding. -/
def someKey (h : OnBytes.Model.Forest.Shape) : Bool :=
  decide (((faceOf h).padding.map (·.1)).sum < 2 ^ h.v)

/-- **Conditional on `FoNums.ok h` and on `someKey h`: the face of a proof file's lookup of shape h
passes the verifier's own tests.** An instance: Honest/K3/FastLaw/RealMember.lean
[not in this library] evaluates `FoNums.ok` and `Face.ok` true at one shape (by evaluation). -/
theorem faceOf_ok (h : OnBytes.Model.Forest.Shape) (hok : FoNums.ok h = true)
    (hk : someKey h = true) : (faceOf h).ok = true := by
  have hv := Cb.Fo.ok_v hok
  have h1 : 1 ≤ h.v := by omega
  have hp : ((faceOf h).padding.map (·.1)).sum < 2 ^ h.v := of_decide_eq_true hk
  have hr : VerifiableInference.Desc.First.Prod.runOk 0 h.v 0 ((faceOf h).orders 0) = true := by
    simp only [VerifiableInference.Desc.First.Prod.runOk, Bool.and_eq_true, beq_self_eq_true,
      List.all_eq_true, List.mem_range, true_and]
    intro i _
    have e := _root_.Fo.ordK_perm h (Cb.Fo.ok_parts hok).1.1 i
    rw [Nat.zero_add] at e ⊢
    exact orderOk_of_perm e
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show 1 ≤ 5
    omega
  · show 5 ≤ 6
    omega
  · show 2 ≤ 32
    omega
  · show 32 ≤ 2 ^ 5
    norm_num
  · rfl
  · intro v hm
    have e : v = h.v := by simpa [faceOf] using hm
    rw [e]
    exact h1
  · rfl
  · show _ < (([h.v].map (2 ^ ·)).sum)
    simpa using hp
  · intro x hx
    have e : x = (h.v, 0) := by simpa [faceOf] using hx
    rw [e]
    exact hr

#print axioms ProofFile.Honest.K3.Law.Spec.faceOf_ok

-- The second hypothesis is needed: the library's least test shape (one call, one tree of 2 ^ 10
-- keys), with all its keys declared padding, passes the library's test and fails the verifier's; as
-- it stands in the library it passes both, and the test on one key tells the two apart.
#guard FoNums.least.any fun h => FoNums.ok h && someKey h && (faceOf h).ok
#guard FoNums.least.any fun h =>
  FoNums.ok { h with pub := #[1024] } && !someKey { h with pub := #[1024] } &&
    !(faceOf { h with pub := #[1024] }).ok

end ProofFile.Honest.K3.Law.Spec
