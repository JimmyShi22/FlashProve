-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/FwdHead.lean: `Fwd` (Reads/FormsPass.lean) at the readers of a segment, at a run
of the output head's own claims.

Why. The readers of a segment (`readersOfLink`, Johnson/Desc/First/Batch/ReadersOfLink.lean) ask the
run itself first, and a second reader, the letter "silent", only where the run is silent. At the
output head that second reader is `k6Silent` (Johnson/Desc/Kinds/Law/K6SilentCode.lean): the run,
called at the state with the reads' tables laid silently. Right behind the output head's own
sub-protocol the run is silent, since the tables are laid one place later; behind that place the run
answers itself.

What is shown. Both at a name that is not the approximate range proof's "K8.equations", and where
the run that is found under the name is one of the kind's own (`runsBy`).
  `fwd_of_run`: **where the run itself answers in front: `Fwd`, under `KeptMore` from the state in
    front to the state behind.**
  `fwd_of_hole`: **where the run is silent in front and the second reader is `k6Silent`: `Fwd`,
    under `KeptMore` from the state with the tables laid silently to the state behind.** This is the
    arm across the place at which the tables are laid.

Limits. "The run itself answers in front" and "the run is silent in front" are premises. The case of
a run that is silent at both states is not reached. The run "join" is not reached. `KeptMore` is
shown here of no sub-protocol. Nothing on soundness.


-/
import Johnson.Desc.Reads.ReaderFwd
import Johnson.Desc.First.Batch.ReadersOfLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.Pass

open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (readerOf LinkHoles statesOfLink readersOfLink)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (withTables k6Silent)

/-- The readers' answer where the run itself answers. -/
theorem readers_of_run (H : LinkHoles) (l : Link S Claim) (b : ℕ) {name : String}
    (hne : (name == "K8.equations") = false) {s : S} {R : VerifiableInference.Desc.K9.Read}
    (h : readerOf (statesOfLink l) b name s = some R) :
    (readersOfLink H l).forms b name s = some R := by
  show (if (name == "K8.equations") = true then H.small s
    else
      match readerOf (statesOfLink l) b name s with
      | some R => some R
      | Option.none => H.silent b name s) = some R
  rw [hne, h]
  rfl

/-- **Where the run itself answers in front.** -/
theorem fwd_of_run {names : List String}
    {runs : Given → Behind → Places → List (String × List Form)}
    {keys : Given → Behind → Places → List Form} {toCl : Form → Claim} {p : Par}
    {h : OnBytes.Model.Head.Shape} {iU3 : ℕ} {s s' : S} (H : LinkHoles) (l : Link S Claim)
    (b : ℕ) {name : String} (hne : (name == "K8.equations") = false)
    (hst : ∀ r, ((statesOfLink l b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy names runs keys toCl p (seatAt h iU3))
    (k : KeptMore iU3 s s') (hans : (readerOf (statesOfLink l) b name s).isSome = true) :
    Fwd (readersOfLink H l) b name s s' := by
  intro R hR
  obtain ⟨R₁, h1⟩ := Option.isSome_iff_exists.1 hans
  have e : R₁ = R := Option.some.inj ((readers_of_run H l b hne h1).symm.trans hR)
  subst e
  exact readers_of_run H l b hne (reader_fwd k (statesOfLink l) b name hst h1)

/-- **Where the run is silent in front and the second reader answers.** -/
theorem fwd_of_hole {names : List String}
    {runs : Given → Behind → Places → List (String × List Form)}
    {keys : Given → Behind → Places → List Form} {toCl : Form → Claim} {p : Par}
    {h : OnBytes.Model.Head.Shape} {iU3 : ℕ} {s s' : S} (H : LinkHoles) (l : Link S Claim)
    (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) (b : ℕ) {name : String}
    (hne : (name == "K8.equations") = false)
    (hst : ∀ r, ((statesOfLink l b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy names runs keys toCl p (seatAt h iU3))
    (hsil : H.silent = k6Silent P (statesOfLink l))
    (hno : readerOf (statesOfLink l) b name s = none)
    (k : ∀ e, withTables P s = some e → KeptMore iU3 e s') :
    Fwd (readersOfLink H l) b name s s' := by
  intro R hR
  have hR' : (if (name == "K8.equations") = true then H.small s
    else
      match readerOf (statesOfLink l) b name s with
      | some R => some R
      | Option.none => H.silent b name s) = some R := hR
  rw [hne, hno, hsil] at hR'
  have hR'' : (withTables P s).bind (readerOf (statesOfLink l) b name) = some R := hR'
  obtain ⟨e, he, h1⟩ := Option.bind_eq_some_iff.1 hR''
  exact readers_of_run H l b hne (reader_fwd (k e he) (statesOfLink l) b name hst h1)

end VerifiableInference.Reads.Pass

#print axioms VerifiableInference.Reads.Pass.readers_of_run
#print axioms VerifiableInference.Reads.Pass.fwd_of_run
#print axioms VerifiableInference.Reads.Pass.fwd_of_hole
