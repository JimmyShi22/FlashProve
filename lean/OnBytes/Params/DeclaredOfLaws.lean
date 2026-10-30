-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/DeclaredOfLaws.lean: laws of the value of the declared structure
(OnBytes/Params/DeclaredOf.lean).

 - `kindOf_eq`: the kind of a round's name in Decl/Declared.lean (`Fmt.kindOf`) is the kind by which
   the program's blocks close a round of that name (`kindOf`, OnBytes/Params/Names.lean). The two
   have one text; the proof is by unfolding.
 - `declaredKey_runs`: a value that `declaredKey` returns runs what it hashes. `declaredKey` makes
   the test before it returns, so this too is an unfolding.
 - `declared_files`, `declared_isDeclared`: a value that `declared` returns holds the three files'
   text, and is the declared structure of its own files.
All go from a returned value inward. What is not claimed: that `declared` returns a value at any
files; anything that leads out of `isDeclared D` (that D's files are three, and that `declared`
returns D at them); that the value of `declared`, with a proof file's chains, runs what it hashes
(`declaredKey_runs` speaks of the value without them); that its digest and its seven plans are the
program's, though `declared` compares them; anything on a proof file's chains.

-/
import OnBytes.Params.DeclaredOf
import OnBytes.Params.ConfigureLaws

namespace OnBytes.Params

/-- The two functions from a round's name to its kind are one. -/
theorem kindOf_eq : ∀ n : String, kindOf n = Fmt.kindOf n := fun _ => rfl

/-- What `declaredKey` returns holds the three files' text and runs what it hashes. -/
theorem declaredKey_runs {x : ConfigurationFiles} {p : Model.Verify.Planned} {D : Fmt.Declared}
    (h : declaredKey x p = .ok D) :
    D.files = [x.policy, x.layout, x.scales] ∧ runsWhatItHashes D = true := by
  unfold declaredKey at h
  obtain ⟨E, _, h⟩ := exc_bind h
  obtain ⟨K, _, h⟩ := exc_bind h
  dsimp only at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact ⟨rfl, hc.2⟩
  · cases h

/-- What `withProof` returns has D's files. -/
theorem withProof_files {x : ConfigurationFiles} {p : Model.Verify.Planned} {D D' : Fmt.Declared}
    (h : withProof x p D = .ok D') : D'.files = D.files := by
  unfold withProof at h
  obtain ⟨L, _, h⟩ := exc_bind h
  unfold withProofOf at h
  dsimp only at h
  split at h
  · cases h
    rfl
  · cases h

/-- What `declared` returns holds the three files' text. -/
theorem declared_files {x : ConfigurationFiles} {D : Fmt.Declared} (h : declared x = .ok D) :
    D.files = [x.policy, x.layout, x.scales] := by
  unfold declared at h
  obtain ⟨p, _, h⟩ := exc_bind h
  obtain ⟨D0, h0, h⟩ := exc_bind h
  rw [withProof_files h]
  exact (declaredKey_runs h0).1

/-- **What `declared` returns is the declared structure of its own files.** -/
theorem declared_isDeclared {x : ConfigurationFiles} {D : Fmt.Declared} (h : declared x = .ok D) :
    isDeclared D = true := by
  unfold isDeclared
  rw [declared_files h]
  show ((declared x).toOption == some D) = true
  rw [h]
  exact beq_self_eq_true (some D)

end OnBytes.Params
